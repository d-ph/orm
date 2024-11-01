<?php

declare(strict_types=1);

namespace Doctrine\ORM\Tools\Pagination;

use ArrayIterator;
use Countable;
use Doctrine\Common\Collections\Collection;
use Doctrine\ORM\EntityManagerInterface;
use Doctrine\ORM\Internal\SQLResultCasing;
use Doctrine\ORM\Mapping\ClassMetadata;
use Doctrine\ORM\NoResultException;
use Doctrine\ORM\Query;
use Doctrine\ORM\Query\AST\Join;
use Doctrine\ORM\Query\AST\JoinAssociationDeclaration;
use Doctrine\ORM\Query\AST\Node;
use Doctrine\ORM\Query\AST\SelectExpression;
use Doctrine\ORM\Query\Parameter;
use Doctrine\ORM\Query\Parser;
use Doctrine\ORM\Query\ResultSetMapping;
use Doctrine\ORM\QueryBuilder;
use Doctrine\Persistence\Mapping\MappingException;
use IteratorAggregate;
use Traversable;

use function array_key_exists;
use function array_map;
use function array_sum;
use function assert;
use function count;
use function in_array;
use function is_string;
use function reset;
use function str_starts_with;

/**
 * The paginator can handle various complex scenarios with DQL.
 *
 * @template-covariant T
 * @implements IteratorAggregate<array-key, T>
 */
class Paginator implements Countable, IteratorAggregate
{
    use SQLResultCasing;

    public const HINT_ENABLE_DISTINCT = 'paginator.distinct.enable';

    private readonly Query $query;
    private bool|null $useResultQueryOutputWalker = null;
    private bool|null $useCountQueryOutputWalker  = null;
    private int|null $count                       = null;
    /**
     * The auto-detection of queries style was added a lot later to this class, and this
     *  class historically was by default using the more complex queries style, which means that
     *  the simple queries style is potentially very under-tested in production systems. The purpose
     *  of this variable is to not introduce breaking changes until an impression is developed that
     *  the simple queries style has been battle-tested enough.
     */
    private bool $queryStyleAutoDetectionEnabled = false;
    private bool $queryCouldHaveToManyJoins      = true;

    /**
     * @param bool $queryCouldProduceDuplicates Whether the query could produce partially duplicated records. One case
     *  when it does is when it joins a collection.
     */
    public function __construct(
        Query|QueryBuilder $query,
        private readonly bool $queryCouldProduceDuplicates = true,
    ) {
        if ($query instanceof QueryBuilder) {
            $query = $query->getQuery();
        }

        $this->query = $query;
    }

    /**
     * Create an instance of Paginator with auto-detection of whether the provided
     * query is suitable for simple (and fast) pagination queries, or whether a complex
     * set of pagination queries has to be used.
     */
    public static function newWithAutoDetection(Query|QueryBuilder $query): self
    {
        if ($query instanceof QueryBuilder) {
            $query = $query->getQuery();
        }

        $queryAST = $query->getAST();
        [
            'hasGroupByClause' => $queryHasGroupByClause,
            'hasHavingClause' => $queryHasHavingClause,
            'rootEntityHasSingleIdentifierFieldName' => $rootEntityHasSingleIdentifierFieldName,
            'couldProduceDuplicates' => $queryCouldProduceDuplicates,
            'couldHaveToManyJoins' => $queryCouldHaveToManyJoins,
        ]         = self::autoDetectQueryFeatures($query->getEntityManager(), $queryAST);

        $paginator = new self($query, $queryCouldProduceDuplicates);

        $paginator->queryStyleAutoDetectionEnabled = true;
        $paginator->queryCouldHaveToManyJoins      = $queryCouldHaveToManyJoins;
        // The following is ensuring the conditions for when the CountWalker cannot be used.
        $paginator->useCountQueryOutputWalker = $queryHasHavingClause !== false
            || $rootEntityHasSingleIdentifierFieldName !== true
            || ($queryCouldHaveToManyJoins && $queryHasGroupByClause !== false);

        return $paginator;
    }

    /**
     * @return array{
     *  hasGroupByClause: bool|null,
     *  hasHavingClause: bool|null,
     *  rootEntityHasSingleIdentifierFieldName: bool|null,
     *  couldProduceDuplicates: bool,
     *  couldHaveToManyJoins: bool,
     * }
     */
    private static function autoDetectQueryFeatures(EntityManagerInterface $entityManager, Node $queryAST): array
    {
        $queryFeatures = [
            // Null means undetermined
            'hasGroupByClause' => null,
            'hasHavingClause' => null,
            'rootEntityHasSingleIdentifierFieldName' => null,
            'couldProduceDuplicates' => true,
            'couldHaveToManyJoins' => true,
        ];

        if (! $queryAST instanceof Query\AST\SelectStatement) {
            return $queryFeatures;
        }

        $queryFeatures['hasGroupByClause'] = $queryAST->groupByClause !== null;
        $queryFeatures['hasHavingClause']  = $queryAST->havingClause !== null;

        $from = $queryAST->fromClause->identificationVariableDeclarations;
        if (count($from) > 1) {
            return $queryFeatures;
        }

        $fromRoot = reset($from);
        if (! $fromRoot instanceof Query\AST\IdentificationVariableDeclaration) {
            return $queryFeatures;
        }

        if (! $fromRoot->rangeVariableDeclaration) {
            return $queryFeatures;
        }

        $rootAlias = $fromRoot->rangeVariableDeclaration->aliasIdentificationVariable;
        try {
            $rootClassMetadata                                       = $entityManager->getClassMetadata($fromRoot->rangeVariableDeclaration->abstractSchemaName);
            $queryFeatures['rootEntityHasSingleIdentifierFieldName'] = (bool) $rootClassMetadata->getSingleIdentifierFieldName();
        } catch (MappingException) {
            return $queryFeatures;
        }

        $rootClassName = $fromRoot->rangeVariableDeclaration->abstractSchemaName;

        $aliasesToClassNameOrClassMetadataMap             = [];
        $aliasesToClassNameOrClassMetadataMap[$rootAlias] = $rootClassMetadata;
        $toManyJoinsAliases                               = [];

        // Check the Joins list.
        foreach ($fromRoot->joins as $join) {
            if (! $join instanceof Join || ! $join->joinAssociationDeclaration instanceof JoinAssociationDeclaration) {
                return $queryFeatures;
            }

            $joinParentAlias     = $join->joinAssociationDeclaration->joinAssociationPathExpression->identificationVariable;
            $joinParentFieldName = $join->joinAssociationDeclaration->joinAssociationPathExpression->associationField;
            $joinAlias           = $join->joinAssociationDeclaration->aliasIdentificationVariable;

            // Every Join descending from a ToMany Join is "in principle" also a ToMany Join
            if (in_array($joinParentAlias, $toManyJoinsAliases, true)) {
                $toManyJoinsAliases[] = $joinAlias;

                continue;
            }

            $parentClassMetadata = $aliasesToClassNameOrClassMetadataMap[$joinParentAlias] ?? null;
            if (! $parentClassMetadata) {
                return $queryFeatures;
            }

            // Load entity class metadata.
            if (is_string($parentClassMetadata)) {
                try {
                    $parentClassMetadata                                    = $entityManager->getClassMetadata($parentClassMetadata);
                    $aliasesToClassNameOrClassMetadataMap[$joinParentAlias] = $parentClassMetadata;
                } catch (MappingException) {
                    return $queryFeatures;
                }
            }

            $parentJoinAssociationMapping = $parentClassMetadata->associationMappings[$joinParentFieldName] ?? null;
            if (! $parentJoinAssociationMapping) {
                return $queryFeatures;
            }

            $aliasesToClassNameOrClassMetadataMap[$joinAlias] = $parentJoinAssociationMapping['targetEntity'];

            if (! ($parentJoinAssociationMapping['type'] & ClassMetadata::TO_MANY)) {
                continue;
            }

            // The Join is a ToMany Join.
            $toManyJoinsAliases[] = $joinAlias;
        }

        $queryFeatures['couldHaveToManyJoins'] = count($toManyJoinsAliases) > 0;

        // Check the Select list.
        foreach ($queryAST->selectClause->selectExpressions as $selectExpression) {
            if (! $selectExpression instanceof SelectExpression) {
                return $queryFeatures;
            }

            // Must not use any of the ToMany aliases
            if (is_string($selectExpression->expression)) {
                foreach ($toManyJoinsAliases as $toManyJoinAlias) {
                    if (
                        $selectExpression->expression === $toManyJoinAlias
                        || str_starts_with($selectExpression->expression, $toManyJoinAlias . '.')
                    ) {
                        return $queryFeatures;
                    }
                }
            }

            // If it's a function, then it has to be one from the following list. Reason: in some databases,
            // there are functions that "generate rows".
            if (
                $selectExpression->expression instanceof Query\AST\Functions\FunctionNode
                && ! in_array($selectExpression->expression::class, [
                    Query\AST\Functions\CountFunction::class,
                    Query\AST\Functions\AvgFunction::class,
                    Query\AST\Functions\SumFunction::class,
                    Query\AST\Functions\MinFunction::class,
                    Query\AST\Functions\MaxFunction::class,
                ], true)
            ) {
                return $queryFeatures;
            }
        }

        // If there are ToMany Joins, then the Select clause has to use the DISTINCT keyword. Note: the foreach
        // above also ensures that the ToMany Joins are not in the Select list, which is relevant.
        if (
            count($toManyJoinsAliases) > 0
            && ! $queryAST->selectClause->isDistinct
        ) {
            return $queryFeatures;
        }

        $queryFeatures['couldProduceDuplicates'] = false;

        return $queryFeatures;
    }

    /**
     * Returns the query.
     */
    public function getQuery(): Query
    {
        return $this->query;
    }

    /**
     * @deprecated Use ::getQueryCouldProduceDuplicates() instead.
     *
     * Returns whether the query joins a collection.
     */
    public function getFetchJoinCollection(): bool
    {
        return $this->queryCouldProduceDuplicates;
    }

    /**
     * Returns whether the query could produce partially duplicated records.
     */
    public function getQueryCouldProduceDuplicates(): bool
    {
        return $this->queryCouldProduceDuplicates;
    }

    /**
     * @deprecated Use the individual ::get*OutputWalker()
     *
     * Returns whether the paginator will use an output walker.
     */
    public function getUseOutputWalkers(): bool|null
    {
        return $this->getUseResultQueryOutputWalker() && $this->getUseCountQueryOutputWalker();
    }

    /**
     * @deprecated Use the individual ::set*OutputWalker()
     *
     * Sets whether the paginator will use an output walker.
     *
     * @return $this
     */
    public function setUseOutputWalkers(bool|null $useOutputWalkers): static
    {
        $this->setUseResultQueryOutputWalker($useOutputWalkers);
        $this->setUseCountQueryOutputWalker($useOutputWalkers);

        return $this;
    }

    /**
     * Returns whether the paginator will use an output walker for the result query.
     */
    public function getUseResultQueryOutputWalker(): bool|null
    {
        return $this->useResultQueryOutputWalker;
    }

    /**
     * Sets whether the paginator will use an output walker for the result query.
     */
    public function setUseResultQueryOutputWalker(bool|null $useResultQueryOutputWalker): static
    {
        $this->useResultQueryOutputWalker = $useResultQueryOutputWalker;

        return $this;
    }

    /**
     * Returns whether the paginator will use an output walker for the count query.
     */
    public function getUseCountQueryOutputWalker(): bool|null
    {
        return $this->useCountQueryOutputWalker;
    }

    /**
     * Sets whether the paginator will use an output walker for the count query.
     */
    public function setUseCountQueryOutputWalker(bool|null $useCountQueryOutputWalker): static
    {
        $this->useCountQueryOutputWalker = $useCountQueryOutputWalker;

        return $this;
    }

    public function count(): int
    {
        if ($this->count === null) {
            try {
                $this->count = (int) array_sum(array_map('current', $this->getCountQuery()->getScalarResult()));
            } catch (NoResultException) {
                $this->count = 0;
            }
        }

        return $this->count;
    }

    /**
     * {@inheritDoc}
     *
     * @psalm-return Traversable<array-key, T>
     */
    public function getIterator(): Traversable
    {
        $offset = $this->query->getFirstResult();
        $length = $this->query->getMaxResults();

        if ($this->queryCouldProduceDuplicates && $length !== null) {
            $subQuery = $this->cloneQuery($this->query);

            if ($this->useOutputWalker($subQuery)) {
                $subQuery->setHint(Query::HINT_CUSTOM_OUTPUT_WALKER, LimitSubqueryOutputWalker::class);
            } else {
                $this->appendTreeWalker($subQuery, LimitSubqueryWalker::class);
                $this->unbindUnusedQueryParams($subQuery);
            }

            $subQuery->setFirstResult($offset)->setMaxResults($length);

            $foundIdRows = $subQuery->getScalarResult();

            // don't do this for an empty id array
            if ($foundIdRows === []) {
                return new ArrayIterator([]);
            }

            $whereInQuery = $this->cloneQuery($this->query);
            $ids          = array_map('current', $foundIdRows);

            $this->appendTreeWalker($whereInQuery, WhereInWalker::class);
            $whereInQuery->setHint(WhereInWalker::HINT_PAGINATOR_HAS_IDS, true);
            $whereInQuery->setFirstResult(0)->setMaxResults(null);
            $whereInQuery->setCacheable($this->query->isCacheable());

            $databaseIds = $this->convertWhereInIdentifiersToDatabaseValues($ids);
            $whereInQuery->setParameter(WhereInWalker::PAGINATOR_ID_ALIAS, $databaseIds);

            $result = $whereInQuery->getResult($this->query->getHydrationMode());
        } else {
            $result = $this->cloneQuery($this->query)
                ->setMaxResults($length)
                ->setFirstResult($offset)
                ->setCacheable($this->query->isCacheable())
                ->getResult($this->query->getHydrationMode());
        }

        return new ArrayIterator($result);
    }

    private function cloneQuery(Query $query): Query
    {
        $cloneQuery = clone $query;

        $cloneQuery->setParameters(clone $query->getParameters());
        $cloneQuery->setCacheable(false);

        foreach ($query->getHints() as $name => $value) {
            $cloneQuery->setHint($name, $value);
        }

        return $cloneQuery;
    }

    /**
     * Determines whether to use an output walker for the query.
     */
    private function useOutputWalker(Query $query, bool $forCountQuery = false): bool
    {
        if (! $forCountQuery && $this->useResultQueryOutputWalker !== null) {
            return $this->useResultQueryOutputWalker;
        }

        if ($forCountQuery && $this->useCountQueryOutputWalker !== null) {
            return $this->useCountQueryOutputWalker;
        }

        // When a custom output walker already present, then do not use the Paginator's.
        return $query->getHint(Query::HINT_CUSTOM_OUTPUT_WALKER) === false;
    }

    /**
     * Appends a custom tree walker to the tree walkers hint.
     *
     * @psalm-param class-string $walkerClass
     */
    private function appendTreeWalker(Query $query, string $walkerClass): void
    {
        $hints = $query->getHint(Query::HINT_CUSTOM_TREE_WALKERS);

        if ($hints === false) {
            $hints = [];
        }

        $hints[] = $walkerClass;
        $query->setHint(Query::HINT_CUSTOM_TREE_WALKERS, $hints);
    }

    /**
     * Returns Query prepared to count.
     */
    private function getCountQuery(): Query
    {
        $countQuery = $this->cloneQuery($this->query);

        if (! $countQuery->hasHint(CountWalker::HINT_DISTINCT)) {
            $hintDistinctDefaultTrue = true;

            // When not joining onto *ToMany relations, then use a simpler COUNT query in the CountWalker.
            if (
                $this->queryStyleAutoDetectionEnabled
                && ! $this->queryCouldHaveToManyJoins
            ) {
                $hintDistinctDefaultTrue = false;
            }

            $countQuery->setHint(CountWalker::HINT_DISTINCT, $hintDistinctDefaultTrue);
        }

        if ($this->useOutputWalker($countQuery, forCountQuery: true)) {
            $platform = $countQuery->getEntityManager()->getConnection()->getDatabasePlatform(); // law of demeter win

            $rsm = new ResultSetMapping();
            $rsm->addScalarResult($this->getSQLResultCasing($platform, 'dctrn_count'), 'count');

            $countQuery->setHint(Query::HINT_CUSTOM_OUTPUT_WALKER, CountOutputWalker::class);
            $countQuery->setResultSetMapping($rsm);
        } else {
            $this->appendTreeWalker($countQuery, CountWalker::class);
            $this->unbindUnusedQueryParams($countQuery);
        }

        $countQuery->setFirstResult(0)->setMaxResults(null);

        return $countQuery;
    }

    private function unbindUnusedQueryParams(Query $query): void
    {
        $parser            = new Parser($query);
        $parameterMappings = $parser->parse()->getParameterMappings();
        /** @var Collection|Parameter[] $parameters */
        $parameters = $query->getParameters();

        foreach ($parameters as $key => $parameter) {
            $parameterName = $parameter->getName();

            if (! (isset($parameterMappings[$parameterName]) || array_key_exists($parameterName, $parameterMappings))) {
                unset($parameters[$key]);
            }
        }

        $query->setParameters($parameters);
    }

    /**
     * @param mixed[] $identifiers
     *
     * @return mixed[]
     */
    private function convertWhereInIdentifiersToDatabaseValues(array $identifiers): array
    {
        $query = $this->cloneQuery($this->query);
        $query->setHint(Query::HINT_CUSTOM_OUTPUT_WALKER, RootTypeWalker::class);

        $connection = $this->query->getEntityManager()->getConnection();
        $type       = $query->getSQL();
        assert(is_string($type));

        return array_map(static fn ($id): mixed => $connection->convertToDatabaseValue($id, $type), $identifiers);
    }
}
