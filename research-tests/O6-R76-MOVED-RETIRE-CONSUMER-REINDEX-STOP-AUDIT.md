# O6 revision 76: moved-retire consumer reindex stop

## Scope

Grind shift #84 (overall #138) resumed from accepted revision-75 boundary
`076030d`. It attacked only the authorized producer-owned package and its exact
consumer under the permanent fresh-check-every-commit protocol.

## Retained package

Commit `1fe4fa8` constructs the private `MovedRightRetirePackage`. The producer
`produceMovedRightRetirePackage` seals, under one dependent result:

- the moved-right action;
- its rule tag;
- its exact checked-action equation at `pairFirst`;
- its equality to `transitionAction right`;
- its reindexed equality to `ORetire child`.

The producer derives all projections from one `LocalAlignedHeadView` of
`movedPairAligned diamond`. Every field and local is quantity 0. Its direct CP5
source check visibly rebuilt the module after TTC/TTM removal, and R16 passed as
additional evidence. No public or frozen declaration changed.

## Exhausted consumer unit

The consumer `movedRetireBeforeInsertedChildImpossible` was attempted three
times, without retaining any failed body:

1. The moved checked equation was successfully reindexed through
   `movedRetireEqualsRequested` before `checkedActionProjects`. The first error
   was only parser precedence on two local equality types.
2. After parenthesizing those types, the moved-right reindex was accepted. The
   remaining failure was a dependent tag projection: eliminating
   `MkForeignInsertPlanView` tried to unify concrete `OInsertTag` with
   `alignedHeadTag sourceHead`.
3. Two tag-independent projection helpers were introduced so the consumer would
   request only source absence and moved-retire presence. Fresh elaboration then
   rejected the new insertion helper's dependent `value` inference and reported
   `foreignInsertPlanView` inaccessible in that malformed context; consequently
   its call from the consumer also lacked a resolved `DecEq name`.

The third attempt therefore stopped at a new **consumer projection statement
shape** inside the same correlated-projection/reindex class. It did not expose a
new semantic premise gap. The entire consumer and both failed projection helpers
were removed. The producer package remains because it independently passed a
visible fresh source check.

## Recommended next cure

Do not reopen the moved package. Add one tiny tag-independent source-insert
absence helper with all `lookupFiber` type parameters explicit (`name`, `key`,
`value`, `world`, `error`) and a locally explicit action type. Check that helper
alone before writing the retirement-presence counterpart. Each helper receives
its own fresh three-attempt budget. Then the consumer should:

1. build `LocalAlignedHeadView` for source-left;
2. reindex its checked action to the concrete insertion;
3. eliminate `MovedRightRetirePackage` once and reindex to concrete retirement;
4. call only the two tag-independent lookup projections;
5. contradict `Nothing = Just oldFiber`.

## Status

- producer-owned moved-retire package: **closed and retained**;
- moved-retire/insert impossibility consumer: **not closed**;
- field 2 whole adjacent discipline: **not closed**;
- fields 3–15: **unopened**;
- final assembly/body: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

The accepted **2–14 shift** remainder is held. Although the package is now
closed, the consumer statement-shape stop prevents honestly reducing the lower
or upper bound.

## Frozen-capital audit

The #83 twenty-unit chain, revision-21 surfaces, parent-yield package, joint
generator, RAR chain, maps, occurrences, and alignments are unchanged.
`adjacentSwapSuffixSpike` remains 1183 bytes with SHA-256
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`.
Production `src/`, `dgamma.ipkg`, and CP3 blob
`2c697e532e83989de8591fa6a4378747c6a501c0` remain isolated. No hole or escape
hatch was added.
