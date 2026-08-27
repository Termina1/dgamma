# O6 revision 45: yielded L-Advance endpoints closed; generator RAR STOP-AUDIT

## Scope

Shift #53 began at accepted revision-44 HEAD `b487e15` and changed only the
private research pointwise head-replayer. No frozen signature, public caller
boundary, production file, or `ReplayInvariantBundle` field changed.

## Ratified R44 endpoint representation succeeds

The locally abstract `value`/`sourceNext` wall did **not** recur through concrete
endpoints. Each successful runtime branch now has its own top-level producer
that fixes fully typed source and replayed `SystemState name key value world
error` endpoints before invoking the common operational packager:

- `replayPointwiseAdvanceYieldedDivertOperational` constructs yielded landing
  `LDivertTag` with `Unloading` lifecycle;
- `replayPointwiseAdvanceYieldedFinishOperational` constructs yielded
  `LFinishTag` with `Active` lifecycle for a singleton remaining program;
- `replayPointwiseAdvanceYieldedIterOperational` constructs `LIterTag` with a
  nonempty `Reloading` continuation.

All three branches retain exact source and target resolver/run equations,
transport the yielded inverse-map relation through
`yieldedMapsGiveLocalUndoRuntimeRelated`, build related pushed accumulators with
`pushLocalUndoRuntimeRelated`, own exact raw target evaluators and pointwise
post-replacement controls, and finish through
`packagePointwiseAdvanceOperationalReplay`.

No dedicated `replaceBinding` lemma is indicated: the concrete endpoint design
eliminated the revision-44 obstruction on the first compile attempt for every
branch.

## Singleton stage capital retained

`singletonAdvanceStageOrigin` reindexes a target singleton L-Advance iterator
stage to the exact source occurrence while opening only constructor-owned
occurrence, lookup, and lifecycle evidence.

A direct separate exact-outcome theorem encountered the expected accumulator
normalization residue: iterator outcomes ignore accumulators, but reducing a
separately computed origin retained a stuck lifecycle match. The third
representation packages origin and exact outcome together:

- `LocatedSingletonAdvanceStageReplay`;
- `locateSingletonAdvanceStageReplay`.

This dependent package compiled and was retained. It never identifies source
and replay accumulator functions or independently stored `DecEq` dictionaries.
`replayIteratorYieldedProjectionExact` was also retained, completing the
proof-free link from a stage outcome to its yielded generator map.

## Bounded singleton generator RAR stop

The next resisting lemma was the per-generator package needed to assemble
`RelationalReplayCorrespondence`. It received three attempts.

1. Separate generator-origin and map functions reached the actual-forward case
   but the origin function left an unreduced singleton action match:

   ```text
   Can't solve constraint between:
     partialEffectMapFor ... sourceBefore x
   and:
     traceGeneratorRuntimeMap
       (traceEffectGeneratorRuntime
         (let LAdvance actor = LAdvance actor in ActualForwardGenerator ...)) x.
   ```

2. An explicit `originShape` equality for that actual generator still failed to
   normalize the separately computed origin:

   ```text
   Can't solve constraint between:
     ActualForwardGenerator ... OccursHere actorMatches
   and:
     singletonAdvanceGeneratorOriginFrom ... generator.
   ```

3. The representation was changed to the same successful pattern as the stage:
   one dependent `LocatedSingletonAdvanceGeneratorReplay` carrying the source
   generator and its universally quantified relational map proof together. The
   first compile reached only a lambda-binder parser diagnostic:

   ```text
   Error: Expected '=>'.
   ... (\observedKeyEq, {x}, {y}, inputs => ...)
   ```

   The obvious binder correction was made locally but not compiled because the
   third attempt had already been consumed. The entire uncommitted generator
   family/package was reverted. No partial RAR producer or metavariable remains.

## Next representation

Under a fresh budget, reintroduce only the dependent per-generator package and
use a two-argument lambda for the actual map field (`\observedKeyEq, inputs =>
...`), allowing implicit inputs to be inferred. Then define the singleton RAR
by projecting both origin and map proof from the *same* located generator
package. This avoids separate-origin normalization exactly as the retained
stage package does.

After that:

1. connect the retained empty, failure, and yielded operational producers to
   `runtimeAdvanceOutcomeRelated` in the sealed L-Advance eliminator;
2. assemble `replayPointwiseAdvanceHead`, occurrence, relative ordinal, and
   alignment, reaching 8/8;
3. only then open whole-suffix RAR/ordinal composition.

## Status

- yielded divert/finish/iter concrete operational producers: **closed**;
- all executable L-Advance runtime branch producers: **closed individually**;
- runtime-outcome dispatcher and complete L-Advance head: **open**;
- singleton stage origin/outcome capital: **closed and retained**;
- singleton generator/RAR capital: **STOP-AUDIT; no partial package retained**;
- semantic families: **7/8** until the complete head is packaged;
- whole-suffix composition: **unopened and still gated**;
- adjacent result: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- O6 estimate: **9–21 shifts**, narrowed from **11–23** by all three concrete
  yielded branch closures and retained stage capital, with the generator package
  retry still charged.
