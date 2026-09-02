# O6 revision 121: body external-order lookup STOP-AUDIT

## Scope

Shift #119 opened only the authorized O6 body unit from clean HEAD `49c1e35`.
The first body obligation was the whole `SameExternalOrchestration`: prefix
reflexivity, the supplied pair relation, and suffix replay external-order
preservation. No occurrence fold, `AdjacentSwapResult`, hole body, closed bundle
field, frozen declaration, or other hole was changed.

## Three-attempt record

1. The initial extraction of the private root-orchestration decision helpers
   failed before insertion, while the suffix transport helpers were inserted.
   Fresh compilation therefore rejected the unbound root decision and an
   implicit root actor. This compile consumed attempt 1.
2. The decision family and explicit root actor were added. Compilation reached
   `bodyRootOrchestrationForward`, where direct elimination of
   `controlPointwise` did not reify the target lookup as `Just targetFiber` for
   `RootRetireStep`/`RootRemoveStep`.
3. The decision family was ordered before consumers and the source lookup was
   explicitly reindexed by the source `found` equation. Compilation still
   stopped at the target side:

```text
Can't solve constraint between:
  Just (MkFiber ... rightParent ... rightLifecycle)
and:
  lookupBinding ... (registry targetBefore)
```

The unit exhausted its fresh three-attempt budget. All body proof edits were
removed. No fourth attempt was made.

## Required design boundary

`ControlEquivalent.controlPointwise` proves a dependent
`FiberControlMaybeRelated` between opaque lookups. Patterning
`SomeControlFibers` exposes the related target fiber but does not preserve the
exact target `lookupFiber = Just targetFiber` equation needed by
`RootRetireStep` and `RootRemoveStep`.

A future design-only campaign must check a producer-owned package that consumes
one pointwise relation and returns, under one constructor elimination:

- the exact source fiber and source lookup equation;
- the exact target fiber and target lookup equation;
- their `FiberControlRelated` witness;
- the exact parent equality.

The body may then transport root-orchestration classification and recursively
construct suffix `SameExternalOrchestration`. This is body-local capital; no
`ReplayInvariantBundle`, `LocalRelationalDiamond`, sealed-spine, revision-19–21,
or public surface change is authorized.

## Status

- distinct-owner pair RAR: **complete and frozen**;
- field 9: **complete and frozen**;
- fields 10–15: **complete and frozen**;
- all 15 replay-bundle fields: **complete**;
- O6 body: **not retained; stopped at target lookup packaging**;
- occurrence fold/result: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

```text
NO_FROZEN_SURFACE_CHANGE_REQUIRED
BODY_EXTERNAL_ORDER=failed_after_3
```
