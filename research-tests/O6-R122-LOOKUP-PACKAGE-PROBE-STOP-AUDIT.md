# O6 revision 122: lookup-package disposable probe STOP-AUDIT

## Scope

Shift #120 (overall #174) began from accepted clean HEAD `74d917b` and followed
the mandatory probe-first ruling. The only opened artifact was disposable
`research-tests/DGamma/R47RootLookupPackageProbePositive.idr`. It declared:

- a producer-owned package indexed by source and target states, actor, and
  source fiber;
- explicit quantity-0 source and target `lookupFiber = Just fiber` fields;
- an explicit `FiberControlRelated` field;
- explicit quantity-0 source and target `fiberParent = Root` fields;
- a single-elimination root-transition consumer covering O-Retire and
  O-Remove, plus the direct O-Insert branch.

The probe was never added to the tracked suite and has been removed in full.
No retained proof implementation, package, body helper, bundle field, frozen
surface, or hole was changed.

## Mandatory probe result

The first fresh probe invocation rebuilt
`DGamma.CP5ConfluenceLocalDiamondSpike`, then rejected the disposable consumer
module for two module-boundary reasons:

```text
Undefined name DecEq.
```

and

```text
Name DGamma.CP5ConfluenceLocalDiamondSpike.pointwiseControlLookupFound is private.
```

The `Building DGamma.R47RootLookupPackageProbePositive` line preceded these
errors and is not a success marker. Neither
`R122_ROOT_LOOKUP_PACKAGE_PROBE=passed` nor
`R122_ROOT_LOOKUP_ONE_ELIM_CONSUMER=passed` was emitted.

The ruling said that any probe failure is a semantic stop requiring a mandatory
design-only campaign. Consequently no import correction, copied private helper,
second probe, retained package, external-order retry, occurrence fold, result,
or hole body was attempted.

## Required design-only campaign

A future disposable campaign must decide the legal module boundary before
testing the dependent representation:

1. either insert the package and producer into a disposable copy of the CP5
   module, where `pointwiseControlLookupFound` is in scope;
2. or give the external probe the exact foundational imports and a private,
   independently checked lookup producer rather than depending on CP5-private
   capital.

Only after that campaign checks both package construction and a one-elimination
`RootOrchestrationStep` consumer may a retained unit receive a fresh budget.
The required semantic shape remains unchanged: the target lookup equation must
be owned at production together with both fibers, their control relation, and
both Root-parent equations.

## Status

- lookup-package probe: **failed and removed**;
- retained lookup package: **unopened**;
- body external-order retry: **unopened**;
- occurrence fold/result/body: **unopened**;
- all 15 replay-bundle fields: **complete and frozen**;
- holes: **20**, split **6/4/8/1/1**.

```text
NO_FROZEN_SURFACE_CHANGE_REQUIRED
R122_LOOKUP_PACKAGE_PROBE=failed
R122_DISPOSABLE_PROBE_REMOVED=passed
```
