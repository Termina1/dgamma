# O6 revision 41: L-Unload pointwise-reliance STOP-AUDIT

## Scope

This shift began from accepted revision-20 landing HEAD `57efb93`.  The exact
proof-bearing effect-map obstruction recorded by R38 is cleared: the intended
L-Unload source/target maps are now related by
`PartialMapsRelated (EffectStateEquivalence keyEq)`, supplied from
`AccumulatorRelated` exactly as the R39 probes established.

No frozen declaration, theorem hole, production file, or output-shaped premise
was changed.

## First remaining semantic boundary

A checked source `LUnload actor` contains the executable guard

```text
relied actor sourceRegistry = False
```

The target registry may have an independent binding order.  The recursive O6
endpoint therefore supplies `ControlEquivalent`, not
`OrderedRegistryControlsRelated`.  The production CP4 L-Unload replayer cannot
be reused: its reliance transport is list-order structural.

Mathematically, pointwise controls contain the needed observation.  A true
target reliance identifies a consumer by name; the matching source consumer has
the same lifecycle shape and committed provider view.  The direct Idris
representation nevertheless does not reduce constructively: `reliedHead`
projects `fiberLifecycle` from two dependent `Fiber` values, while
`FiberControlRelated` deliberately permits distinct proof-bearing owned tables
and accumulator functions.

## Bounded attempts and exact diagnostic

Two representations were attempted and fully reverted:

1. direct `reliedHead` equality by destructing `FiberControlRelated` and its
   `LifecycleControlRelated` field;
2. an order-independent target witness fold followed by lookup-by-name and an
   explicit lifecycle-observation bridge.

The second representation reaches the correct target consumer and source
lookup, but the final direct projection still retains the unrelated dependent
fiber witnesses.  The stable diagnostic is:

```text
Mismatch between: rightTable and leftTable.
```

`R41PointwiseRelianceProjectionNegative.idr` pins that exact rejected direct
representation at
`directPointwiseReliedHeadProjectionDoesNotReduce`.

## STOP decision

The fresh bounded budget for this representation family is exhausted.  The
partial helpers and L-Unload head were reverted.  No caller-supplied target
guard, ordered registry relation, exact table equality, accumulator equality,
or output-shaped capital is admitted.

The next attempt must introduce a producer-local observation theorem that
states reliance using only lookup-by-name plus lifecycle control observations,
without ever asking the dependent `fiberLifecycle (MkFiber ... table ...)`
projections to reduce against one another.  R41's old direct `Refl`
representation must not be retried.

L-Advance was not opened after this STOP: the requested dependency order and
clean-boundary rule prefer retaining the exact first obstruction over mixing a
second XL family into a failed shift.  Whole-suffix composition remains
unopened.

## Status

- closed generic semantic families: **6/8**;
- L-Unload: map boundary cleared, stopped at pointwise reliance-guard transport;
- L-Advance: unopened;
- whole-suffix RAR/ordinal composition: unopened;
- holes: **20**, split **6/4/8/1/1**;
- revised O6 estimate: **15–28 shifts**, widened from 14–26 only for the newly
  exposed observation bridge.
