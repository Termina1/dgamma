# O6 revision 42: L-Unload observation-consumer STOP-AUDIT

## Scope and retained progress

Shift #50 began at accepted revision-41 HEAD `7e4c437` and followed the ruling
that R41's direct `fiberLifecycle`/`Refl` route may not be retried.

Three independently elaborating producer foundations are retained:

1. `pointwiseReliedFalse` proves the global L-Unload reliance guard across
   independently ordered registries. Each target entry is located by name, its
   matching source entry is recovered through `ControlEquivalent`, and
   `lifecycleControlReliedHeadSame` compares only the lifecycle observation.
   No direct dependent `fiberLifecycle` projection is compared.
2. `PointwiseUnloadSourceObservation` and
   `pointwiseUnloadSourceObservation` retain one successful operational
   observation: the exact owner lookup, Unloading decomposition, reliance
   guard, exact `LUnloadTag`, and concrete replacement endpoint.
3. `pointwiseRelatedLifecycleMaps` promotes related lifecycle owners to the
   landed strong `PartialMapsRelated (EffectStateEquivalence keyEq)` boundary.
   It is shared with the later L-Advance producer.

All three foundations elaborate in
`CP5ConfluenceLocalDiamondSpike.idr`; R16 was checked before each lemma-sized
commit.

## Bounded head attempts

Two consumer representations were attempted after the foundations:

1. destruct the indexed source observation and then reconstruct a named source
   owner before consuming `FiberControlRelated`;
2. retain the source observation as a value, use projections for every source
   field, and consume `FiberControlRelated` only after related-map capital had
   already been sealed against the generic located owners.

Both target applicability and relational-map construction succeed before the
failure. The second representation reaches the precise observation-consumer
boundary and is rejected when dependent refinement tries to identify the table
owned by the control-relation pattern with the table projection of the computed
source observation. Idris reports:

```text
Pattern variable sourceTable unifies with:
  ... .unloadObservedTable
Suggestion: Use the same name for both pattern variables, since they unify.
```

The first representation showed the same disease one index earlier as a false
self-mismatch such as:

```text
Mismatch between: sourceOutcome and sourceOutcome (implicitly bound ...).
Mismatch between: sourceRetired and sourceRetired (implicitly bound ...).
```

These are not runtime or mathematical differences. They are elaborator-visible
identities between independently bound indices of a computed dependent record.
The table term has therefore reappeared *through* the accepted observation
route, triggering the supervisor-mandated STOP rule.

## Semantic analysis

There is still no evidence that the desired L-Unload replay statement is false:

- global reliance transport is now proved constructively;
- target applicability is executable from the transported guard;
- source and target accumulator maps satisfy the landed relational boundary;
- the post-unload control states need only the common inactive outcome and do
  not require table equality;
- actual effect frames can compose with the relational maps to derive the
  endpoint effect relation.

The gap is the consumer representation. The current observation exposes a
fully decomposed dependent source fiber. Destructing a separately indexed
`FiberControlRelated` then asks Idris to refine the computed record projections
against fresh pattern indices. The next representation must instead retain a
**generic located owner** together with a sealed owner-shape/evaluator package,
consume the generic owner in `ControlEquivalent` and map production, and open
its shape only inside one producer-local eliminator. This mirrors the
`LocatedForeignUnloadPlanView` discipline more closely than projecting all
owned fields into the outer head.

That redesign must not add an ordered-registry relation, target reliance guard,
exact accumulator result equality, exact table equality, or any output-shaped
premise. The two failed consumer forms are banned from retry.

## STOP decision and status

The complete partial `replayPointwiseUnloadHead` was reverted. No head, target
transition, or partial consumer helper remains. The three independently
elaborating foundations above remain committed.

L-Advance was not opened after this mandated dependency-ordered stop, and
whole-suffix composition remains unopened.

- closed generic semantic families: **6/8**;
- L-Unload: source observation, reliance transport, and relational maps proved;
  stopped at dependent observation consumption;
- L-Advance: unopened;
- whole-suffix RAR/ordinal composition: unopened;
- holes: **20**, split **6/4/8/1/1**;
- revised O6 estimate: **16–30 shifts**, adjusted from 15–28 for the sealed
  generic-owner eliminator now shown necessary.
