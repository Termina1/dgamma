# O6 revision 72: parent-yield transport closes; retirement/recovery order stop

## Scope

Grind shift #80 (overall #134) resumed from `c4fdf17` and executed the accepted
revision-71 equality-view cure. The private lifecycle view and the complete
transported-parent-yield package are retained at `9039970`. Bundle field 2 was
then analyzed in strict field order. Before opening another implementation
unit, its second independent semantic obligation exposed a new wall class:
`ChildRetirementProvenance` is order-sensitive across the moved pair, while the
revision-21 safety family retains only insertion licensing and cross-insertion
evidence.

No bundle field, result record, or adjacent body was partially changed.

## 1. `LocatedReloadingControl` — closed

The private indexed view returns exactly:

```idris
rightLifecycle = Reloading
  sourceRemaining rightAccumulator rightView
```

Its producer matches the concrete source and target `Reloading` lifecycles and
`ReloadingControls` together. Exact remaining-program equality is eliminated
before constructing the view. This avoids the revision-71 mistake of matching a
derived relation and expecting it to rewrite the original target lifecycle
index.

All data and equations are quantity 0.

## 2. Direct correlated parent-fiber package — closed

`LocatedParentYieldControl` retains as one erased package:

- exact source and target parent fibers;
- exact source and target lookup equations;
- every source `ParentRegistrationYield` field indexed directly by the source
  fiber; and
- `FiberControlRelated sourceFiber targetFiber`.

`locateParentYieldControl` opens the source yield where `sourceFiber` is
concrete, calls `pointwiseControlLookupFound`, and seals the target fiber,
lookup, and relation. The package producer elaborates unchanged from the
validated revision-71 shape.

`sealTransportedParentYield` opens the package once with the direct correlated
patterns:

```idris
MkFiber component leftParent  leftRetired  leftTable  leftLifecycle
MkFiber component rightParent rightRetired rightTable rightLifecycle
FibersControlRelated leftParent rightParent ...
```

The exact shared names close both prior nonlinear-fiber walls. It then consumes
`LocatedReloadingControl`, rewrites `targetFound` along
`rightLifecycleIsReloading`, constructs the exact target
`ParentRegistrationYield`, and seals it in private
`LocatedTransportedParentYield`.

The only consumer is literal projection:

```idris
transportedParentYield located = targetParentYield located
```

No target fiber, lifecycle, yield, or lookup is accepted from a caller.

## 3. Attempt ledger

The view+producer unit used its full fresh budget and closed on attempt 3.

1. **Attempt 1:** Idris inferred the local equality annotation's left lookup as
   a value where a type was expected when the `=` notation left key/value
   metavariables underconstrained.
2. **Attempt 2:** replacing the annotation with explicit `Equal` moved the
   diagnostic to the precise unsolved `?key = key` constraint at
   `registry target`.
3. **Attempt 3:** supplying all hidden `lookupFiber` type arguments
   (`name`, `key`, `value`, `world`, `error`) closed the view, target lookup
   reindex, target yield, final package, and projection consumer.

The whole CP5 research module checked. R16 and the frozen spike hash passed
before and after the retained commit.

## 4. Bundle field 2 decomposition

`RegistrationDiscipline` has two independent child-insertion obligations:

1. `ParentRegistrationYield` at the exact insertion before-state — now
   constructively transportable through `ControlEquivalent`; and
2. `ChildRetirementProvenance parent child rest` — either the parent never
   enters recovery in the remaining trace, or the child is retired before the
   first such recovery.

The sealed suffix spine is sufficient after the moved pair: it preserves each
head action/tag and endpoint relation, so `NoParentRecovery` and
`ChildRetiresBeforeRecovery` can be replayed structurally. The unchanged prefix
can likewise be reconstructed structurally once a correct moved-pair boundary
transformer is available.

The moved pair itself is different. Revision-21 safety retains:

- A/A: both activation classifiers;
- A/O: exclusion of an activation actor from a child insertion's parent;
- O/A: exclusion of an activation actor from an inserted child and its parent;
- O/O: inserted-child distinctness and cross-license exclusions.

It retains no condition preventing an earlier child's retirement from crossing
its parent's recovery boundary.

## 5. New semantic countershape

Consider a child insertion in the unchanged prefix whose source provenance
continues into the moved pair:

```text
... OInsert child (ChildOf parent) component ...
    ORetire child ; LLeave parent
```

The source provenance is constructive:

```idris
ChildRetiredBeforeParent
  (ChildRetiresNow retire rest Refl)
```

`LLeave parent` is a `ParentRecoveryStep`. After an O/A adjacent swap the
remaining trace begins:

```text
LLeave parent ; ORetire child
```

Neither constructor of `ChildRetirementProvenance parent child` applies:

- `ParentDoesNotRecover` is impossible because the first step is
  `ParentLeaves`;
- `ChildRetiredBeforeParent` is impossible because the first step is not
  `ORetire child`, and `ChildRetiresLater` requires proof that this first step
  is not a parent recovery.

The existing O/A revision-21 evidence does not rule this out. Its `childSafe`
and `parentSafe` premises are both conditional on **left being an OInsert** and
are therefore vacuous for `ORetire child`. Actor distinctness also holds when
`child` and `parent` differ. `TraceIndependent` concerns generated effect-map
commutation and iterator-yield stability; it does not state the temporal
retirement-before-recovery order.

Thus target discipline cannot be obtained from the landed safety package by the
parent-yield cure alone. This is a new semantic wall class, not another Idris
elimination issue. Per the shift instruction, no field-2 implementation attempt
was opened after identifying it.

## 6. Required design ruling

A sufficient pair-local condition is the erased exclusion:

```idris
(child, parent : name) ->
transitionAction left = ORetire child ->
ParentRecoveryStep parent right -> Void
```

It states exactly that moving `left` behind `right` does not move an earlier
child's retirement past its parent's first recovery. It must be producer-owned
or derived from already authenticated sort-selection capital; it must not be a
detached caller-selected target discipline.

Before any interface revision, the next campaign should:

1. construct a checked genuine O/A instance of the countershape if operational
   applicability permits it;
2. test whether `TraceIndependent` or an existing scheduling theorem actually
   excludes it;
3. inventory what the four genuine diamond producers and the adjacent-sort
   selection site own; and
4. compare a new safety field/constructor premise with a stricter swap-selector
   restriction.

The byte-frozen adjacent declaration must remain unchanged during that design
campaign.

## Frozen-capital audit

The retained package adds only private declarations before the private outer
replay envelope. It does not change:

- revision-21 public safety/record surfaces or any genuine producer;
- `ReplayInvariantBundle`, `AdjacentSwapResult`, RAR, or revision-20 maps;
- joint generator, generator origin, RAR chain, conversion, ordinals,
  correspondence, or suffix alignment;
- the 1183-byte `adjacentSwapSuffixSpike` declaration, SHA-256
  `e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`;
- `src/`, `dgamma.ipkg`, or CP3 blob
  `2c697e532e83989de8591fa6a4378747c6a501c0`.

## Status

- `LocatedReloadingControl`: **proved / retained**;
- raw correlated parent-yield package: **proved / retained**;
- exact target lookup reindex: **proved / retained**;
- target `ParentRegistrationYield`: **proved / retained**;
- projection-only consumer: **proved / retained**;
- bundle field 2 parent-yield sub-obligation: **closed**;
- bundle field 2 whole `RegistrationDiscipline`: **semantic STOP at retirement/recovery order**;
- bundle fields 3–15: **unopened**;
- final assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- movement against accepted 2–16 band: **one shift consumed; 1–15 remain pending design ruling**.
