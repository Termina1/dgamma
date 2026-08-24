# O5 ordered-control order audit

Date: 2026-08-16
Branch baseline: `cp5-thm73-scoping`
Shift baseline: `6f9856a11aac648e0575192726379b331cea27c2`
Discovery HEAD: `9631d79` (after the checked early-`OInsert` raw replay column)

## Stop reason

The remaining O5 endpoint assembly reaches a structural contradiction in the
`OInsert`/`OInsert` case.  This is not a dictionary-coherence mismatch and it is
not missing executable applicability capital.  Both moved transitions are now
constructible.  The obstruction is the *ordered* control field of
`LocalRelationalDiamond`:

```idris
0 swappedControls : OrderedRegistryControlsRelated name key world error value
  (bindings (registry originalFinal))
  (bindings (registry swappedFinal))
```

Per the stop-audit-gate rule, proof work stopped before changing this accepted
record or the O5 declaration.

## Exact producer trace

Let two distinct actors `leftActor` and `rightActor` both perform successful
`OInsert` transitions from a source registry `source`.
`insertBinding` prepends its fresh binding.  Therefore the original order is:

```text
left then right:  rightActor :: leftActor :: bindings source
```

The source-authenticated transposition proved in shift 76 executes the checked
early right insertion and then reconstructs the checked moved left insertion.
Its order is necessarily:

```text
right then left:  leftActor :: rightActor :: bindings source
```

These are the only executable endpoints of `applyAction`; no caller-selected
registry, action, evaluator output, or endpoint is involved.

The established private producer is:

```idris
orchestrationRawAfterCheckedInsert
```

It handles all three left-rule cases.  In the left-insert case it derives:

- source freshness and parent preservation from the actual checked views;
- provision compatibility by proving finite provision-overlap symmetry and
  extracting the later checked right insertion's head disjointness;
- the remove/insert parent-child exclusion, for the left-remove case, from the
  actual later successful right insertion after deletion.

Thus the early-insert applicability column is sealed at source.  The order
obstruction appears only after these genuine producers exist.

## Why `OrderedRegistryControlsRelated` cannot relate the endpoints

The family is indexed structurally:

```idris
data OrderedRegistryControlsRelated ... where
  OrderedControlsNil : ... [] []
  OrderedControlsCons :
    (actor : name) ->
    FiberControlRelated leftFiber rightFiber ->
    OrderedRegistryControlsRelated ... leftRest rightRest ->
    OrderedRegistryControlsRelated ...
      (Bind actor leftFiber :: leftRest)
      (Bind actor rightFiber :: rightRest)
```

Every `OrderedControlsCons` requires the same actor at both heads.  Consequently,
a purported relation between the two insertion endpoints forces
`rightActor = leftActor` at the first constructor, contradicting O5's accepted
actor-distinctness premise.  Provision symmetry, generation scans,
`insertedChildrenDistinct`, and `generatedLicensesDoNotCross` cannot change this
list-index contradiction.

The obstruction is independent of the stored `DecEq` dictionaries fixed by
revision 15.

## Consumer audit

Tracked search at discovery HEAD finds:

- one declaration of the `swappedControls` record field;
- three existing `MkLocalRelationalDiamond` producers for the closed O3/O4
  orientations;
- **zero projections or downstream uses of `swappedControls`**.

`LocalRelationalDiamond` is consumed as a package by adjacent-swap records, but
no checked producer or theorem extracts this field.  Therefore the ordered
field currently behaves as producer-only specification capital.  It is stronger
than registry observation by actor name and stronger than the executable
semantics can preserve under two independent fresh insertions.

This audit does not itself retire or weaken the field.  R14 N2 coordinate gating
and the accepted O3/O4 interfaces remain untouched pending authorization.

## Options requiring a gate

1. **Retire `swappedControls` as vestigial producer-only capital.**
   This is the smallest declaration change if the zero-consumer audit is
   accepted.  It changes the `LocalRelationalDiamond` constructor and therefore
   requires a scoped revision and re-review of O3/O4 producers, even though no
   downstream theorem projects the field.

2. **Replace it with a permutation/name-indexed control relation.**
   This is semantically appropriate if endpoint control correspondence is
   intended specification capital.  A candidate must authenticate the actor
   lookup correspondence rather than accept a caller-selected permutation.
   This is a larger interface design and producer/test task.

3. **Exclude `OInsert`/`OInsert` from O5.**
   This makes the local theorem provable but defeats the stated O5 purpose and
   blocks canonical sorting of distinct actor blocks containing yielded
   insertions.  Not recommended without a replacement sorting argument.

4. **Change insertion to canonical registry ordering.**
   This changes production operational semantics and is out of scope for the
   research grind.  Not recommended.

Recommendation: independently verify the zero-consumer claim and authorize
option 1 if no future accepted consumer needs ordered list identity.  Otherwise
design option 2 with a producer-authenticated name/permutation relation before
resuming O5.

## Scope and state

No declaration, record field, hole signature, closed O3/O4 theorem, production
module, package file, or CP3 theorem was changed by this audit.  The O5 hole
remains, as do 22 total holes with split `6/4/8/3/1`.
