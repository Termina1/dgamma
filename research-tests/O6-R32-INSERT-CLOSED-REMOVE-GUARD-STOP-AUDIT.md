# O6 revision 32: O-Insert closure and O-Remove guard stop-audit

## Scope

This checkpoint remains private to the research-only
`CP5ConfluenceLocalDiamondSpike`. The frozen `adjacentSwapSuffixSpike` type,
opaque result boundary, sealed spine, production tree, package, and manifest are
unchanged.

## O-Insert closure

The pointwise O-Insert semantic head is now complete.

1. `insertSourceIngredientsPointwise` evaluates `applyAction` directly and
   returns an unindexed producer package containing exact absence, guards, and
   the concrete-after equality. It does not use the inaccessible imported
   indexed view and therefore retains the caller's `sourceAfter` index.
2. `replayPointwiseInsertHead` transports freshness, parent presence, and
   declaration disjointness through `ControlEquivalent`; constructs the checked
   target insertion; derives target well-formedness; relates both installed
   empty effect tables to their actual endpoints; transports pointwise controls
   through the fresh insertions; proves the exact head map; constructs the
   non-advance singleton RAR; and packages occurrence and ordinal evidence.

No endpoint, target map, target guard, RAR, occurrence, ordinal, or target bundle
is accepted as input. The source package required three elaboration attempts:
the final repair used the branch's definitional `Refl` guard rather than an
independently oriented with-proof.

Commits:

- `4d4a6d7` — derive unindexed insert source ingredients;
- `e0f18f6` — replay pointwise insert suffix heads.

## O-Remove foundations

Two reusable foundations elaborate:

- `pointwiseNoChildPreserved` audits every uniquely named target entry, finds
  its source fiber through symmetric pointwise control, transports the exact
  parent field, and proves target childlessness without assuming registry order;
- `removeEffectFrameRelated` specializes the checked actual-transition frame to
  the empty table installed by O-Remove.

Commits:

- `80dc7d6` — transport childlessness through pointwise controls;
- `ef41505` — specialize the checked remove effect frame.

## Bounded O-Remove source-normalizer attempt

The unindexed O-Remove source package was attempted three times and reverted.
It directly evaluated `lookupFiber` and the executable removable guard. The
first attempt also confirmed that `removeSuccessView`, although used by older
code in this module, is not accessible to the new consumer through the current
compiled import boundary. The direct replacement then stopped at exact
orientation/normalization of the nested lazy Boolean guard:

```text
Can't solve constraint between:
  True
and:
  retired oldFiber &&
    Delay (isInactive (fiberLifecycle oldFiber) &&
      Delay (not (hasChild actor source))).
```

No theorem premise or output capital can legitimately solve this: it is an
internal normalization problem. The attempted helper and partial head were
fully reverted. The next authorized O-Remove attempt must split `retired`,
`isInactive`, and `hasChild` as three explicit executable views and return their
individual equations, rather than transport one composite `with` proof. If that
staged normalizer again reaches the same composite-guard constraint, the family
requires a dedicated expected-failure Idris probe before any further proof work.

This stop is not evidence that O-Remove is uninhabitable, and no output-shaped
capital was requested. It is the bounded per-family stop-audit for this shift.
No lifecycle family was opened after the stop.

## Inventory and estimate

Fully closed semantic pointwise heads: O-Insert and O-Retire.

Generic capital closed for every non-LAdvance singleton once its semantic head
map exists: RAR, action/registration occurrence, generation, ordinal, exact
alignment, endpoint sealing, and map retention.

Still open: O-Remove; L-Begin; L-Divert; L-Leave; L-Unload with accumulator map
transport; and L-Advance with iterator-stage/yielded-map provenance. Whole
suffix RAR/ordinal composition and final adjacent-result assembly remain gated
behind those six families.

The remaining O6 estimate changes from **20–36** to **18–34 shifts**. O-Insert
closed in two proof shifts; the O-Remove childlessness/effect foundations reduce
its eventual body, while the staged guard normalizer remains charged. Holes
remain 20 with split `6/4/8/1/1`.
