# O6 revision 43: L-Unload closed; L-Advance foundations audit

## Scope

Shift #51 began at accepted revision-42 HEAD `42e3a75` and used only the
ratified generic-owner/sealed-eliminator route. R41 direct projection, revision
42 direct-destruction, and revision 42 projection-only consumers were not
retried. No frozen declaration, public adjacent-swap signature, production
file, or caller premise changed.

## L-Unload closure

The pointwise L-Unload semantic family is now complete.

`SealedPointwiseUnloadEvaluator` makes the source owner a constructor result and
retains inside the sealed package:

- the exact owner lookup;
- the operational false reliance guard;
- the source accumulator/view/outcome;
- the exact concrete source endpoint.

`LocatedSealedPointwiseUnloadSource` exposes only the generic owner and its
lookup. `sealPointwiseUnloadSource` opens the previously accepted
`PointwiseUnloadSourceObservation` before any control relation exists.

`eliminateSealedPointwiseUnloadHead` is the sole shape eliminator. The GADT and
`FiberControlRelated` indices are shared before refinement. Exact source lookup
and source endpoint evidence are retained inside the GADT constructor, avoiding
both dependent self-unification failures found in revisions 41–42. The
eliminator constructs:

- target reliance via `pointwiseReliedFalse`;
- the checked target `LUnload` transition;
- source/target `Inactive` control relation;
- pointwise post-replacement controls under independently ordered registries;
- strong relational actual maps via `pointwiseRelatedLifecycleMaps`;
- the post-effect endpoint by composing actual frames with those maps;
- singleton RAR, occurrence, and relative ordinal capital.

`replayPointwiseUnloadHead` locates the two generic owners and delegates all
shape opening to that eliminator. The table term did **not** reappear through
this design, so the escalation boundary was not triggered.

## L-Advance progress

The eighth semantic family is opened but not closed.

Retained foundations are:

- `SealedPointwiseAdvanceEvaluator` and
  `LocatedSealedPointwiseAdvanceSource`, which authenticate an exact reloading
  source owner and checked source transition without exposing computed table
  projections to the outer producer;
- `sealPointwiseAdvanceSource`, exhaustive over owner lifecycle and rejecting
  impossible non-reloading successful actions;
- `PointwiseAdvanceOperationalReplay`, the common indexed result of any of the
  empty, failure, yielded-finish, yielded-iter, or landing-divert branches;
- `packagePointwiseAdvanceOperationalReplay`, which uniformly turns a target
  raw evaluator, post-control relation, and `PartialMapsRelated` actual-map
  proof into checked target and relational endpoint capital using actual effect
  frames.

The next shift must implement the runtime branch eliminator. Nonempty branches
should consume `runtimeAdvanceOutcomeRelated` / retained exact stage outcomes
and `iteratorStageOutcomeRelated`; successful branches must retain yielded
inverse-map provenance. After all operational branches share
`PointwiseAdvanceOperationalReplay`, singleton iterator-stage/generator RAR
capital can be assembled without widening any caller boundary.

No incomplete L-Advance function or partial branch remains in the tree.

## Status

- closed generic semantic families: **7/8**;
- L-Unload: **closed** through the ratified sealed eliminator;
- L-Advance: source sealing and common operational endpoint package proved;
  runtime branches and RAR remain open;
- whole-suffix RAR/ordinal composition: unopened, correctly gated behind 8/8;
- holes: **20**, split **6/4/8/1/1**;
- revised O6 estimate: **12–24 shifts**, narrowed from 16–30 after L-Unload
  closure and the reusable L-Advance operational package.
