# O6 revision 54: generic aligned-head dispatch erasure STOP-AUDIT

## Scope

Shift #62 (overall #116) resumed from the accepted 8/8 milestone at
`9b01d2c`. It used the supervisor-authorized fresh three-attempt budget for the
private all-action dispatcher needed to instantiate the retained generic suffix
spine recursion. The continuation recipe from revision 53 was followed:

- dispatch on `AlignedStep ... NoTransitions AlignedEnd`;
- wildcard the definitionally generated source step;
- keep the L-Begin lookup rewrite;
- parenthesize every erased raw/tag equality annotation;
- derive fixed tags from producer-owned source plan views;
- delegate L-Advance directly to `replayPointwiseAdvanceHead`.

The parenthesized annotations cleared the revision-53 wall and five clauses
elaborated far enough to reach L-Divert. The remaining obstruction is an erased
scrutinee binding, not a semantic family or suffix-capital failure. The budget
was exhausted, and the complete dispatcher was reverted. No whole-suffix lemma,
final assembly, frozen signature, production file, or hole changed.

## Attempt 1: first five branches clear; Divert erasure wall

The restored aligned-singleton dispatcher used exact parenthesized forms such as:

```idris
let 0 raw : (applyAction ... = Just (tag, afterState))
    ...
    0 tagSame : (tag = OInsertTag)
```

O-Insert, O-Retire, O-Remove, L-Begin, and the direct L-Advance delegation all
cleared. Idris stopped at the L-Divert source-plan producer:

```text
DGamma.CP4DeletionSelectedForeignLifecycleDivert.foreignDivertPlanView
is not accessible in this context.
```

The function is public but has quantity 0. The local unannotated
`located = foreignDivertPlanView ...` binding was therefore inferred as runtime
capital and could not consume the erased source-plan view. This is precisely the
kind of detached/runtime widening the O6 design forbids; no quantity was widened.

## Attempt 2: diagnostic tag theorem reaches L-Leave import boundary

As a localization diagnostic, L-Divert used the already imported erased
`successfulLDivertTag`. That cleared the Divert branch and reached L-Leave. The
analogous `successfulLeaveTag` exists in `CP4RecoverySelectedStep` but is not in
this module's dependency surface:

```text
Undefined name successfulLeaveTag.
Did you mean: successfulLDivertTag?
```

No import was added. This preserved scope and confirmed that only the erased
fixed-tag extraction remained; all closed head producers accepted the transported
tag.

## Attempt 3: source-plan route restored; untyped quantity syntax rejected

The authorized source-plan view representation was restored for Divert and
Leave, and the retained unload observation was restored for L-Unload. The three
scrutinees were marked with an untyped quantity prefix:

```idris
0 located = foreignDivertPlanView ...
```

Idris parsed the prefix as an ordinary numeric term rather than a quantified
untyped `let` declaration:

```text
No type declaration for ... fromInteger.
```

A quantity-0 local requires a full type annotation, or the source-plan
elimination must be factored into a dedicated erased per-action tag lemma whose
result is only `tag = FixedTag`. The latter is the cleaner authorized fallback:
it keeps the dependent plan witness wholly inside its producer and each dispatcher
clause delegates separately to the already closed head.

## Reversion and next representation

All dispatcher and tag-helper code was reverted after attempt 3. No incomplete
branch, metavariable, or new import remains.

A fresh fallback budget should use three small erased helpers before attempting
the exhaustive dispatcher:

1. `pointwiseDivertTag`, returning `tag = LDivertTag` by eliminating
   `foreignDivertPlanView` entirely inside the quantity-0 helper;
2. `pointwiseLeaveTag`, returning `tag = LLeaveTag` by eliminating
   `foreignLeavePlanView` and `foreignLeaveReplayData` inside the helper;
3. `pointwiseUnloadTag`, returning `tag = LUnloadTag` by projecting the retained
   `pointwiseUnloadSourceObservation` inside the helper.

The dispatcher then has eight separate clauses: fixed-tag equality elimination
followed by the matching closed head; L-Advance delegates directly. This is the
supervisor-named per-action-clause fallback, not a design change. Each helper is
a separately budgeted resisting lemma and should be committed only with the
complete dispatcher or at an independently useful typed boundary.

## Status

- semantic action families: **8/8, unchanged**;
- generic aligned all-action dispatcher: **STOP; fully reverted**;
- retained generic spine recursion: **typed, not instantiated**;
- whole-suffix RAR/ordinal composition: **unopened**;
- final adjacent-result assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- estimate: **3–15 shifts held**, pending the erased per-action tag-helper
  fallback.
