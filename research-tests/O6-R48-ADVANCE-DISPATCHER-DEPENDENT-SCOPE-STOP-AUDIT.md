# O6 revision 48: L-Advance dispatcher dependent-scope STOP-AUDIT

## Scope

Shift #56 began at accepted revision-47 HEAD `fc7530f` and retried only the
private exhaustive sealed L-Advance dispatcher. The retained generator/stage
provenance, singleton RAR, operational producers, and common head packager were
not changed. Frozen signatures, production files, caller boundaries, and holes
were untouched.

## Three-attempt diagnostic

### Attempt 1: ratified component naming

The revision-47 eliminator was restored with:

- `finish {component}` retained;
- `{component}` named in both `dispatchRemaining` clauses;
- the exhaustive empty, missing, failure, yielded-divert, yielded-finish, and
  yielded-iteration branch structure unchanged.

Elaboration passed both previous component-shadow walls and reached the nested
`dispatchDefined` helper. Its captured accumulator function was re-abstracted
by the local `where`, so the source lookup proof no longer shared the exact
function binder:

```text
Mismatch between: sourceAccumulator and sourceAccumulator.
... dispatchDefined ...
```

### Attempt 2: explicit dependent proof arguments

`dispatchDefined` was changed to accept the concrete source/target lookups,
parent equality, accumulator relation, and transition-map relation explicitly.
Every `with` clause carried those arguments. The same mismatch remained: the
nested helper's *type-level accumulator function itself*, not merely its proof,
was independently abstracted.

```text
Mismatch between: sourceAccumulator and sourceAccumulator.
... dispatchDefined sourceFound replayedFound ...
```

This rules out further nested-`where` annotation variations.

### Attempt 3: top-level nonempty helper

The nonempty dispatcher was moved to a top-level private helper with component,
step/rest, accumulators, view, lookups, relations, checked source, maps, and
endpoint all explicit. The nested accumulator mismatch disappeared completely.
Elaboration reached two later dependent refinements:

1. In the replay-side missing-capability branch, recomputing
   `runtimeAdvanceOutcomeRelated` did not definitionally rewrite its first
   runtime outcome to `Nothing` from the already-retained replay resolution:

   ```text
   Can't solve constraint between:
     case resolveCommittedValues ... replayedRegistry of ...
   and Nothing.
   ```

   The production dispatcher avoids this by carrying one outcome-agreement
   value as an indexed argument while splitting both runtime outcomes.

2. In the outer sealed eliminator, `case retiredSame of Refl` selected the
   target-oriented retired index. The retained source lookup stayed indexed by
   the source flag:

   ```text
   Mismatch between: replayedRetired and sourceRetired.
   ... sealedSourceFound
   ```

   The equality must be eliminated in the opposite orientation before entering
   the common-single-retired-flag helper.

The third attempt exhausted the fresh dispatcher budget. The complete helper
and eliminator were reverted. No incomplete dispatcher, outer head, or
metavariable remains.

## Ratified candidate for the next fresh budget

Keep the top-level nonempty helper—the attempt proves it removes the independent
accumulator-function wall—but change two indices before compiling:

1. add the producer-owned `RuntimeIteratorOutcomeAgreement` as an explicit
   indexed argument to the helper, computed once by the sealed eliminator;
   split resolutions/runs while carrying that value, as in the production
   dispatcher, rather than recomputing the theorem inside refined branches;
2. eliminate `sym retiredSame` to refine the target retired flag to the retained
   source flag before passing source lookup capital.

This remains private producer-owned capital. It neither widens the caller
boundary nor requests output-shaped evidence.

Only after this dispatcher compiles should the thin
`replayPointwiseAdvanceHead` and 8/8 milestone be opened.

## Status

- generator/stage provenance, singleton RAR, common head packager: **retained**;
- exhaustive runtime dispatcher: **STOP-AUDIT; fully reverted**;
- semantic families: **7/8**;
- whole-suffix composition: **unopened and gated**;
- adjacent result: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- O6 estimate: **7–19 shifts**, unchanged because this shift retained no new
  declaration but removed the nested-helper route and identified the exact two
  dependent indices required by the top-level representation.
