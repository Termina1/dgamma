# O6 revision 52: nonempty join yielded-equation STOP-AUDIT

## Scope

Shift #60 (overall #114) began at accepted revision-51 HEAD `0331808` and
used the authorized fresh budget for the thin top-level nonempty agreement join.
All three branch seals remained unchanged. The join exhausted its three-attempt
budget while materializing the yielded agreement at the resolved runtime
indices and was fully reverted. No outer owner eliminator, whole-suffix lemma,
final result, frozen signature, production file, or hole changed.

## Retained premise

The exact revision-51 attempt-3 join was restored: one indexed
`RuntimeIteratorOutcomeAgreement` is computed by its future owner and carried
through source/target capability-resolution and evaluator-run splits. No branch
recomputes it. Undefined/mixed shapes use the existing indexed contradictions.

The failure/failure clause added the two authorized typed equations:

```idris
sourceOutcome = rewrite sourceResolved in rewrite sourceRan in Refl
replayedOutcome = rewrite replayedResolved in rewrite replayedRan in Refl
```

Passing these instead of bare `Refl` closed the revision-51 failure wall.

## Three-attempt diagnostic

### Attempt 1: yielded constructor reconstruction

Elaboration passed the failure seal and reached the success/success clause. It
then rejected reconstructing `RuntimeYieldsAgree` directly for the retained
yielded seal because the expected indices were still the syntactic
`runtimeAdvanceOutcome` applications, while the constructor had concrete
`Just (IteratorYielded ...)` indices:

```text
Can't solve constraint between:
  Just (IteratorYielded ... replayedLocal ... replayedUndo ...)
and:
  case resolveCommittedValues ... replayedRegistry of ...
```

### Attempt 2: reuse the carried agreement

The branch passed the original carried `agreement` rather than rebuilding the
constructor. The same mismatch remained: after dependent case elimination the
term's indices were concrete yielded outcomes, while the helper call expected
the unreduced runtime applications.

### Attempt 3: explicit with-proof elimination

The success/success branch explicitly eliminated `sourceResolved`,
`replayedResolved`, `sourceRan`, and `replayedRan` before opening the agreement.
Idris rejected the first equality pattern because the named `with` proof is
oriented from the runtime computation to the observed result and was not
accepted as definitional `Refl` at that nested position:

```text
Can't solve constraint between:
  Just ?_
and:
  resolveCommittedValues ...
... case sourceResolved of Refl
```

No fourth equation-materialization variation was compiled. The entire
undefined contradiction and nonempty join were reverted. No partial branch,
outer head, or metavariable remains.

## Scoped next representation

This stop is confined to packaging the already-proved yielded agreement across
its two outcome equalities. The three seals and sealed dispatcher design remain
accepted.

A producer-owned dependent package avoids identifying or separately
transporting the agreement proof and its certificate:

```idris
record LocatedSealedPointwiseAdvanceYieldedAgreement first second where
  constructor MkLocatedSealedPointwiseAdvanceYieldedAgreement
  locatedYieldedAgreement : RuntimeIteratorOutcomeAgreement ... first second
  0 locatedYieldedSeal :
    SealedPointwiseAdvanceYieldedAgreement locatedYieldedAgreement
```

In success/success, construct this package at the two concrete yielded outcomes
using `(RuntimeYieldsAgree ..., MkSealedPointwiseAdvanceYieldedAgreement)`, then
transport the **whole package** sourceward across `sym replayedOutcome` and
`sym sourceOutcome` with `replace`. Destructing the transported package gives an
agreement and seal sharing exactly the runtime-function indices expected by
`eliminateSealedPointwiseAdvanceYieldedBranch`. This does not equate proof
objects, does not alter a public boundary, and does not recompute the agreement.

This representation requires a dedicated acceptance decision and a fresh
three-attempt budget; it must not be attempted as a fourth local rewrite.

## Status

- branch seals: **3/3 closed and unchanged**;
- nonempty agreement join: **STOP; fully reverted**;
- complete outer L-Advance head: **open**;
- semantic families: **7/8**;
- whole-suffix composition: **unopened and gated**;
- final adjacent result: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- O6 estimate: **5–17 shifts**, held unchanged because no new declaration was
  retained in this shift.
