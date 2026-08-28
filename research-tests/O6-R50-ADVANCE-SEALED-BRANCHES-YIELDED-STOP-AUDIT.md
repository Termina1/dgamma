# O6 revision 50: sealed L-Advance branches, yielded STOP-AUDIT

## Scope

Shift #58 (overall #112) began at accepted revision-49 design-gate HEAD
`8c999b3`. It implemented the authorized producer-owned per-outcome dispatcher
shape. The empty and defined-failure seals are retained as lemma-sized commits.
The yielded seal consumed its independent three-attempt budget and was fully
reverted, as required. No outer head, whole-suffix lemma, final result, frozen
signature, production file, or hole changed.

## Retained branch seals

### Empty branch — `217855e`

`eliminateSealedPointwiseAdvanceEmptyBranch` delegates target-match ownership,
checked replay, endpoint, maps, and exact singleton RAR/ordinal packaging to the
existing proved producers. It compiled on its first attempt and passed R16
before commit.

### Defined-failure branch — `95e72c2`

`eliminateSealedPointwiseAdvanceFailureBranch` accepts only the two exact
indexed runtime failure equations obtained by eliminating the once-computed
agreement. It opens both capability resolutions and both evaluator runs itself.
Undefined and successful shapes are eliminated by the indexed equations; the
positive shape derives the observable error equality internally and enters
`replayPointwiseAdvanceRaisedOperational` plus
`packagePointwiseAdvanceHead`. No resolution/run proof is caller capital.

Attempt 1 reached only the known erased equality-annotation parser ambiguity.
Parenthesizing the three local equality types closed the branch on attempt 2.
R16 passed before commit.

## Yielded seal: three-attempt diagnostic

All attempts carried the same once-computed indexed
`RuntimeIteratorOutcomeAgreement`; none recomputed runtime outcomes. They also
kept inverse maps fully typed and source/target match equations producer-owned.

### Attempt 1: premature indexed agreement pattern

A private `SealedPointwiseAdvanceYieldedAgreement` certificate and yielded
eliminator were introduced. Pattern-matching `RuntimeYieldsAgree` in the outer
function clause attempted to force the still-unreduced runtime functions before
capability resolution:

```text
Can't solve constraint between:
  Just (IteratorYielded ...)
and:
  case resolveCommittedValues ... of ...
```

### Attempt 2: delayed agreement elimination

The agreement and yielded certificate were carried generically through both
resolution/run splits. Only the fully reduced success/success clause opened
`RuntimeYieldsAgree`; this cleared the premature-index wall and reached the
final target-match dispatch.

Direct `case matches` refinement reproduced the known computed-scrutinee issue:

```text
Can't solve constraint between: targetMatches ... and False.
... sourceFalse = sourceMatches
```

### Attempt 3: explicit top-level match eliminator

A top-level `packageSealedPointwiseAdvanceYieldedMatch` was added, explicitly
quantifying the Boolean and both source/target equations. Its clauses separately
owned divert, finish, and iter packaging, eliminating the computed-scrutinee
problem by the already-proved empty-branch pattern.

Before checking the bodies, elaboration stopped in the new helper signature:

```text
Can't solve constraint between: ?world [no locals in scope]
and: ?world [no locals in scope].
... resolveCommittedValues ... view sourceRegistry
```

The resolver occurrence omitted the full explicit implicit parameter set
`{name} {key} {value} {world} {error}` used by the existing operational
producers. The mechanically indicated signature correction was **not compiled**
because this was attempt 3.

The complete yielded certificate, match helper, eliminator, and every partial
branch were reverted. No metavariable or incomplete declaration remains.

## Stop boundary

Per the revision-49 authorization, exhaustion of any seal budget requires an
immediate STOP-AUDIT. The next shift may resume only after accepting a fresh
yielded-seal budget. The exact retained recipe is:

1. generic agreement plus yielded certificate through resolution/run splits;
2. open `RuntimeYieldsAgree` only in the fully reduced success/success clause;
3. top-level explicit Boolean match eliminator;
4. fully explicit resolver implicits in that helper signature;
5. typed source-to-target inverse maps and producer-owned exact match equations;
6. careful clause layout.

## Status

- empty seal: **closed and retained**;
- defined-failure seal: **closed and retained**;
- yielded seal: **STOP; fully reverted**;
- complete L-Advance head: **open**;
- semantic families: **7/8**;
- whole-suffix composition: **unopened and gated**;
- final adjacent result: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- O6 estimate: **6–18 shifts** after retaining two of the three branch seals,
  subject to acceptance of the yielded continuation budget.
