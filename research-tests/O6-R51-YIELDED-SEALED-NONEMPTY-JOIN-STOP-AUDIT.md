# O6 revision 51: yielded seal closed; nonempty join STOP-AUDIT

## Scope

Shift #59 (overall #113) resumed at accepted revision-50 HEAD `440df40`.
The authorized yielded-seal continuation closed on its first fresh attempt and
is retained at `1f45b16`. The following thin nonempty agreement join exhausted
its own three-attempt budget and was fully reverted. No outer owner eliminator,
whole-suffix lemma, final result, frozen signature, production file, or hole
changed.

## Yielded seal closure — `1f45b16`

The exact accepted revision-50 attempt-3 representation was restored:

- generic once-computed `RuntimeIteratorOutcomeAgreement` plus erased yielded
  certificate carried through both capability resolutions and evaluator runs;
- `RuntimeYieldsAgree` opened only in the fully reduced success/success clause;
- top-level explicit Boolean/equation match eliminator;
- delegated divert/finish/iter success tail;
- fully typed inverse-map orientation;
- exact producer-owned source and replay match equations.

Adding `{name} {key} {value} {world} {error}` to both resolver occurrences in
the match-eliminator signature removed the revision-50 ambiguity. The complete
343-line yielded package compiled on attempt 1 and passed R16 before commit.
All three authorized branch seals are now retained.

## Nonempty agreement join: three-attempt diagnostic

### Attempt 1: undefined-branch type annotation

A private `pointwiseAdvanceUndefinedContradiction` and top-level
`replayPointwiseAdvanceNonemptyHead` join were introduced. The contradiction
producer opens the source resolution/run and rules out an undefined stage for
an authenticated source action. The declaration initially left `tag` and
`sourceAfter` auto-implicit in an unparenthesized action equality:

```text
Can't solve constraint between: ?value and ?value.
... MkSystemState sourceWorld sourceRegistry
```

### Attempt 2: agreement opened before runtime reduction

Making `tag` and `sourceAfter` explicit and parenthesizing the action equality
closed attempt 1. The direct RHS `case agreement` still tried to select
`RuntimeOutcomesUndefined` while both indexed runtime functions were unreduced:

```text
Can't solve constraint between:
  Nothing
and:
  case resolveCommittedValues ... of ...
```

Idris consequently marked the failure and yielded clauses unreachable.

### Attempt 3: explicit resolution/run join

The top-level join was changed to carry the single agreement through source and
target resolution and run splits. All impossible combinations used the existing
indexed agreement contradictions. This reached the concrete failure/failure
branch. Calling the retained failure seal with bare `Refl` for its two exact
runtime equations failed because the surrounding `with` proof names had not
been explicitly rewritten into those equations:

```text
Can't solve constraint between:
  Just (IteratorRaised sourceError)
and:
  case resolveCommittedValues ... sourceRegistry of ...
... sourceError replayedError Refl Refl
```

The indicated continuation is two fully typed local equations constructed with
`rewrite sourceResolved in rewrite sourceRan in Refl` and the corresponding
replayed proofs, then passed to the existing failure seal. That correction was
**not compiled** because this was attempt 3.

The undefined contradiction and the entire nonempty join were reverted. No
partial branch, outer head, or metavariable remains.

## Stop boundary

This stop concerns only the thin nonempty agreement join. The sealed dispatcher
design and all three branch seals remain accepted and retained. A fresh join
budget should preserve the attempt-3 top-level resolution/run split and add the
two explicit typed runtime equations in the failure/failure clause. It must not
recompute the agreement or widen any seal boundary.

## Status

- empty seal: **closed**;
- defined-failure seal: **closed**;
- yielded seal: **closed**;
- seals: **3/3**;
- nonempty agreement join and complete outer head: **STOP; reverted**;
- semantic families: **7/8**;
- whole-suffix composition: **unopened and gated**;
- final adjacent result: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- O6 estimate: **5–17 shifts**, narrowed from the accepted **6–18** band by
  retaining the yielded seal, subject to acceptance of a fresh join budget.
