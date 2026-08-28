# O6 revision 53: L-Advance closed; generic head dispatch STOP-AUDIT

## Scope

Shift #61 (overall #115) began at accepted revision-52 HEAD `6d2100e`.
The authorized dependent agreement/seal transport closed the nonempty join, and
the thin outer L-Advance head then closed the eighth semantic family. Both are
retained as lemma-sized commits. The following generic all-action head
dispatcher exhausted its own three-attempt budget and was fully reverted. No
whole-suffix composition, final result, frozen signature, production file, or
hole changed.

## Retained closures

### Dependent yielded agreement transport — `92cc114`

`LocatedSealedPointwiseAdvanceYieldedAgreement` packages the indexed
`RuntimeIteratorOutcomeAgreement` and its
`SealedPointwiseAdvanceYieldedAgreement` certificate under shared source/target
outcome indices. In success/success the producer:

1. materializes exact source and replay yielded outcome equations from the named
   resolution/run proofs;
2. constructs the agreement+seal package at the two concrete outcomes;
3. transports the whole package sourceward with `replace` across
   `sym replayedOutcome`, then `sym sourceOutcome`;
4. destructs the transported package and enters the retained yielded seal.

The authorized representation compiled on attempt 1. The failure branch keeps
the named equation recipe and the agreement is still computed exactly once.
R16 passed before commit.

### Thin L-Advance owner chain — `abdde3d`

`replayPointwiseAdvanceRemainingHead`,
`eliminateSealedPointwiseAdvanceHead`, and `replayPointwiseAdvanceHead` close the
outer chain. The owner and control relation are opened once, the nonempty
agreement is computed once, and empty/nonempty programs enter the three retained
seals and common head packager.

Attempt 1 exposed that matching `remainingSame` did not rewrite the target lookup
proof. Attempt 2 explicitly transported the target lookup in three producer-owned
steps — remaining, view, then retirement — each sourceward with `sym`, preserving
all source indices. It compiled and passed R16. The eight semantic action
families are now **8/8**.

## Generic aligned-head dispatcher: three-attempt diagnostic

The existing structural suffix recursion is parameterized by
`PointwiseRelationalHeadReplayer`. Instantiating it requires a private exhaustive
all-action dispatcher. Fixed-tag actions must derive their unique tag from the
authenticated raw source action; L-Advance keeps its observed tag.

### Attempt 1: dictionary alignment and L-Begin found rewrite

The first dispatcher matched the `Fired` transition directly. This duplicated
`nameEq`/`keyEq` pattern variables even though `AlignedTransitions` already owns
the aligned dictionaries:

```text
Can't match on ?nameEq ... (Non linear pattern variable).
```

The L-Begin tag producer also needed `rewrite found in raw` before passing the
source action to `foreignBeginPlanView`.

### Attempt 2: dispatch on aligned singleton

Each branch was changed to dispatch on
`AlignedStep action tag checked NoTransitions AlignedEnd`, letting the aligned
index own the stored dictionaries. The separate `sourceStep` pattern then unified
with the constructor-generated `Fired` term:

```text
Pattern variable sourceStep unifies with: Fired ...
Suggestion: Use the same name for both pattern variables, since they unify.
```

### Attempt 3: wildcard indexed transition

Replacing that redundant source-step variable with `_` cleared the indexed
pattern wall and reached the first O-Insert branch body. Idris consumed the final
attempt on the known erased equality-annotation ambiguity:

```text
Mismatch between: Maybe (RuleTag, SystemState ...) and Type.
... let 0 raw : applyAction ... = Just ...
```

The raw equality annotation needs parentheses, as in the retained L-Advance and
failure fixes. The same parenthesized form should be used for every fixed-tag
branch by default. This mechanical correction was **not compiled** because this
was attempt 3.

The complete `pointwiseBeginTag` and generic dispatcher were reverted. No
partial dispatcher or metavariable remains.

## Stop boundary

This stop concerns only the private all-action dispatcher used to instantiate
the already-proved generic spine recursion. The eight semantic head producers,
three seals, nonempty join, and thin L-Advance owner chain remain closed.

A fresh dispatcher budget should retain the attempt-3 representation:

- dispatch on `AlignedStep ... NoTransitions AlignedEnd`;
- wildcard the definitionally indexed source transition;
- `rewrite found in raw` for L-Begin;
- parenthesize all erased raw/tag equality annotations;
- derive fixed tags from producer-owned plan/source views;
- delegate L-Advance directly to `replayPointwiseAdvanceHead`.

## Status

- L-Advance seals/join/outer head: **closed**;
- semantic families: **8/8**;
- generic all-action head dispatcher: **STOP; fully reverted**;
- structural suffix recursion/spine: **retained but not yet instantiated**;
- whole-suffix RAR/ordinal composition: **unopened**;
- final adjacent result: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- O6 estimate: **3–15 shifts**, narrowed from **5–17** by retaining the join and
  eighth-family outer head, subject to acceptance of a fresh dispatcher budget.
