# O6 revision 103: B6 equality-helper elaboration STOP-AUDIT

## Scope

Grind shift #111 (overall #165) resumed from accepted HEAD `62f064f`. The first
B6 dispatcher dependency was opened under its independent three-attempt budget:
a top-level helper recovering exact source action/tag equality from the retained
B4 Iter/Iter classification. All three fresh attempts failed at progressively
narrower elaboration boundaries. Per the permanent stop rule, the entire helper
was removed. No final dispatcher, pair RAR, field, or assembly work was opened.

## Attempted statement

The removed helper consumed:

- explicit `name/key/world/error/value` and fixed state indices;
- the original `left` and `right` transitions;
- `transitionActor left = transitionActor right`;
- producer-owned `R101EqualOwnerActivationIterPair`.

It returned exactly:

```idris
(transitionAction left = transitionAction right,
 transitionTag left = transitionTag right)
```

It eliminated the B4 classification once, recovered exact `LAdvance` forms with
`r101IterActionView`, derived the actor equality, and intended to compose the
two exact action equations. No package or proof was recomputed.

## Three-attempt record

### Attempt 1

The first version treated the abstract `Transition` as if it exposed a
`transitionChecked` projection. Idris correctly rejected:

```text
Undefined name transitionChecked.
```

This established that the helper must pattern-match the `Fired` constructors to
recover the stored dictionaries and checked equations.

### Attempt 2

The second version used aliased constructor patterns:

```idris
left@(Fired leftNameEq leftKeyEq leftAction leftTag leftChecked)
```

The exact views elaborated, but the alias did not reduce record-style transition
projections in the local owner equality. Idris reported the decisive mismatch:

```text
Mismatch between: right and
  Fired rightNameEq rightKeyEq rightAction rightTag rightChecked.
```

This is the same dependent alias opacity previously seen in package boundaries.

### Attempt 3

The third version removed the aliases and used only exact constructor fields.
The remaining equation was reduced to the transition-actor/action-owner bridge,
but direct assignment of `sameActor` did not unfold the opaque owner expression:

```text
Can't solve constraint between:
  case leftAction of ...
and:
  actionOwner leftAction.
```

The next mechanically indicated representation is now precise: with the
unaliasing cure retained, construct the owner equality through the existing
fully explicit top-level lemma
`transitionActorFiredActionOwner leftNameEq leftKeyEq leftAction leftTag
leftChecked` (and its right-hand counterpart), rather than relying on direct
definitional unfolding. This would be a fourth attempt and was therefore not
made.

## Stop classification

This is an **elaboration stop**, not a semantic gap:

- B4 already owns exact Iter/Iter tags and activation witnesses;
- `r101IterActionView` successfully recovers both exact L-Advance action forms;
- `sameActor` is the required actor equality;
- the sole remaining bridge is already present as
  `transitionActorFiredActionOwner`.

No new premise, frozen-surface change, dictionary identity, stage equality, or
caller-owned output capital is indicated.

## Status

- B6 final dispatcher: **unopened**;
- B6 Iter equality helper: **removed after three attempts**;
- positional pair RAR: **unopened**;
- field 9 population: **unopened**;
- fields 10–15 population: **unopened**;
- assembly/body: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

One shift of the accepted **2–7 shift** band was consumed. The nominal remainder
is **1–6 shifts**, subject to review because no new proof capital was retained.

## Manifest and isolation

```text
NO_FROZEN_SURFACE_CHANGE_REQUIRED
```

The #110 chain and all earlier capital remain byte-identical. The frozen
`adjacentSwapSuffixSpike` remains 1183 bytes with SHA-256
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`.
Production `src/`, `dgamma.ipkg`, and CP3 remain unchanged. There are no new
holes, escapes, probes, partial declarations, staged changes, or retained failed
units.
