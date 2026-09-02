# O6 revision 105: pair-RAR source-check STOP-AUDIT

## Scope

Grind shift #113 (overall #167) resumed from accepted HEAD `c6f5fd0` and opened
only the positional equal-owner pair RAR under its independent three-attempt
budget. The authorized package-owned transport cure succeeded through moved
action/tag transport and endpoint reindexing. The final attempt reached the
first singleton RAR and failed only because it supplied the alignment-local
source checked proof rather than the proof stored in the unaliased source
transition constructor. The whole unit was removed. Field 9 and all later units
were not opened.

## Attempted statement

The removed helper stated exactly:

```idris
RelationalReplayCorrespondence name key world error value
  (MoreTransitions left (MoreTransitions right NoTransitions))
  (MoreTransitions (movedRight diamond)
    (MoreTransitions (movedLeft diamond) NoTransitions))
```

Its inputs were only source-pair alignment and the ratified
`R102EqualOwnerPairDispatch`.

The implementation:

1. produced and eliminated `R101FourAlignedHeadViews` exactly once;
2. derived aligned moved/source action and tag equalities from package-owned
   source projections, cross equations, and dispatch equalities;
3. transported both moved checked equations with
   `checkedActivationEquationTransport` using only package fields;
4. reindexed moved-right output with `swappedMiddle = middle`;
5. reindexed moved-left input/output with both deterministic endpoint
   equalities;
6. selected `activationSingletonRAR` twice or
   `orchestrationSingletonRAR` twice and joined them with
   `consRelationalReplayCorrespondence`.

No opaque `movedRightAction`/`movedRightTag` or moved-left diamond projection was
eliminated.

## Three-attempt record

### Attempt 1

The package proof correctly produced a transition-action equality whose left
side was the opaque actual moved transition. The local moved-alignment pattern
had independently named that action. Idris rejected the local annotation:

```text
Can't solve constraint between:
  transitionAction (diamond .movedRight)
and:
  movedRightActionValue.
```

### Attempt 2

The four equality annotations were changed to use the actual transition
projections directly:

```idris
transitionAction (movedRight diamond) = leftAction
transitionTag (movedRight diamond) = leftTag
transitionAction (movedLeft diamond) = rightAction
transitionTag (movedLeft diamond) = rightTag
```

This let package-owned action/tag elimination and both transported moved checks
elaborate. The first singleton call then showed only that the abstract source
transition alias had not reduced to the aligned `Fired` constructor:

```text
Mismatch between:
  Fired nameEq keyEq leftAction leftTag leftChecked
and:
  left
```

### Attempt 3

The source transitions were unaliased in the function left-hand side and
reconstructed as fully typed `sourceLeftStep`/`sourceRightStep` values. Both
aligned action/tag transports, both endpoint replacements, and target moved
transition reindexing remained accepted. The sole remaining mismatch was:

```text
Mismatch between: leftChecked and leftOriginalChecked.
```

Here `leftChecked` is the proof named by eliminating source alignment;
`leftOriginalChecked` is the quantity-0 checked proof stored in the unaliased
source `Fired` constructor. All dictionaries, actions, tags, states, target
transitions, package cross equations, and deterministic endpoints had already
unified.

## Isolated next representation

The next fresh unit must keep attempt 3 unchanged except at the two singleton
calls:

- use `leftOriginalChecked`, not alignment-local `leftChecked`, as the first
  source checked proof;
- use `rightOriginalChecked`, not alignment-local `rightChecked`, as the second
  source checked proof;
- pass the corresponding original action/tag constructor fields if Idris needs
  them syntactically;
- keep transported moved proofs for target checks;
- avoid preserving the let aliases in the requested RAR indices if direct exact
  constructors reduce more reliably.

This is a source proof-identity/elaboration boundary, not a semantic gap. No
proof irrelevance axiom or dictionary equality is requested: the proof already
belongs to the exact source transition indexed by the result.

A fourth attempt was not made.

## Status

- B6 dispatcher: **complete and frozen**;
- positional pair RAR: **removed after three attempts**;
- package-owned moved transport and endpoint reindex path: **checked up to the
  source stored-proof selection**;
- field 9: **append composition retained; population unopened**;
- fields 10–15: **foundations retained; population unopened**;
- body/assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

One shift of the accepted **1–5 shift** band was consumed. A nominal **1–4
shift** remainder is proposed.

## Manifest and isolation

```text
NO_FROZEN_SURFACE_CHANGE_REQUIRED
```

The frozen `adjacentSwapSuffixSpike` remains 1183 bytes with SHA-256
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`.
Production `src/`, `dgamma.ipkg`, CP3, revisions 19–21, B6, and all prior capital
remain unchanged. No new hole, escape, staged change, probe, or partial pair-RAR
surface remains.
