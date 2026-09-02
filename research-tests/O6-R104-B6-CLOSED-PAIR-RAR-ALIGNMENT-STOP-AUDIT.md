# O6 revision 104: B6 closes; pair-RAR aligned-check STOP-AUDIT

## Scope

Grind shift #112 (overall #166) resumed from accepted HEAD `cfd756c`. The
revision-103 owner bridge was repaired, both exact source-equality families were
retained, both aligned mixed exclusions were packaged, and the complete B6
four-way dependent dispatcher was declared. The next positional pair-RAR unit
then exhausted its independent three-attempt budget at the aligned moved-check
boundary and was removed completely. Field 9 and later units were not opened.

## Retained owner-equality cure

Commit `18b7da2` retains `r102IterPairEqualities`.

It uses unaliased exact `Fired` patterns, eliminates the producer-owned B4
classification once, recovers both exact L-Advance forms with
`r101IterActionView`, and constructs the action-owner equality only through the
existing explicit `transitionActorFiredActionOwner` lemmas. It then projects the
two exact owner equations with `cong actionOwner` and composes the L-Advance and
L-Iter equalities.

Attempt 1 reached one final opaque `actionOwner` reduction after the authorized
owner bridge. Attempt 2 replaced proof-pattern unfolding with explicit
`cong actionOwner` equations and passed fresh CP5 and R16.

Commit `a349396` retains the symmetric
`r102RetirePairEqualities`. It uses `r101RetireActionView`, the same explicit
actor/owner bridge, and composes exact O-Retire action/tag equalities. It passed
on attempt 1.

## Retained mixed aligned consumers

Commit `73e809d` retains
`r102ActivationOrchestrationSameOwnerImpossible`; commit `8cee3c2` retains
`r102OrchestrationActivationSameOwnerImpossible`.

Each helper:

- produces `R101FourAlignedHeadViews` internally;
- eliminates that package once;
- gives every dependent head/check/witness an explicit quantity-0 type;
- transports moved checks through the package-owned exact cross action/tag
  equations;
- invokes the already ratified exact mixed-order impossibility theorem.

Both passed on attempt 1. No caller-owned alignment, applicability, or endpoint
capital was introduced.

## B6 dispatcher

Commit `2d464cd` retains:

- `R102EqualOwnerPairDispatch`;
- `r102DispatchEqualOwnerPair`.

The result has exactly two constructors:

1. producer-owned Iter/Iter classification, exact source action/tag equality,
   and `swappedMiddle = middle`, `swappedFinal = originalFinal`;
2. producer-owned Retire/Retire classification with the same exact equalities
   and endpoints.

The dispatcher eliminates `registrationSwapSafety diamond` once:

- A/A calls the retained B4 classifier and iterator equality helper;
- A/O and O/A call the two aligned impossibility consumers;
- O/O calls the retained B5 classifier and retirement equality helper;
- both surviving branches invoke `r101SameCheckedPairEndpoints` with a fresh
  producer-owned four-head package.

Attempt 1 was a parser failure caused by record-style parameter syntax on an
indexed `data` declaration. Attempt 2 changed it to the required explicit
colon/arrow signature and passed fresh CP5 and R16.

**B6 is complete.**

## Positional pair-RAR attempts

The removed unit stated exactly:

```idris
RelationalReplayCorrespondence name key world error value
  (MoreTransitions left (MoreTransitions right NoTransitions))
  (MoreTransitions (movedRight diamond)
    (MoreTransitions (movedLeft diamond) NoTransitions))
```

It consumed only source alignment and `R102EqualOwnerPairDispatch`. The planned
branches used `activationSingletonRAR` twice or `orchestrationSingletonRAR`
twice, then `consRelationalReplayCorrespondence`.

### Attempt 1

The source alignment pattern rebound the existing dependent `right` transition.
Idris requested the exact same dependent name:

```text
Pattern variable right unifies with Fired ...
Suggestion: Use the same name for both pattern variables.
```

### Attempt 2

The pattern spelled the second aligned transition twice, once before its fields
were introduced. Idris rejected it as a non-linear future binder:

```text
Can't match on movedLeftActionValue [no locals in scope]
(Non linear pattern variable).
```

### Attempt 3

Wildcard tail indices let both source and moved pair alignments elaborate. Both
RAR branches reached the first singleton call, but eliminating the opaque
`movedRightAction`/`movedRightTag` record projections did not reindex the
constructor-owned aligned moved check. The decisive diagnostic was:

```text
Mismatch between: movedRightTagValue and leftTag.
```

The whole pair-RAR unit was then removed as required.

## Isolated next representation

This is an aligned dependent-correlation issue, not a semantic gap. The failed
unit mixed two independent observations of the moved step:

- `movedPairAligned diamond`, which owns the exact moved checked equation;
- opaque `movedRightAction`/`movedRightTag` projections, eliminated later.

The next fresh unit must instead consume the already retained
`R101FourAlignedHeadViews` once and use its construction-owned exact cross
action/tag equations. It should derive aligned source equality from the source
projections plus the dispatch equality, explicitly transport each moved checked
equation to the corresponding source action/tag, and only then apply endpoint
reindexing and the two singleton RARs. Do not independently eliminate the opaque
diamond action/tag projections.

No frozen interface or new premise is indicated.

## Status

- owner-equality cure: **complete**;
- B6 four-way dispatcher: **complete**;
- positional pair RAR: **removed after three attempts**;
- field 9: **append composition retained; population still open**;
- fields 10–15: **foundations retained; population unopened**;
- body/assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

One shift of the accepted **1–6 shift** band was consumed while B6 closed. A
remaining **1–5 shift** band is proposed for the corrected pair RAR, field
population, body closure, and mandatory 19-hole review stop.

## Manifest and isolation

```text
NO_FROZEN_SURFACE_CHANGE_REQUIRED
```

The frozen `adjacentSwapSuffixSpike` remains 1183 bytes with SHA-256
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`.
Production `src/`, `dgamma.ipkg`, CP3, revisions 19–21, and all prior capital
remain unchanged. No new hole, escape, staged change, probe, or partial pair-RAR
surface remains.
