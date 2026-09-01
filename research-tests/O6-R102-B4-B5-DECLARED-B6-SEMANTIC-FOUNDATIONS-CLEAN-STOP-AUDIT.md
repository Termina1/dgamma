# O6 revision 102: B4/B5 declared; B6 semantic foundations retained

## Scope

Grind shift #110 (overall #164) resumed from accepted HEAD `2491286` and
stopped at clean committed HEAD before opening the final B6 dependent dispatcher
assembly. No exhausted or partial unit remains.

Completed:

1. producer-owned four-head package;
2. final exact B4 declaration;
3. B5 presence foundations, exhaustive exact core, and final declaration;
4. both mixed same-owner semantic exclusions required by B6;
5. exact action-shape recovery and deterministic equal-owner endpoints.

Not opened: final four-way B6 record/dispatcher, pair RAR, field population, or
assembly.

## Four aligned heads

Commit `902cc8b` retains:

- `R101FourAlignedHeadViews`;
- `r101ProduceFourAlignedHeadViews`.

The package owns four explicitly typed quantity-0 `LocalAlignedHeadView` values:
source left/right and moved right/left. It also owns the four exact moved/source
action and tag equations. Construction uses nested eliminations, not inferred
local views.

Attempt 1 showed that dependent pattern aliases did not reduce record projection
fields. Attempt 2 reconstructs all four `MkLocalAlignedHeadView` values explicitly
at the outer constructor, so every equation normalizes against its exact field.
Fresh CP5 and R16 passed.

## B4 declaration

Commit `e61b011` retains:

- `R101EqualOwnerActivationIterPair`;
- `r101AlignedActionOwnersSame`;
- `r101ConsumeFourAlignedHeadViews`;
- `r101ClassifyEqualOwnerActivationPair`.

The consumer eliminates the four-head package once, gives every dependent local
an explicit quantity-0 type, transports source and moved checked transitions to
one exact action/tag representation, and invokes frozen
`r100ExactTwoOrderActivationTags`. The result owns both source and moved
activation witnesses and exact source L-Iter tag equalities.

Attempt 1 failed only because a local field name shadowed the global
`movedRight` projection. Attempt 2 renamed it `movedRightHead` and passed.

**B4 is declared and fully checked.**

## B5 presence classifier

Commit `e0b97ab` retains exact projections for:

- checked O-Insert source absence;
- checked O-Retire source presence;
- checked O-Remove source presence and output absence.

Attempt 1 exposed missing parenthesized propositions and under-specified
`lookupFiber` parameters. Attempt 2 made all lookup type parameters explicit and
passed.

Commit `e123c80` retains `r101ExactTwoOrderOrchestrationTags`. It checks all nine
orchestration cells using the two execution orders:

- Insert/Insert is excluded by producer-owned candidate distinctness;
- Insert against Retire/Remove and their reverse orientations compare source
  absence with source presence;
- Remove/Retire, Retire/Remove, and Remove/Remove compare post-Remove absence
  with the next checked source presence;
- only Retire/Retire returns exact O-Retire tag equalities.

Attempt 1 had one reversed actor equality; attempt 2 corrected it and passed.

Commit `8f19d29` retains:

- `R101EqualOwnerOrchestrationRetirePair`;
- exact aligned insert-distinct transport;
- the one-elimination four-head consumer;
- `r101ClassifyEqualOwnerOrchestrationPair`.

It passed on attempt 1.

**B5 is declared and fully checked.**

## B6 semantic foundations

Commit `06313b9` retains exact paper-activation source presence and output
presence projections. Advance source lookup is transported through the
constructor-owned source-state equality. Attempt 1 exposed an opaque
`before@(MkSystemState ...)` alias; attempt 2 matches the state directly and
passes.

Commits `daf4d36` and `303c4c2` retain the exact same-owner mixed exclusions:

- activation then orchestration;
- orchestration then activation.

Both pass on attempt 1. Insert is excluded by activation output presence versus
checked insertion absence. Retire is excluded by the retained
retire-then-activation theorem in the applicable order. Remove is excluded by
post-remove absence versus the later activation source presence.

Commit `0a1ec42` retains `R101IterActionView`, `R101RetireActionView`, and exact
action-shape producers. The first attempt used incomplete generic witness
indices; the second exposed those indices and an unparenthesized local equality;
the third uses fully explicit checked transitions and passes. These packages
recover exact L-Advance and O-Retire action forms from the classifier tag
outputs without assuming that generic witness fields refine opaquely.

Commit `540efd5` retains `r101SameCheckedPairEndpoints`. Given exact source
action/tag equality and the four-head package, it proves:

```idris
(swappedMiddle diamond = middle,
 swappedFinal diamond = originalFinal)
```

It transports the moved-right checked equation to the source-left action/tag,
uses projected raw determinism for the intermediate endpoint, reindexes the
moved-left source state, and repeats raw determinism at the final endpoint.

Attempts:

1. unparenthesized dependent local equality;
2. mistakenly supplied checked equations to raw `applyActionDeterministic`;
3. projected both checked equations first and passed.

## Clean stopping boundary

The remaining B6 unit is now mechanical but dependent and should begin with a
fresh context and fresh budget. It must:

1. eliminate `CandidateRegistrationSwapSafety`;
2. AA: call the declared B4 classifier;
3. OO: call the declared B5 classifier;
4. AO/OA: transport the four exact heads and call the retained mixed exclusion;
5. recover source action equality with the exact Iter/Retire action views;
6. call `r101SameCheckedPairEndpoints`;
7. return one producer-owned classification carrying the exact endpoint
   equalities.

No partial B6 result type or dispatcher is retained.

## Status

- B4 declaration: **complete**;
- B5 declaration: **complete**;
- B6 semantic exclusions and endpoint determinism: **complete**;
- B6 final dispatcher: **unopened**;
- pair RAR: **unopened**;
- field 9: **retained append composition awaits pair RAR**;
- fields 10–15 population: **unopened**;
- assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

Because B4 now declares successfully, the implementation band is proposed to
re-open at **2–7 shifts** for B6 dispatcher, pair RAR/field population, assembly,
and the mandatory 19-hole review stop. This replaces the suspended 2–8 proposal.

## Manifest and isolation

```text
NO_FROZEN_SURFACE_CHANGE_REQUIRED
```

`adjacentSwapSuffixSpike` remains 1183 bytes with SHA-256
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`.
Production `src/`, `dgamma.ipkg`, CP3, revisions 19–21, and all frozen capital
remain unchanged. No new hole, escape hatch, failed unit, probe, or staged
change remains.
