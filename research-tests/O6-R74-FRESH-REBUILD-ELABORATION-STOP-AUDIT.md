# O6 revision 74: fresh-rebuild elaboration stop

## Scope and retained result

Grind shift #82 (overall #136) began at accepted R73 boundary `c5d27cd`.
The private classifier theorem was promoted successfully:

```idris
0 candidateSafetyExcludesParentRecovery :
  CandidateRegistrationSwapSafety left right ->
  (child, parent : name) ->
  transitionAction left = ORetire child ->
  ParentRecoveryStep parent right -> Void
```

A direct source check of the restored file proves this retained unit elaborates
from source. The R46 positive and exact negative remain permanent tracked tests.
No public or frozen declaration changed.

## Fresh-build discovery

A sequence of registration-discipline and endpoint-invariant helpers appeared
to pass `R16ConfluenceTheoremAssemblyPositive` during the shift. Those checks
produced no build output: an existing research TTC was selected through the
combined `IDRIS2_PATH`, so the changed CP5 source was not rebuilt. The mandatory
fresh suite invalidated the apparent progress immediately.

The direct fresh CP5 diagnostic exposed these classes:

1. implicit `nameEq`, `keyEq`, component, and registry binders resolved to
   existing global projections rather than fresh local indices;
2. dependent trace LHS patterns reused endpoint-indexed variables nonlinearly;
3. same-owner retirement parent-yield reconstruction required a producer-owned
   correlated package, not direct reuse of fields indexed by `retireFiber`;
4. helper declaration order placed adjacent-pair consumers before the sealed
   suffix discipline producer;
5. quietness and failure folds needed explicitly tracked membership in the
   original target registry and fully covering lifecycle-relation eliminators.

Three fresh repair checks were spent. The third still reported errors in all
five classes. Under the fresh three-attempt rule, the complete unverified body
was removed rather than retained as nominal progress.

## Rollback discipline

The working tree was restored to the accepted R73 implementation plus only the
fresh-checked classifier lemma. The following apparent milestones are therefore
**not retained**:

- suffix `NoParentRecovery` and retirement-provenance transport;
- adjacent-prefix/pair retirement transport;
- moved/pointwise parent-yield transport;
- registration-discipline field 2;
- bundle fields 3–7.

The earlier R74 audit claiming those fields closed was removed. Historical
commits from `0f876a8` through `e26b2d8` are superseded by the rollback commit and
must not be cited as checked proof capital.

## Status

- private classifier exclusion: **proved and retained**;
- parent-yield package from `9039970`: **unchanged and retained**;
- bundle field 1: **closed from the accepted boundary**;
- field 2 parent-yield sub-obligation: **closed from `9039970`**;
- field 2 retirement-provenance transport: **not retained**;
- bundle field 2 whole discipline: **blocked at elaboration engineering, with no new semantic gap found**;
- fields 3–15: **unopened at the retained HEAD**;
- final result/body: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

## Recommendation

Next shift should start from the retained source-checked boundary and use direct
source CP5 checks—not R16 alone—after every helper. The structural proof should
be rebuilt in this order:

1. explicit-index suffix recovery/provenance helpers;
2. direct fresh check and commit;
3. correlated same-owner retirement-yield packages;
4. adjacent pair/prefix provenance;
5. declaration-order-correct suffix discipline and pair discipline;
6. field 2 only after a direct fresh check;
7. fields 3–15 in record order.

The accepted **3–15** implementation band is not reduced: this shift retained
only the already-designed classifier lemma and exposed build-harness debt. The
remaining estimate stays **3–15 shifts**.

## Permanent validation protocol

R16 is now assembly evidence only. After every touched CP5 helper and before
its commit, remove that module's TTC/TTM and run a direct source check which
must visibly rebuild `DGamma.CP5ConfluenceLocalDiamondSpike`. A no-output/no-op
check is not evidence. `test-r12-harness.sh` now contains a seeded stale-TTC
regression and emits `R12_STALE_CP5_TTC_REUSE_REJECTED=passed` only when the
fresh runner removes the cached interface before the spike boundary.

## Frozen-capital audit

The retained tree preserves:

- revision-21 public surfaces and all four producers;
- `LocatedTransportedParentYield` package at `9039970`;
- joint generator, generator origin, RAR, maps, occurrences, ordinals, and
  alignments;
- 1183-byte `adjacentSwapSuffixSpike`, SHA-256
  `e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`;
- `src/`, `dgamma.ipkg`, and CP3 blob
  `2c697e532e83989de8591fa6a4378747c6a501c0`;
- no new holes or escape hatches.
