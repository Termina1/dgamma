# O6 R149 — grind-shift route-B audit

## Coordinate and scope

R149 began on branch `cp5-thm73-scoping` at the mandated exact HEAD
`0ae080c280d85acc4ef03e511aa8e713e688c2f7`.  The only initial untracked
artifacts were the permitted `paper/` directory and
`review-o6-body-adversarial.md`; both remain untouched and untracked.

The shift followed the ordered cascade in `O6-R146-STRATEGY-MEMO.md`:

1. isolate A2 (`selectedHead`/`foreignHead`), with a hard 3-attempt cap;
2. isolate A3 (`selectedInside`/`foreignAfter`), with a hard 3-attempt cap;
3. compose A1+A2+A3 only after both probes pass, with a hard 3-attempt cap;
4. continue route B in order only after composition checks;
5. stop at the first exhausted prerequisite.

No production file or package manifest was edited.  O14, O17, O19, and O21
withdrawal branches remained out of scope.

## A2 probe — producer-owned common head

The disposable `DGamma.R149SelectedForeignHeadProbe` isolated the dependent
head mismatch from R148.  Its verdict was **pass on attempt 3/3**.

1. A direct nonlinear `Refl` elimination still unified `selectedHead` with
   `foreignHead`; it reproduced the rejected R148 mechanics.
2. Retaining only a tail equality advanced elaboration but still required
   `foreignSuffix` and `selectedSuffix` to be definitionally identical.
3. `SharedExactTraceHead` made the common head producer-owned.  The producer
   eliminated the full trace equality once, transported with `replace`, and
   exposed one constructor-owned head to both consumers.  The probe then gave:

   ```text
   1/1: Building DGamma.R149SelectedForeignHeadProbe
   exit 0
   ```

The probe source and generated TTC/TTM artifacts were removed after the
verdict.

## A3 probe — explicit final index

The disposable `DGamma.R149TailFinalIndexProbe` isolated the final-state
inference failure between `selectedInside` and `foreignAfter`.  Its verdict was
**pass on attempt 1/3**.

The successful family used a producer-owned recursive spine and threaded the
common final state explicitly before the two distinct suffix proofs.  Idris no
longer had to infer the final index from independently indexed append
expressions:

```text
1/1: Building DGamma.R149TailFinalIndexProbe
exit 0
```

The probe source and generated TTC/TTM artifacts were removed after the
verdict.

## Composition — A1+A2+A3 pre-interval classifier

With both mandatory probes green, the complete classifier was reopened.  Its
verdict was **pass on attempt 2/3**.

1. The first attempt exposed nonlinear-pattern elaboration in the first-action
   helper and in consumers of the shared-head package.
2. The checked version uses single-elimination helpers, wildcarded
   constructor-owned tails, and one explicit common middle index.  The direct
   terminal check reported:

   ```text
   2/2: Building DGamma.CP5ConfluenceDeletionChainSpike
   exit 0
   ```

Commit `788caab` (`research: classify exact pre-interval openings`) retains:

- `firstTraceActionPreInterval`;
- `SharedExactPreIntervalHead` and its producer/lift;
- `ExactPreIntervalPrefixClassification`;
- the equal-position first-action/owner contradiction;
- selected-head and foreign-head classifiers;
- `ErasedFirstLifecyclePreIntervalView`; and
- `erasedFirstLifecyclePreIntervalCovering`.

The constructors own the exact prefix/suffix positional evidence.  Equal
opening positions are rejected by A1, A2 transports one shared dependent head,
and A3 threads the final state explicitly.  No proof reconstructs equality
from raw action values.

## Route B — operational occurrence fold

Composition authorized route B.  The first required producer was
`deletionStepOperationalOccurrenceFoldSpike`.

### Checked capital retained

A structural generation-subsequence occurrence producer reached a clean
boundary and was committed as `d961e62` (`research: preserve located actions
through deletion subsequences`):

- `prependGenerationSubsequenceLocatedActionOccurrence` prefixes a source
  transition to a located tail occurrence; and
- `generationSubsequenceLocatedActionOrigin` maps every exact survivor
  occurrence to its producer-owned source occurrence.

The recursion distinguishes the exact head and dependent tail using the
located prefix itself.  It never searches for an equal action, so repeated raw
registrations at different births remain distinct.  After correcting one
name collision with an older later helper, the retained producer passed:

```text
2/2: Building DGamma.CP5ConfluenceDeletionChainSpike
exit 0
```

### Disposable exact-ordinal probe (3/3)

A separate exact-ordinal law for that source producer was explored and fully
removed after its 3-attempt cap:

1. `cong (map S)` exposed the mismatch between the expected successor ordinal
   and the prefixed record's projected `beforeActionOccurrence` count.
2. A rewrite by the prefix-ordinal lemma did not change the projection-stuck
   target.
3. Explicit transitivity solved the kept-tail shape but the delete case left
   the opaque generic occurrence preventing reduction of
   `generationSubsequenceLocatedActionOrigin`.

This is a dependent projection mechanics boundary, not a counterexample to the
ordinal statement.

### Disposable finite-bijection producer (3/3)

The generic occurrence correspondence also requires a genuine
`RegistrationGenerationBijection`.  A finite-permutation construction was
probed and fully removed after 3/3:

1. adjacent involutive swaps, lifted tail maps, and a deleted-head rotation
   elaborated until an unavailable `funExt` in the lifted inverse proof;
2. replacing extensionality with a pointwise successor proof exposed a stuck
   reduction through the two lifted functions;
3. explicit `with` decomposition reached the same equality, now between the
   producer-owned mapped generation and the projected nested lift.

The important semantic finding is that deletion cannot use the tempting
infinite predecessor shift on `Nat`: that map is not bijective.  A sound fold
must build a *finite* permutation, rotating each deleted source ordinal into an
unused ordinal beyond the finite trace while moving retained birth ordinals to
their survivor positions.

### Hole body transcript (3/3)

With the checked segment producer available, the globally indexed body itself
was opened for its strict 3-attempt budget and restored after exhaustion.

1. Supplying the checked `beforeDeletion` occurrence producer to the whole
   correspondence failed at the segment endpoint:

   ```text
   Can't solve constraint between:
     result .survivingBeforeEnd
   and:
     result .survivingFinal.
   ```

2. The identity whole-trace correspondence was correctly rejected because
   deletion changes the final state:

   ```text
   Can't solve constraint between:
     finalState
   and:
     result .survivingFinal.
   ```

3. Supplying the checked `afterDeletion` occurrence producer exposed the
   opposite segment seam:

   ```text
   Can't solve constraint between:
     (candidate .selectedEpisode) .locatedAfter
   and:
     result .survivingEpisodeEnd.
   ```

Thus the remaining producer package is precise: (a) a dependent append-region
classifier that embeds occurrences across the before/episode/after seams,
(b) its exact global ordinal law, and (c) the finite generation-bijection fold.
The segment occurrence recursion itself is now checked and retained.

## Ordered stop and semantic disposition

`deletionStepOperationalOccurrenceFoldSpike` exhausted its body budget, so the
ordered cascade stopped immediately:

- `deletedClassificationForcesLeftScannerDiscardSpike`: **0/3**;
- `deletedClassificationForcesRightScannerDiscardSpike`: **0/3**;
- `enrichDeletionChainStepSpike`: **0/3**; and
- enrichment steps (b)–(d): not opened.

The R146 semantic stop condition did **not** fire.  No exact operational
constructor admitted a selected unload while an installed committed consumer
remained, and no checked case showed that the route-B hypotheses fail to locate
a generation.  The stop is the finite permutation plus dependent append/index
mechanics above; route B remains ratified.

## Census, restrictions, and final gate

The hole census remains **13**, split exactly as before:

- CanonicalSort: 2
- CrossTrace: 4
- DeletionChain: 6
- LocalDiamond: 0
- RenamingComposition: 1

No new hole, postulate, `believe_me`, `assert_total`, unsafe operation,
`partial`/`covering` annotation, local `let`, or `with` block was retained.
All disposable bodies and probes were removed.  `%default total` and the
quantity discipline remain unchanged.

Fresh final evidence after restoration:

```text
Idris 2, version 0.8.0
DeletionChain seeded direct check:
  2/2: Building DGamma.CP5ConfluenceDeletionChainSpike
  exit 0
seeded package closure:
  207/207: Building DGamma.CP4ProgressProof
  exit 0
src/DGamma/CP3.idr blob:
  2c697e532e83989de8591fa6a4378747c6a501c0
production diff from 34b21c9 over src/ + dgamma.ipkg:
  empty (0 bytes)
adjacentSwapSuffixSpike full definition:
  1470 bytes
  SHA-256 2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf
adjacentSwapSuffixSpike statement prefix:
  1154 bytes
  SHA-256 3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf
```

The frozen adjacent-swap definition is byte-identical to the R149 start; the
local-diamond file has no diff from `0ae080c`.  No full build-tree deletion or
from-scratch rebuild occurred.  One Idris process ran at a time throughout the
checks.
