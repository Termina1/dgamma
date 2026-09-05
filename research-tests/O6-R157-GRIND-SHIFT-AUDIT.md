# O6 R157 — scoped provider adapter closed, O9 integration stop audit

## Coordinate, scope, and protocol

R157 began on branch `cp5-thm73-scoping` at the mandated exact HEAD
`7bcf3236a57e530c15c443866a26108989d672f2`.  The only initial untracked
artifacts were the permitted `paper/cordis-paper.pdf`,
`paper/cordis-paper.txt`, and `review-o6-body-adversarial.md`; they remain
untouched and untracked.

The shift continued the ratified route B from
`O6-R146-STRATEGY-MEMO.md`.  All retained source changes are confined to
`research/DGamma/CP5ConfluenceDeletionChainSpike.idr`.  Production `src/`,
`dgamma.ipkg`, the local-diamond spike, O14, O17, O19, and the O21 withdrawal
branches were not edited.  No build-tree deletion or from-scratch rebuild was
performed.

The incremental Idris discipline remained binding: at most one fresh
declaration was admitted per compiler invocation, every passing declaration
was seed-checked and committed immediately, an orphan-process check preceded
each invocation, and only one Idris process ran at a time.  Failed O9 bodies
and their temporary direct import were restored completely after the three
attempts were exhausted.

## Unit A — localized opening count and inside contradiction

Commit `11c4674` extends `ScopedClosingLocalization` with the non-dependent
count equality

```text
transitionCount (traceBeforeOpening localizedGlobalEpisode) =
transitionCount (traceBeforeOpening localizedPrefixEpisode)
```

and constructs it by `Refl`.  This is the precise repair prescribed by R156:
it transports only `Nat`, not two heterogeneously indexed traces.

Commit `b48756a` closes `insideScopedOpeningContradiction` on attempt 2.  The
proof builds the exact `GenerationScopedClosingStart` for the localized global
consumer episode.  Its opening occurrence is assembled inside the selected
installed interval, while the new count equality transports the consumer
ordinal from the prefix-localized episode to the global episode.  The resulting
`PrecedenceEdge` is rejected directly by
`NoDependentClosingEpisodeForGeneration`; no raw-name-global predicate is
constructed.

## Unit B — before/inside assembly and public Boolean adapter

The remaining route-B branch assembly was retained in six immediate commits:

- `f653c58` — `beforeScopedSelectedBeginOccurs` embeds the selected opening in
  the localized foreign closing episode;
- `97a002a` — `ScopedClosingLocalization` retains the exact opening-state
  equality needed to transport `resolvedProviderAt` into the prefix episode;
- `4914df0` — `beforeScopedOpeningContradiction` invokes the checked ordering
  theorem and then rejects the selected opening via the containing-provider
  exclusion proved in R156;
- `54f02dd` — `generationScopedCandidateTrueFromOpening` dispatches the
  `ForeignOpeningInsideSelectedInterval` and
  `ForeignOpeningBeforeSelectedInterval` cases to the two checked
  contradictions;
- `a1b3d8a` — `generationScopedCandidateTrueImpossible` reconstructs the exact
  opening owner fiber and discharges the `providerCandidate = True` case; and
- `4eff0b3` — `generationScopedCrossingExcludesSelected` performs the Boolean
  inspection and exports the required
  `providerCandidate @{keyEq} wanted currentSelected = False` result.

These declarations passed on their first retained spelling after the R156
surface repair, except `insideScopedOpeningContradiction`, whose second spelling
passed as recorded above.  The adapter is generation-scoped throughout.  It
neither casts the scoped predicate to `NoDependentClosingEpisode` nor contains
a retained call to `deletionTheoremProof`.

The complete R157 retained delta before this audit is 461 insertions and one
replacement in the deletion-chain research module, across eight separately
seed-checked commits.

## Unit C — O9 body exhausted at the CP4 predicate boundary

Only after the public Boolean adapter checked was the fresh
`enrichDeletionChainStepSpike` body unit opened.  It exhausted exactly three
compiler attempts and was restored to
`?enrichDeletionChainStepSpike_rhs`.

### Attempt 1/3 — public Lemma-72 interface probe

A complete application of the existing checked deletion theorem was assembled
from `chainReplayCapital` and the selected candidate.  Elaboration reached the
dependency argument and rejected the scoped premise:

```text
When unifying:
  (consumer : name) -> ... ->
  GenerationScopedClosingStart ... -> PrecedenceEdge ... -> Void
and:
  NoDependentClosingEpisode (selectedActor candidate) trace
Mismatch between: GenerationScopedClosingStart ... and PrecedenceEdge ...
```

Thus the old public result producer cannot be used as the O9 implementation.
The probe did not typecheck and no call was retained.

### Attempt 2/3 — selected-episode fold integration surface

The body was narrowed to the first concrete readiness producer,
`selectedClosedEpisodeFoldFromPremises`.  The declaration was not in scope
through the deletion-theorem import, so Idris rejected the unseeded direct
module surface as undefined.  This attempt introduced no retained import.

### Attempt 3/3 — freshly seeded selected-episode fold

The selected-episode fold module was imported directly and freshly seeded.
Elaboration then reached the fold's dependency argument and produced the same
semantic type mismatch as attempt 1: the fold requires the false raw
`NoDependentClosingEpisode`, while O9 deliberately accepts only
`NoDependentClosingEpisodeForGeneration`.

This is the binding R157 stop.  The new adapter proves the exact
`providerCandidate = False` leaf needed by foreign lifecycle replay, but the
existing CP4 selected-episode and post-close fold APIs consume the stronger raw
predicate *before* they expose the occurrence-local lifecycle anchor,
activation interval, current fibers, and dependency key required by that
adapter.  Sound continuation requires a freshly authorized generalized replay
seam parameterized by this occurrence-local provider-exclusion operation (or a
research-side duplicate of the affected selected-episode and post-close fold
path).  It must not manufacture the refuted raw predicate.  Once that seam
exists, O9 must still construct the concrete readiness/tag capital and the
finite registration-generation bijection required by
`DeletionProducerOperationalCapital`.

## Ordered stop and downstream disposition

The strict three-attempt stop fired in Unit C.  Consequently:

- O9 `enrichDeletionChainStepSpike` remains unfilled;
- O10 `deleteClosingEpisodesCoreSpike` received 0/3 attempts; and
- O11 `assembleClosingFreeAccountingSpike` received 0/3 attempts.

The R146 semantic route-change condition did **not** fire.  No checked branch
admitted a selected `LUnload` while an installed committed consumer remained,
and no generation-scoped premise was refuted.  The stop is an integration/API
boundary between the repaired predicate and the frozen CP4 fold, not a
counterexample to route B.

The hole delta is zero.  The canonical census remains **10**:

- CanonicalSort: 2
- CrossTrace: 4
- DeletionChain: 3
- LocalDiamond: 0
- RenamingComposition: 1

No new hole, postulate, `believe_me`, `assert_total`, unsafe operation,
`partial`/`covering` annotation, retained local `let`, retained `with` block, or
hidden signature was introduced.  `%default total` remains in force.

## Fresh seeded checks and frozen invariants

After restoring the failed O9 body and temporary import, the following checks
were forced fresh without deleting the build tree:

```text
Idris 2, version 0.8.0

DeletionChain direct check:
  2/2: Building DGamma.CP5ConfluenceDeletionChainSpike
  exit 0

R11DeletionCertificateProjectionPositive:
  1/1: Building DGamma.R11DeletionCertificateProjectionPositive
  exit 0

R11DirectDeletionStepCloneNegative:
  compiler exit 1
  intended diagnostics present:
    cloneDeletionStepWithAlternateMap
    occurrences and alternate

seeded production package closure:
  169/207: Building DGamma.CP4DeletionSelectedEpisodeFold
  207/207: Building DGamma.CP4ProgressProof
  exit 0

src/DGamma/CP3.idr blob:
  2c697e532e83989de8591fa6a4378747c6a501c0

dgamma.ipkg blob:
  da0c007ee08c4648e459296eb6f0e72a40e2ac89

production diff from 34b21c9 over src/ + dgamma.ipkg:
  empty (git diff --quiet exit 0)

local-diamond diff from R157 start 7bcf323:
  empty (git diff --quiet exit 0)

DeletionChain research blob before this audit:
  5c61d42ca6021815cdcc3b63104acd1e8d533375

adjacentSwapSuffixSpike full definition:
  1470 bytes
  SHA-256 2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf

adjacentSwapSuffixSpike statement prefix:
  1154 bytes
  SHA-256 3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf
```

The adjacent hashes use the frozen R128 byte convention.  `git diff --check`
passes, and the escape-hatch scan is empty.  Apart from this audit before
commit, the only untracked paths are the three permitted initial artifacts.

## Gate verdict

**STOP at O9 after completing the generation-scoped inside/before proof and
public provider-candidate adapter.**  Route-B Unit A and Unit B are now closed
and retained.  The first O9 consumer cannot accept that adapter through the
frozen CP4 API because it still demands the refuted raw-name-global predicate.
O10 and O11 were correctly not opened.  Continuation requires authorization
for a scoped provider-exclusion replay/fold seam before O9 receives another
body budget.
