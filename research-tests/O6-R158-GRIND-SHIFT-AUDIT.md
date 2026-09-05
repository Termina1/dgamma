# O6 R158 — research-side generalized fold seam stop audit

## Coordinate, ruling, and scope

R158 began on branch `cp5-thm73-scoping` at the mandated exact HEAD
`f4af8ee1dd2c3c2d415d74b6682e7402bc73c252`.  The tracked tree was clean; the
only initial untracked paths were the permitted `paper/` directory and
`review-o6-body-adversarial.md`.  Both remain untouched and untracked.

`O6-R157-GRIND-SHIFT-AUDIT.md` was read first, followed by the governing
`O6-R146-STRATEGY-MEMO.md`.  The R157 failure was treated as the necessity
witness for a research-only generalized selected-episode/post-close fold seam.
No production API change was attempted.  All retained Idris changes are in
`research/DGamma/CP5ConfluenceDeletionChainSpike.idr`; `src/` and
`dgamma.ipkg` are byte-identical to the frozen production coordinate.

The shift did not call `deletionTheoremProof` from the O9 chain and did not
construct, cast, or assume a raw `NoDependentClosingEpisode` from
`NoDependentClosingEpisodeForGeneration`.  O14, O17, O19, and the O21
withdrawal branches were not edited.  No build artifact or `build/` path was
deleted.  Every compiler invocation was preceded by an orphan-process kill,
and only one Idris process ran at a time.

## Unit A retained prefix — generalized seam surface

Four immediate commits retain the checked research-side seam prefix.

### `08da456` — occurrence-local selected lifecycle interface

`ScopedSelectedEpisodeLifecycleProvider` is the generalized analog of
production `SelectedEpisodeLifecycleAnchorProvider`.  Its callback exposes the
complete occurrence-local context before provider exclusion is consumed:

- current generation ordinal and environment;
- exact lifecycle action, checked transition, and whole-trace occurrence;
- exact interior prefix and remainder to the selected close;
- the current selected-episode replay boundary;
- concrete selected/owner plan fibers and survivor owner;
- plan/original/survivor lookup equations; and
- the owner control relation.

Only after those clauses are exposed does it ask for a dependency key and
return

```text
providerCandidate wanted leftSelected = False
```

The interface has no raw-name-global dependency premise.

### `a563254` — scoped exclusion consumption point

`scopedForeignLifecycleControlsFromExclusion` is the research analog of the
production pair
`foreignLifecycleGuardFrameFromEvidence` /
`replayForeignLifecycleControlsFromProviderEvidence`.  It consumes the direct
occurrence-local Boolean exclusion, builds
`ForeignLifecycleGuardFrame` with the already-public
`foreignLifecycleGuardFrameFromProviderExclusion`, and invokes the checked
five-rule control dispatcher.  No precedence-evidence sum is reopened and no
raw predicate is accepted.

### `3b1cf81` — exact state/control transports

`scopedSystemStateEta` and `scopedLifecycleControlTransportBefore` retain the
two exact state-index transports needed by the generalized lifecycle replay.
They are top-level, total, and single-elimination helpers.

### `32e5e9a` — extracted L-Advance outcome producer

`scopedSelectedLifecycleOutcomes` is the parameterized operational-outcome
clause used before lifecycle control consumption.  Its eight action clauses
match the production local outcome provider: `LAdvance` delegates to
`selectedForeignAdvanceOutcomeProvider`, while the other seven action shapes
produce `Unit`.  The owner lookup transport is explicit and fully typed.

All retained declarations use explicit telescopes, introduce no local `let`,
`with` block, nonlinear pattern, inferred local view, postulate, escape hatch,
or partiality annotation.  `%default total` remains in force.

## Clause-by-clause map against the frozen fold path

| Frozen production clause / consumer | R158 research-side clause | Status |
|---|---|---|
| `SelectedEpisodeLifecycleAnchorProvider.lifecycleAnchorAt` exposes local transition/boundary/fiber evidence and returns `ForeignLifecycleProviderFrameEvidence` | `ScopedSelectedEpisodeLifecycleProvider.scopedLifecycleExcludesSelectedAt` exposes the same local context and returns direct `providerCandidate = False` | **checked** |
| `lifecycleProviderFrameExcludesSelected` consumes a sum whose precedence branch needs raw `NoDependentClosingEpisode` | The scoped provider returns the Boolean leaf directly after local context exposure | **checked surface** |
| `foreignLifecycleGuardFrameFromEvidence` selects a raw-dependent evidence branch, then builds the ordered source frame | `scopedForeignLifecycleControlsFromExclusion` calls `foreignLifecycleGuardFrameFromProviderExclusion` directly | **checked** |
| `replayForeignLifecycleControlsFromProviderEvidence` dispatches after the evidence join | `scopedForeignLifecycleControlsFromExclusion` invokes `replayForeignLifecycleControlsFromFrame` after the direct scoped join | **checked** |
| local `lifecycleOutcomes` inside `retainedForeignLifecyclePreservesEpisodeBoundary` | top-level `scopedSelectedLifecycleOutcomes` with the same eight action clauses and exact L-Advance theorem | **checked** |
| survivor state eta/control transport inside retained lifecycle replay | `scopedSystemStateEta` / `scopedLifecycleControlTransportBefore` | **checked** |
| `retainedForeignLifecyclePreservesEpisodeBoundary` | `retainedForeignLifecycleFromScopedExclusion` | **attempted 3/3, reverted** |
| `selectedEpisodeLocalReplayer` generalized over the scoped provider | not opened because the preceding retained-lifecycle micro-unit exhausted its budget | **not attempted** |
| selected interior fold and `SelectedClosedEpisodeFold` assembly | not opened | **not attempted** |
| raw-free post-close lifecycle/fold and combined generalized theorem | not opened | **not attempted** |
| derivation of the old raw research fold as a corollary | not opened | **not attempted** |

This map records a strict strengthening of the integration surface rather than
a changed semantic route: occurrence-local data is now available before the
provider predicate is consumed, exactly as required by the supervisor ruling.
The complete generalized selected/post-close fold theorem was not reached.

## Binding stop micro-unit — raw-free retained lifecycle replay failed 3/3

After the checked consumption point, the next declaration was the raw-free
analog of `retainedForeignLifecyclePreservesEpisodeBoundary`.  Its body used
only the direct exclusion callback and the checked R158 helpers; it contained
no call to the frozen deletion theorem and no raw dependency predicate.  The
strict three-invocation budget was exhausted during direct import-surface
closure:

1. **Attempt 1/3.**  The compiler rejected undefined
   `ActorOutsideDeletionPlan` and `lifecycleOwnerPresent`.  The latter was
   reported undefined because its defining module's public surface could not
   yet be elaborated without the direct control-plan import.
2. **Attempt 2/3.**  After direct imports of
   `CP4DeletionControlPlan` and `CP4DeletionBoundaryLifecycleCore`, elaboration
   advanced to the next missing exported type,
   `RetainedNoEpisodeBoundaryStep`; `lifecycleOwnerPresent` was still reported
   inaccessible through the incomplete signature closure.
3. **Attempt 3/3.**  After adding the direct
   `CP4DeletionBoundaryRetained` import, elaboration advanced again to
   `ForeignRetainedEpisodeStep`; `lifecycleOwnerPresent` remained inaccessible
   while that result type was unresolved.

The full uncommitted declaration and all its uncommitted direct imports were
restored immediately after attempt 3.  No failed source or probe remains.
The next mechanically indicated import would be the module that directly
exports `ForeignRetainedEpisodeStep`, followed by a fresh accessibility check
for `lifecycleOwnerPresent`, but the binding stop prohibited trying that
spelling in R158.

This is **not** evidence that the generalized seam is structurally impossible
without production access.  The diagnostics progressed monotonically through
transitive public type dependencies and never rejected the scoped proposition,
the direct provider exclusion, or any operational constructor.  Therefore R158
does not invoke the supervisor ruling's audited-impossibility park.  It stops
under the incremental 3/3 rule with a safe committed prefix.

## Micro-unit ledger

| Declaration / surface | Attempts | Commit | Outcome |
|---|---:|---|---|
| `ScopedSelectedEpisodeLifecycleProvider` + direct import closure | 3 | `08da456` | retained |
| `scopedForeignLifecycleControlsFromExclusion` + direct replay-core import | 3 | `a563254` | retained |
| `scopedSystemStateEta` | 1 | `3b1cf81` | retained |
| `scopedLifecycleControlTransportBefore` | 1 | `3b1cf81` | retained |
| `scopedSelectedLifecycleOutcomes` + direct import closure | 3 | `32e5e9a` | retained |
| `retainedForeignLifecycleFromScopedExclusion` | 3 | — | reverted; binding stop |
| scoped selected local replayer | 0 | — | not opened |
| generalized selected fold | 0 | — | not opened |
| generalized post-close replay/fold | 0 | — | not opened |
| O9 `enrichDeletionChainStepSpike` body | 0/3 | — | not opened |
| O10 `deleteClosingEpisodesCoreSpike` body | 0/3 | — | not opened |
| O11 `assembleClosingFreeAccountingSpike` body | 0/3 | — | not opened |

Every passing declaration was checked before commit.  A micro-unit contained at
most three compiler invocations; no exhausted spelling was retried.

## O9/O10/O11 and hole census

The Unit A prerequisite stopped before a complete generalized selected/post-close
fold producer existed, so the ordered O9 body budget was never opened.  The
mandatory order consequently kept O10 and O11 unopened as well.

Hole delta is **0**.  The canonical census remains **10**:

- CanonicalSort: 2
- CrossTrace: 4
- DeletionChain: 3
- LocalDiamond: 0
- RenamingComposition: 1

The DeletionChain holes remain exactly:

- `enrichDeletionChainStepSpike`;
- `deleteClosingEpisodesCoreSpike`; and
- `assembleClosingFreeAccountingSpike`.

## Fresh checks and frozen invariants

Freshness was forced by source timestamps only.

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
  207/207: Building DGamma.CP4ProgressProof
  exit 0

src/DGamma/CP3.idr blob:
  2c697e532e83989de8591fa6a4378747c6a501c0

dgamma.ipkg blob:
  da0c007ee08c4648e459296eb6f0e72a40e2ac89

production diff from 34b21c9 over src/ + dgamma.ipkg:
  empty (git diff --quiet exit 0)

local-diamond diff from R158 start f4af8ee:
  empty (git diff --quiet exit 0)

adjacentSwapSuffixSpike full definition:
  1470 bytes
  SHA-256 2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf

adjacentSwapSuffixSpike statement prefix:
  1154 bytes
  SHA-256 3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf
```

The adjacent hashes were freshly recomputed with the frozen R128 convention.
`git diff --check` passes.  The retained R158 delta contains no
`believe_me`, `assert_total`, postulate, unsafe operation, `partial`/`covering`
annotation, local `let`, or `with` block.  Apart from this audit before commit,
the only untracked paths are the two permitted initial artifacts.

## Gate verdict

**STOP in Unit A at the raw-free retained lifecycle replay import/accessibility
micro-unit.**  R158 checked and retained the generalized occurrence-local seam,
the direct scoped-exclusion consumption point, its exact transport helpers, and
the extracted operational outcome producer.  It did not complete the selected
fold or post-close fold, and therefore correctly opened 0/3 attempts for each
of O9, O10, and O11.  The committed prefix is semantically route B and remains
entirely research-side.
