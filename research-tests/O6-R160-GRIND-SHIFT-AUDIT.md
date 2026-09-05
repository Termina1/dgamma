# O6 R160 — registry-eta probe stop audit

## Coordinate, ruling, and scope

R160 began on branch `cp5-thm73-scoping` at the mandated exact HEAD
`6acf518e124bed6a4c2f0663456c5e853bddb2ff`.  The tracked tree was clean; the
only initial untracked paths were the permitted `paper/` directory and
`review-o6-body-adversarial.md`.  They remain untouched and untracked.

`O6-R159-GRIND-SHIFT-AUDIT.md` was read first, followed by the governing
`O6-R146-STRATEGY-MEMO.md`.  The standing research-only ruling was preserved:
production `src/` and `dgamma.ipkg` were not edited, the frozen
`deletionTheoremProof` was not called, and no scoped-to-raw cast was introduced.
O14, O17, O19, and the O21 withdrawal branches were not edited.  No build
artifact or `build/` path was deleted.  Every compiler check was preceded by an
orphan-process kill, and only one Idris process ran at a time.  Fresh checks
were forced only by source timestamps.

The ordered scope required a single minimal disposable probe of the exact
`installedAt`/`MkSystemState` eta mismatch before any retained seam work.  That
probe consumed its strict 3-invocation budget, so the binding stop rule ended
the shift before any retained Idris declaration, seam assembly, or hole body
was opened.

## Unit A — disposable registry-eta probe

The probe tested candidate cure (i): avoid constructing or eliminating
`MkSystemState` entirely and state the contradiction over an abstract state's
projections:

```text
lookupFiber actor (registry state) = Nothing
installedAt actor state = True
-----------------------------------
Void
```

The probe was the only new top-level declaration admitted during its checks.
Its invocation ledger is:

1. The first Idris invocation was rejected at command-line parsing because the
   initial direct-check spelling used unsupported separate `-i` arguments.  It
   is conservatively counted against the binding invocation budget; no source
   diagnostic was obtained.
2. With the seeded package TTC root in `IDRIS2_PATH` and the correct
   `--source-dir research` spelling, elaboration reached the probe.  The checker
   rejected hidden dependent type variables in the unqualified `lookupFiber`
   occurrence.  The attempted reuse of the deliberately minimal
   `scopedFalseNotTrue` helper was also inaccessible at that underconstrained
   type boundary.
3. The signature was made zero-hidden by explicitly binding
   `name`, `key`, `world`, `error`, and `value`, and the body used a direct
   impossible equality rather than the inaccessible helper.  Idris still
   reported a hidden dependent `value` at the `lookupFiber` occurrence; because
   that proposition did not elaborate, the subsequent `rewrite` was not seen
   as an equality rewrite rule.

The probe was removed in full immediately after invocation 3.  The research
source is byte-identical to the R159 boundary; no probe declaration, temporary
file, or failed body remains.

### Probe verdict

**The projection-only cure was not semantically rejected, but it did not pass
within the authorized probe budget.**  The final diagnostic is earlier than
the original registry eta wall: it is the zero-hidden elaboration of
`lookupFiber`, not a contradiction between `registry state` and a separately
constructed registry.  A future authorized shift should not retry this
spelling unchanged.  Its first disposable declaration should fully instantiate
both observations at their use sites, including
`{name}`, `{key}`, `{value}`, `{world}`, and `{error}` on `lookupFiber` and the
corresponding explicit parameters on `installedAt`, while retaining the
abstract `state`.  If that exact projection-only spelling fails, move to the
memo's single-elimination producer-owned equation cure rather than reconstruct
`MkSystemState` in the contradiction statement.

This is an elaboration/zero-hidden boundary.  It is not structural-impossibility
evidence for route B, does not satisfy the strategy memo's semantic route-change
condition, and does not justify a production API unfreeze.

## Seam, O9/O10/O11, and hole census

The binding stop occurred before a winning contradiction helper could be
landed.  The seam therefore remains exactly at the R159 safe prefix:

- retained foreign lifecycle replay: complete;
- occurrence-local registration discipline and exact retained plan step:
  complete;
- exhaustive foreign orchestration/lifecycle retained dispatch: complete;
- selected-owner retained dispatch: stopped before its `OInsert` contradiction;
- assembled `SelectedEpisodeLocalReplayer`: not reached;
- generalized selected interior/closed fold: not reached;
- raw-free post-close lifecycle/fold: not reached.

Consequently O9 `enrichDeletionChainStepSpike`, O10
`deleteClosingEpisodesCoreSpike`, and O11
`assembleClosingFreeAccountingSpike` were not opened.  Their attempt counts are
fresh **0/3**.  Hole delta is **0** and the canonical census remains **10**:

- CanonicalSort: 2
- CrossTrace: 4
- DeletionChain: 3
- LocalDiamond: 0
- RenamingComposition: 1

The three DeletionChain holes remain exactly O9, O10, and O11 above.

## Micro-unit ledger

| Declaration / unit | Attempts | Commit | Outcome |
|---|---:|---|---|
| disposable projection-only registry-eta probe | 3/3 | — | stopped; fully removed |
| winning registry-eta helper | 0/3 | — | not reached |
| selected-owner retained dispatcher | 0/3 | — | not reached |
| assembled selected local replayer/fold | 0/3 | — | not reached |
| generalized post-close fold | 0/3 | — | not reached |
| O9 `enrichDeletionChainStepSpike` | 0/3 | — | unopened |
| O10 `deleteClosingEpisodesCoreSpike` | 0/3 | — | unopened |
| O11 `assembleClosingFreeAccountingSpike` | 0/3 | — | unopened |

No passing production declaration existed to commit.  The committed R159 seam
prefix remains the safe code boundary; this audit is the only R160 artifact.

## Fresh checks and frozen invariants

After restoring the probe completely, freshness was forced by timestamps only.
The restored source and the mandated positive/negative fixtures produced:

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

DeletionChain research blob:
  843274c893cd9933a85fe2138b15b006857a5dc4

production diff from 34b21c9 over src/ + dgamma.ipkg:
  empty (git diff --quiet exit 0)

local-diamond diff from R160 start 6acf518:
  empty (git diff --quiet exit 0)

adjacentSwapSuffixSpike full definition:
  1470 bytes
  SHA-256 2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf

adjacentSwapSuffixSpike statement prefix:
  1154 bytes
  SHA-256 3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf
```

The adjacent hashes were freshly recomputed with the frozen R128 convention.
`git diff --check` passes.  No R160 Idris delta remains, so no escape hatch,
unsafe operation, totality weakening, local alias, `with` block, nonlinear
pattern, or hidden signature was retained.  Apart from this audit before
commit, the only untracked paths are the permitted initial artifacts.

## Gate verdict

**STOP in Unit A after the mandated disposable registry-eta probe exhausted
3/3 invocations.**  The safe R159 seam prefix remains intact.  O9/O10/O11 retain
fresh attempt budgets and the 10-hole census is unchanged.  R160 records an
elaboration-only stop and does not authorize a semantic route change or an
owner-level production unfreeze request.
