# O6 R154 — route-B incremental construction stop audit

## Coordinate, scope, and method

R154 began on branch `cp5-thm73-scoping` at the mandated exact HEAD
`11665f6`.  The tracked tree was clean; the only initial untracked paths were
the permitted `paper/` directory and `review-o6-body-adversarial.md`.  Both
remain untouched and untracked.

The shift read `O6-R153-GRIND-SHIFT-AUDIT.md` first and then the governing
`O6-R146-STRATEGY-MEMO.md`.  Work stayed in
`research/DGamma/CP5ConfluenceDeletionChainSpike.idr`.  Production `src/` and
`dgamma.ipkg` were not edited.  O14, O17, O19, O21 withdrawal branches, O10,
and O11 were not opened.  No `build/` directory or build artifact was deleted;
fresh seeded checks were forced only with source timestamps.  An orphan check
preceded every compiler invocation and only one Idris process ran at a time.

The R153 monolith was recovered only as decomposition guidance and split into
small declarations.  Each newly added helper was submitted alone and committed
immediately after its successful direct check.  No failed declaration remains
in the tree.

## Retained route-B capital

### Scoped start surface

Commit `1adc07a` removes the unused `scopedSelectedGeneration` and
`scopedSelectedCurrent` fields from `GenerationScopedClosingStart`.  The record
now carries only the exact selected ordinal, the selected-interval consumer
opening, and the resulting consumer ordinal.  This surface revision passed on
attempt 1.

### Producer-owned pre-interval count

Commit `a8e9584` enriches the inside constructor of
`ExactPreIntervalPrefixClassification` with the erased equation

```text
transitionCount foreignPrefix =
  transitionCount selectedPrefix + S (transitionCount selectedToForeign)
```

The head producer supplies `Refl`; recursive prefix propagation supplies
`cong S`.  Attempt 1 exposed the remaining lifecycle projection pattern which
had not bound the new constructor field.  Updating that one consumer checked on
attempt 2.

Commit `87dd79b` threads the same erased equation through
`ForeignOpeningInsideSelectedInterval` and
`exactPreIntervalToLifecycleView`.  This checked on attempt 1.  The exact count
needed to construct `scopedConsumerOrdinal` is therefore now producer-owned;
it is not reconstructed from proof equality downstream.

### Known dependency header

Commit `d04ff8d` adds the direct route-B imports for provider-frame dispatch,
ordering, and well-founded recursion.  This import-only surface checked on
attempt 1.

### Append occurrence transports

The three separately checked occurrence helpers are:

- `appendLeftOccursScoped`, commit `30aed2a`, attempt 2.  Attempt 1 used
  `absurd` without an `Uninhabited` instance; the empty indexed occurrence was
  changed to an impossible clause.
- `appendRightOccursScoped`, commit `7203021`, attempt 1.
- `transportOccursScoped`, commit `a4127fd`, attempt 1.

All three have explicit type/state telescopes and introduce no local view,
nonlinear pattern, `let`, or `with` block.

### Spanning activation/closing trace equation

Commit `3034d21` proves `scopedSpanningDecomposition` on attempt 1.  It joins an
exact opening prefix and exact first-closing suffix around a common installed
anchor, retaining the state-indexed trace equation needed to build the
localized consumer closed episode.

## Stop micro-unit — `extendLocatedClosingRightScoped` failed 3/3

The next declaration was the prefix-episode extension required before
`ScopedClosingLocalization`.  Its strict three-invocation budget was exhausted:

1. The first full-telescope spelling left the trace index named `prefix`
   implicit.  Parsing stopped at the following `located` binder.
2. Binding that trace explicitly as `(prefix : Transitions ...)` produced the
   same parser failure.  This identifies `prefix` as the problematic spelling
   at this declaration boundary rather than another unmatched delimiter in the
   preceding checked helper.
3. Renaming the trace to `prefixTrace` reached elaboration.  The copied nested
   associativity body was rejected because its final `cong` produced
   `appendTransitions (appendTransitions ... ) right` where the target was the
   right-associated trace.  The mismatch was between `right` and the expected
   post-opening suffix.

The exact third diagnostic was an equality mismatch in the final `trans` of
`extendLocatedClosingRightScoped`; parsing and dependent indices had already
succeeded.  Per the binding stop rule, the entire uncommitted declaration was
restored immediately, and no later route-B unit was attempted.

This is not a semantic route-B counterexample.  The already checked
`appendLocatedClosingEpisodeRight` earlier in the same module proves the
canonical append target.  A future authorized micro-unit should reuse that
capital and perform only the final exact-trace transport to `global`, rather
than replaying the nested associativity proof.  That is a spelling change, not
a semantic route change under the R146 condition.

## Micro-unit ledger

| Declaration / surface | Attempts | Commit | Outcome |
|---|---:|---|---|
| `GenerationScopedClosingStart` field trim | 1 | `1adc07a` | retained |
| `ExactPreIntervalPrefixClassification` count + structural producers | 2 | `a8e9584` | retained |
| `ErasedFirstLifecyclePreIntervalView` count propagation | 1 | `87dd79b` | retained |
| known route-B import header | 1 | `d04ff8d` | retained |
| `appendLeftOccursScoped` | 2 | `30aed2a` | retained |
| `appendRightOccursScoped` | 1 | `7203021` | retained |
| `transportOccursScoped` | 1 | `a4127fd` | retained |
| `scopedSpanningDecomposition` | 1 | `3034d21` | retained |
| `extendLocatedClosingRightScoped` | 3 | — | reverted; binding stop |

## O9/O10/O11 and hole census

O9 `enrichDeletionChainStepSpike` remains stated with its original hole.  Its
route-B support chain advanced through count propagation, append occurrence
transport, and the exact spanning equation, but stopped before closing
localization.  The O9 chain never calls frozen `deletionTheoremProof` and no
conversion from `NoDependentClosingEpisodeForGeneration` to
`NoDependentClosingEpisode` was introduced.

The ordered stop prevented any attempt at O10
`deleteClosingEpisodesCoreSpike` or O11
`assembleClosingFreeAccountingSpike`.

Hole delta is **0**.  The canonical census remains **10**:

- CanonicalSort: 2
- CrossTrace: 4
- DeletionChain: 3
- LocalDiamond: 0
- RenamingComposition: 1

No hole, postulate, `believe_me`, `assert_total`, `partial`/`covering`
annotation, unsafe operation, retained probe, or escape hatch was added.
`%default total` remains in force.

## Fresh gate evidence

Freshness was forced by source timestamps only; no build artifact was removed.

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

production diff from 34b21c9 over src/ + dgamma.ipkg:
  empty (0 bytes)

adjacentSwapSuffixSpike full definition:
  1470 bytes
  SHA-256 2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf

adjacentSwapSuffixSpike statement prefix:
  1154 bytes
  SHA-256 3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf
```

`git diff --check` passes.  Apart from this audit before commit, the only
untracked paths are the two permitted initial paths; there are no stray
research files.

## Gate verdict

**STOP at the prefix-episode extension micro-unit.**  The checked committed
prefix is retained as route-B capital.  O9 is not filled; O10 and O11 are
untouched.  Any continuation requires a fresh authorization and must resume
with the one-declaration transport through the already checked
`appendLocatedClosingEpisodeRight`.
