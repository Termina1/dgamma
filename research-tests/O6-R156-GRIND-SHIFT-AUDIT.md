# O6 R156 — route-B incremental continuation stop audit

## Coordinate, scope, and method

R156 began on branch `cp5-thm73-scoping` at the mandated exact HEAD
`5989830ac2dd6b9da1078cb873a1602c67998293`. The tracked tree was clean; the
only initial untracked paths were the permitted `paper/` directory and
`review-o6-body-adversarial.md`. Both remain untouched and untracked.

The shift read `O6-R155-GRIND-SHIFT-AUDIT.md` and
`O6-R154-GRIND-SHIFT-AUDIT.md` first, followed by the governing
`O6-R146-STRATEGY-MEMO.md`. All Idris edits stayed in
`research/DGamma/CP5ConfluenceDeletionChainSpike.idr`. Production `src/` and
`dgamma.ipkg` were not edited. O14, O17, O19, the O21 withdrawal branches, and
all other production declarations remained frozen.

The binding incremental protocol was observed. Each compiler invocation saw at
most one new top-level declaration; every successful declaration was committed
immediately. The first declaration to exhaust its three-attempt budget was
fully reverted together with its uncommitted support-surface adjustment. An
orphan-process check preceded every compiler invocation and only one Idris
process ran at a time. No build artifact or `build/` path was deleted; fresh
checks were forced only through source timestamps.

## Retained route-B capital

### Unit A — linear common-prefix cancellation

Commit `b759d21` proves `orientTransitionHeadRightScoped` on attempt 1. It is the
dedicated one-orientation transport required by the R155 diagnosis: distinct
head names and an explicit `headEq` are retained, and only the right head is
transported.

Commit `320c95f` proves `commonTransitionPrefixInjectiveScoped` on attempt 1. It
isolates constructor injectivity for two tails under a single constructor-owned
head.

Commit `52ca4cb` proves the explicit-head cancellation step on attempt 1. Commit
`05062be` names that step `cancelTransitionHeadScoped` and lifts it structurally
to the required arbitrary-prefix theorem `cancelTransitionPrefixScoped`, also
on attempt 1. Every recursive pattern is linear; the two head occurrences are
passed as distinct arguments and related by explicit `Refl` evidence rather
than a nonlinear pattern.

### Unit B(f) — containing-provider exclusion

Commit `9f6bca9` proves `providerClosedDecompositionScoped` on attempt 1. It
combines `ProviderContainsConsumer`'s opening and closing equations, then spends
the checked common-prefix cancellation to expose the provider's exact closed
interior.

Commit `4a414d7` proves `containingProviderExcludesConsumerBeginScoped` on
attempt 2. Attempt 1 incorrectly treated erased dictionaries as explicit left
arguments. Attempt 2 kept those binders implicit and checked. The theorem embeds
the selected `L-Begin` occurrence through the consumer interval into the
containing provider interval, where `closedEpisodeExcludesBeginScoped` refutes
it.

Commit `fe19ea8` proves `missingLookupRejectsInstalledScoped` on attempt 3.
Attempts 1 and 2 exposed, respectively, missing explicit type parameters and the
opacity of `installedAt`; the checked spelling uses the public
`installedAtMissing` equation and the existing Boolean contradiction.

Commit `eac1e55` proves `installedFiberScoped` on attempt 1. It eliminates the
existing erased inspection package, rejects the missing branch through the
previous theorem, and returns the exact successful lookup witness.

### Unit B(g) — committed-opening adapter capital

Commit `c03ddc8` introduces `ScopedCommittedOpeningEvidence` on attempt 1. The
package retains precisely the opening-boundary resolution observation and its
`PrecedenceEdge`.

Commit `f220cce` proves `committedSelectionAtOpeningScoped` on attempt 3.
Attempt 1 found that the necessary provider-candidate and persistence
interfaces required direct imports. Attempt 2 then exposed the committed
snapshot's constructor-owned fiber index and a stale seeded interface. The
checked spelling directly imports and freshly seeds the known modules and
states the view lookup at `committedFiber`; it transports the current selected
provider observation backward through the installed activation without a raw
no-dependent predicate.

Commit `6a04e3e` proves `openingResolvedFromCommittedScoped` on attempt 1.
Commit `fec7d79` proves `precedenceFromOpeningResolutionScoped` on attempt 1,
using start-state well-formedness, exact provider data, and component
preservation along the installed trace. Commit `e3d0993` proves
`buildScopedCommittedOpeningEvidence` on attempt 1.

No retained declaration contains a `with` block, local `let` alias, hidden
automatic telescope, nonlinear pattern, `believe_me`, `assert_total`, postulate,
`partial`, or `covering` annotation. `%default total` remains in force. The O9
route never calls frozen `deletionTheoremProof` and does not construct or cast a
raw `NoDependentClosingEpisode` from
`NoDependentClosingEpisodeForGeneration`.

## Stop micro-unit — `insideScopedOpeningContradiction` failed 3/3

The next Unit B declaration was the exact consumer of the inside branch of
`ErasedFirstLifecyclePreIntervalView`. Its strict three-invocation budget was
exhausted:

1. The first spelling lacked the direct `CP4RecoveryModelTrace` import needed
   for `OccurrenceEmbedding`; body elaboration consequently also emitted a
   cascading accessibility diagnostic.
2. With the direct import freshly seeded, elaboration reached the consumer
   ordinal. Idris correctly distinguished
   `traceBeforeOpening (localizedPrefixEpisode localization)` from
   `traceBeforeOpening (localizedGlobalEpisode localization)`, so the prefix
   count equation could not be used at the global episode index.
3. The final spelling tried to add a trace equality between those two opening
   prefixes to `ScopedClosingLocalization`. That equality itself is not
   homogeneous: the two `LocatedClosedEpisode` values expose independently
   indexed existential `locatedPreStart` states. Constructor elaboration
   rejected the mismatch before the intended `Refl` producer could be used.

The complete failed declaration, its direct import, and the attempted record
field were restored immediately. No probe, generated interface, failed body,
or extra research file remains.

This is an elaboration/index-surface stop, not the R146 semantic stop condition.
No accepted `L-Unload` was found to coexist with an installed committed
consumer, and no lifecycle or generation constructor failed to supply the
required witness. The narrowly diagnosed continuation is to retain only the
non-dependent equation

```text
transitionCount (traceBeforeOpening localizedGlobalEpisode) =
transitionCount (traceBeforeOpening localizedPrefixEpisode)
```

in `ScopedClosingLocalization`; its checked producer should be `Refl`, and it
avoids equating traces whose source indices are only propositionally related.
That cure requires a fresh authorized micro-unit.

## Micro-unit ledger

| Declaration / surface | Attempts | Commit | Outcome |
|---|---:|---|---|
| `orientTransitionHeadRightScoped` | 1 | `b759d21` | retained |
| `commonTransitionPrefixInjectiveScoped` | 1 | `320c95f` | retained |
| explicit head cancellation step | 1 | `52ca4cb` | retained |
| `cancelTransitionPrefixScoped` lift | 1 | `05062be` | retained |
| `providerClosedDecompositionScoped` | 1 | `9f6bca9` | retained |
| `containingProviderExcludesConsumerBeginScoped` | 2 | `4a414d7` | retained |
| `missingLookupRejectsInstalledScoped` | 3 | `fe19ea8` | retained |
| `installedFiberScoped` | 1 | `eac1e55` | retained |
| `ScopedCommittedOpeningEvidence` | 1 | `c03ddc8` | retained |
| `committedSelectionAtOpeningScoped` + direct import surface | 3 | `f220cce` | retained |
| `openingResolvedFromCommittedScoped` | 1 | `6a04e3e` | retained |
| `precedenceFromOpeningResolutionScoped` | 1 | `fec7d79` | retained |
| `buildScopedCommittedOpeningEvidence` | 1 | `e3d0993` | retained |
| `insideScopedOpeningContradiction` | 3 | — | reverted; binding stop |

## O9/O10/O11 and hole census

O9 `enrichDeletionChainStepSpike` remains stated with its original hole. Unit B
advanced through exact containing-provider exclusion and committed-opening
transport but stopped before the inside/before classifier consumer and final
`providerCandidate = False` adapter were complete.

The ordered stop prevented Unit C's O9 body attempt and all attempts at Unit D
`deleteClosingEpisodesCoreSpike` or Unit E
`assembleClosingFreeAccountingSpike`.

Hole delta is **0**. The canonical census remains **10**:

- CanonicalSort: 2
- CrossTrace: 4
- DeletionChain: 3
- LocalDiamond: 0
- RenamingComposition: 1

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
  empty (git diff --quiet exit 0)

dgamma.ipkg blob (current and 34b21c9):
  da0c007ee08c4648e459296eb6f0e72a40e2ac89

DeletionChain research blob at the committed stop boundary:
  ef1069b3371d481b0a5ad181d74fa0809b396ca4

adjacentSwapSuffixSpike full definition:
  1470 bytes
  SHA-256 2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf

adjacentSwapSuffixSpike statement prefix:
  1154 bytes
  SHA-256 3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf
```

`git diff --check` passes. Apart from this audit before commit, the only
untracked paths are the two permitted initial paths; there are no stray
research files.

## Gate verdict

**STOP at the global-versus-prefix opening-count transport micro-unit.** The
checked committed prefix through `buildScopedCommittedOpeningEvidence` is
retained as route-B capital. O9 is not filled; O10 and O11 are untouched. A
future authorized continuation should add the non-dependent count equation to
`ScopedClosingLocalization`, consume the inside/before classification, and only
then attempt the generation-cast provider adapter and O9.
