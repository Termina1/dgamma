# O6 R155 — route-B incremental continuation stop audit

## Coordinate, scope, and method

R155 began on branch `cp5-thm73-scoping` at the mandated exact HEAD
`8ec22666d738c4eef59c625c83e4bdfbb0d840ee`. The tracked tree was clean; the
only initial untracked paths were the permitted `paper/` directory and
`review-o6-body-adversarial.md`. Both remain untouched and untracked.

The shift read `O6-R154-GRIND-SHIFT-AUDIT.md` and
`O6-R153-GRIND-SHIFT-AUDIT.md` first, followed by the governing
`O6-R146-STRATEGY-MEMO.md`. All Idris edits stayed in
`research/DGamma/CP5ConfluenceDeletionChainSpike.idr`. Production `src/` and
`dgamma.ipkg` were not edited. O14, O17, O19, the O21 withdrawal branches, and
all production declarations remained frozen.

The binding incremental protocol was observed: each compiler invocation saw at
most one new top-level declaration, every successful declaration was committed
immediately, and the first declaration to exhaust its three-attempt budget was
fully reverted. An orphan-process check preceded every compiler invocation and
only one Idris process ran at a time. No build artifact or `build/` path was
deleted; fresh checks were forced only by source timestamps.

## Retained route-B capital

### Unit A — scoped right extension by transport

Commit `db11cc0` proves `extendLocatedClosingRightScoped` on attempt 1. The body
is the R154-prescribed transport: it invokes the already checked
`appendLocatedClosingEpisodeRight` and transports that result across the exact
scoped trace equation. It does not copy or retry the rejected nested
associativity body.

### Unit B(d) — exact selected-generation consumer ordinal

Commit `ff81550` proves `selectedGenerationConsumerOrdinalScoped` on attempt 1.
It composes the producer-owned foreign-prefix count equation with the selected
candidate's exact start ordinal. No ordinal is reconstructed from erased trace
identity.

Commit `2b2cbf7` proves the supporting exact occurrence locator
`locatedActionFromOccursScoped` on attempt 1. It performs one elimination of
the checked located-transition result and retains the exact action and trace
decomposition.

### Unit B(e) — inside-selected branch

Commit `3a01b81` proves `insideSelectedContradictsScopedMaximality` on attempt 3.
The checked declaration constructs the exact `LocatedActionOccurrence` for the
consumer opening, constructs `GenerationScopedClosingStart`, derives its global
ordinal through `selectedGenerationConsumerOrdinalScoped`, and spends
`NoDependentClosingEpisodeForGeneration` directly.

Attempt 1 exposed that the selected interior endpoint must be definitionally
the selected episode's `lastInstalledState`, not a free anchor state. Attempt 2
reached the located-occurrence decomposition and showed that its equality was
oriented from the selected interior to the append trace. Attempt 3 fixed that
orientation with `sym` and checked. No raw `NoDependentClosingEpisode` value was
constructed.

### Closing localization support for Unit B(f)

Commit `c51d5e3` adds the one-constructor `ScopedClosingLocalization` package on
attempt 1. Besides the localized prefix/global episodes and installed opening
segment, it retains the exact activation-to-anchor and anchor-to-first-close
factorization of the consumer interior.

Commit `46e0aa3` proves `buildScopedClosingFromOpening` on attempt 1. It consumes
one `FirstClosingResult`, constructs the installed interior with
`appendInstalledTrace`, uses the checked scoped spanning equation, and extends
the resulting prefix episode to the global trace through Unit A.

Commit `4955fc2` proves `buildScopedClosingFromOpeningResult` on attempt 1. This
single-elimination adapter consumes the exact `LastOpeningResult` and delegates
to the previous constructor.

Commit `06d2b2c` proves `localizeScopedClosing` on attempt 1. It splits aligned
execution at the installed lifecycle anchor, obtains the last opening from the
empty initial registry, and returns the exact localization package. The body
uses only top-level helpers and no local view or `let` alias.

Commit `766b082` proves `installedTraceEndScoped` on attempt 1, exposing the
installed endpoint needed for later committed-view transport.

### No-second-begin support for Unit B(f)

Commit `7c36b1e` proves `installedSourceContradictsBeginScoped` on attempt 1 by
combining the checked `L-Begin` source boundary with an installed source.

Commit `cc3d362` proves `installedTraceExcludesBeginScoped` on attempt 1. It
uses the checked occurrence split to expose the installed source at the exact
begin transition and delegates the contradiction.

Commit `0ace3d9` introduces the exact append-side occurrence family
`AppendOccurrenceScoped` on attempt 1. Commit `d217759` proves its structural
classifier `classifyAppendOccurrenceScoped` on attempt 1.

Commit `dfedfe6` proves `beginUnloadTransitionImpossibleScoped` on attempt 1;
the begin and unload singleton heads are constructor-disjoint.

Commit `2c383bf` proves `closedEpisodeExcludesBeginScoped` on attempt 1. It
classifies an alleged second begin between the installed interior and the final
unload singleton, refuting the former with installedness and the latter by rule
identity. This is the exact no-second-begin fact needed to exclude a selected
`L-Begin` from a containing installed closed interval.

No retained declaration contains a `with` block, local `let` alias, hidden
automatic telescope, `believe_me`, `assert_total`, postulate, `partial`, or
`covering` annotation. `%default total` remains in force.

## Stop micro-unit — `cancelTransitionPrefixScoped` failed 3/3

The next Unit B(f) support declaration was exact left cancellation for a common
transition prefix, needed to turn `ProviderContainsConsumer`'s two global
ordering equations into the provider closed-interior decomposition.

Its strict three-invocation budget was exhausted:

1. A direct structural clause attempted to peel the common `MoreTransitions`
   head with `case sameAppend of Refl => Refl`. Idris oriented the exposed tail
   equality in the reverse direction and rejected `rightTrace` versus
   `leftTrace`.
2. Wrapping that equality in `sym` produced the mirror rejection,
   `leftTrace` versus `rightTrace`; dependent head elimination still did not
   expose a stable tail equation.
3. The final spelling reused the checked `sharedExactPreIntervalHead` view to
   make the common head constructor-owned. Elaboration reached the view
   pattern, but Idris required a nonlinear identification between the
   constructor-owned tail pattern and the caller's explicit append tail
   (`viewForeignTail` unified with `appendTransitions ...`). That spelling is
   incompatible with the standing no-nonlinear-pattern rule and was rejected.

The complete failed declaration was restored immediately. No probe, generated
interface, failed body, or extra research file remains.

This is an elaboration stop, not the R146 semantic stop condition. No accepted
`L-Unload` was found to coexist with an installed committed consumer, and no
constructor failed to provide a required lifecycle/generation witness. The
checked no-second-begin theorem immediately preceding the stop is positive
capital for the intended before-selected contradiction. A future authorized
micro-unit should package append cancellation in a constructor-owned exact-tail
family whose constructor stores the tail equation directly, avoiding both
orientation guessing and nonlinear pattern recovery.

## Micro-unit ledger

| Declaration / surface | Attempts | Commit | Outcome |
|---|---:|---|---|
| `extendLocatedClosingRightScoped` | 1 | `db11cc0` | retained |
| `selectedGenerationConsumerOrdinalScoped` | 1 | `ff81550` | retained |
| `locatedActionFromOccursScoped` | 1 | `2b2cbf7` | retained |
| `insideSelectedContradictsScopedMaximality` | 3 | `3a01b81` | retained |
| `ScopedClosingLocalization` | 1 | `c51d5e3` | retained |
| `buildScopedClosingFromOpening` | 1 | `46e0aa3` | retained |
| `buildScopedClosingFromOpeningResult` | 1 | `4955fc2` | retained |
| `localizeScopedClosing` | 1 | `06d2b2c` | retained |
| `installedTraceEndScoped` | 1 | `766b082` | retained |
| `installedSourceContradictsBeginScoped` | 1 | `7c36b1e` | retained |
| `installedTraceExcludesBeginScoped` | 1 | `cc3d362` | retained |
| `AppendOccurrenceScoped` | 1 | `0ace3d9` | retained |
| `classifyAppendOccurrenceScoped` | 1 | `d217759` | retained |
| `beginUnloadTransitionImpossibleScoped` | 1 | `dfedfe6` | retained |
| `closedEpisodeExcludesBeginScoped` | 1 | `2c383bf` | retained |
| `cancelTransitionPrefixScoped` | 3 | — | reverted; binding stop |

## O9/O10/O11 and hole census

O9 `enrichDeletionChainStepSpike` remains stated with its original hole. The
route-B chain now contains Unit A, the complete inside-selected contradiction,
closing localization, installed endpoint lookup, append occurrence
classification, and the no-second-begin theorem. Unit B(f) stopped before the
provider containment decomposition; the final before-selected provider
exclusion and Unit B(g) `providerCandidate = False` adapter were therefore not
attempted.

The O9 chain never calls frozen `deletionTheoremProof`, and no conversion from
`NoDependentClosingEpisodeForGeneration` to raw
`NoDependentClosingEpisode` exists.

The ordered stop prevented Unit C's `enrichDeletionChainStepSpike` fill and all
attempts at Unit D `deleteClosingEpisodesCoreSpike` or Unit E
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

**STOP at the common-prefix cancellation micro-unit.** The checked committed
prefix through `closedEpisodeExcludesBeginScoped` is retained as route-B
capital. O9 is not filled; O10 and O11 are untouched. Any continuation requires
a fresh authorization and must resume with a constructor-owned exact-tail
cancellation view before completing the before-selected provider containment
contradiction.
