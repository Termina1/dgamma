# O6 R161 — grind-shift audit

## Scope and baseline

R161 ran on branch `cp5-thm73-scoping` from `d804cde6a76b71b77044d917a4535e53b6db80b7`.
All Idris implementation changes are confined to
`research/DGamma/CP5ConfluenceDeletionChainSpike.idr`; production `src/`,
`dgamma.ipkg`, the frozen `deletionTheoremProof`, and the LocalDiamond module
remain unchanged.  The only pre-existing untracked paths remain `paper/` and
`review-o6-body-adversarial.md` before this audit.

The shift followed R146's route B.  In particular, it did **not** convert
`NoDependentClosingEpisodeForGeneration` into the refuted raw-name-global
`NoDependentClosingEpisode`.

## Registry-eta probe and selected fold

The mandated fully instantiated selected-owner `OInsert` registry-eta probe was
run three times against the real compiler and failed three distinct ways:

1. `replace` left an unsolved, textually identical lookup constraint;
2. rewriting the producer-owned absence equation did not change `False = True`;
3. eliminating the absence equation still left `Nothing` versus the hidden
   `lookupBinding ?.registry`.

The probe was removed completely.  The authorized fallback was the exact
`MkSystemState` projection.  That projection closed selected `OInsert`; the
remaining selected retained/deleted dispatch, occurrence embeddings, boundary
construction, generation-scoped lifecycle localization, reliance exclusion,
and closed selected fold were then completed.

The resulting route-B seam includes:

- exact selected insert/retire dispatch;
- deleted registered/selected dispatch;
- a complete `SelectedEpisodeLocalReplayer`;
- interior and closing replay assembly;
- generation-scoped non-begin and begin lifecycle exclusion;
- `scopedSelectedLifecycleProvider`;
- `scopedSelectedClosedFoldFromPremises`.

The selected lifecycle provider uses occurrence-local opening/closing evidence,
transported installed traces, and the selected-unload reliance guard.  No raw
name predicate was introduced.

## Raw-predicate-free post-close seam

R161 reconstructed the post-close path on the research side rather than calling
the production functions whose signatures require the stronger raw predicate.
The checked seam now contains:

- `scopedSystemEta`;
- `scopedPostCloseForeignTables`;
- symmetric effect-state transport;
- `scopedPostCloseOutcomes`;
- `scopedRetainedForeignPostCloseLifecycle`;
- `scopedPostCloseSuffixFold`;
- `scopedDeletionResultFromSelectedFold`.

Thus the generation-scoped selected fold can now be continued through the
post-close suffix and assembled into the existing frozen `DeletionResult`
without any cast to `NoDependentClosingEpisode`.

## O9 producer-capital discovery and ruling

Opening O9 exposed a separate, type-real producer-capital boundary after the
semantic deletion seam was complete:

- `SelectedClosedEpisodeFold` and
  `RelationalNoEpisodeSuffixReplayFold` retain `GenerationReplayReady`, but
  that family permits a kept same-action replay with a different `RuleTag`;
- the public `DeletionResult` similarly retains only the generation
  subsequences and endpoint quotient;
- `DeletionProducerOperationalCapital` requires constructor-local kept-tag
  equalities; and
- `DeletionChainStep.nextPremises` requires the target
  `ReplayInvariantBundle`, including target registration discipline and the
  other recursive invariants.

These facts cannot soundly be recovered from the weaker public result types.
The supervisor ruled that the research-side fold outputs must be enriched with
parallel producer-owned certificates, following the same doctrine as R152:
producers carry constructor-bound evidence and consumers only project it.
Stopping merely to re-audit the already-characterized boundary was rejected.

The first checked surface/enrichment prefix was landed:

- `ReplayReadyRuleTagsPreserved` indexes exact tag retention by the concrete
  replay-ready value;
- `ScopedSelectedClosedEpisodeFoldOutput` adds a tag-authenticated selected
  fold surface;
- `ScopedPostCloseSuffixFoldOutput` adds the corresponding post-close surface;
- checked base, kept-prepend, and deleted-prepend constructors for the tagged
  post-close output;
- `DeletionProducerOperationalCapital` now explicitly requires before,
  episode, and after replay tag certificates.

A converter from tag-authenticated readiness to
`GenerationSubsequenceRuleTagsPreserved` exhausted 3/3 elaboration attempts on
its dependent paired-pattern boundary and was fully removed.  Its final error
required the `ReplayReadyDelete` proof and `ReplayEndsDelete` proof to share the
same dependent tail binder; the next shift should reintroduce it using a
single producer-owned elimination rather than two independently named patterns.

## Surface-revision clause map

| Former clause | R161 enriched clause | Consumer rule |
|---|---|---|
| `GenerationReplayReady` only | `GenerationReplayReady` plus `ReplayReadyRuleTagsPreserved ... ready` | project the exact retained-tag certificate |
| `SelectedClosedEpisodeFold` only | `ScopedSelectedClosedEpisodeFoldOutput` with `selectedOutputFold` and `selectedOutputTags` | do not infer tags from the public fold |
| `RelationalNoEpisodeSuffixReplayFold` only | `ScopedPostCloseSuffixFoldOutput` with `postCloseOutputFold` and `postCloseOutputTags` | do not infer tags from the public fold |
| capital's free tag certificates | capital now also owns the three concrete ready-indexed certificates | derive subsequence/whole tag facts from producer output |
| target invariants reconstructed by O9 | pending fold-output retention of registration discipline / `ReplayInvariantBundle` | O9 must project, not reconstruct from an under-specified subsequence |

## Micro-unit ledger

All successful implementation units were checked before commit.  The complete
R161 implementation series is 80 commits from `a877281` through `0341d4d`.
The main grouped ledger is:

| Unit | Attempts | Commit/range | Outcome |
|---|---:|---|---|
| fully instantiated registry-eta probe | 3/3 | — | failed; fully removed |
| exact `MkSystemState` fallback and selected `OInsert` | incremental | `a877281`–`c6957bd` | passed |
| selected retained/deleted dispatch and local replayer | incremental | `837feda`–`1b261da` | passed |
| interior premises, embeddings, and selected closed fold | incremental | `aa96024`–`c7f8471` | passed |
| scoped lifecycle localization/exclusion/provider | incremental | `6725b35`–`a80b16e` | passed |
| whole embedding and selected fold from premises | incremental | `6067a92`–`4cde73f` | passed |
| post-close eta/tables/outcomes | incremental | `aa490c8`–`f7f93f7` | passed |
| retained foreign post-close lifecycle | 2/2 | `2e018bb` | passed after direct imports |
| scoped post-close suffix fold | 3/3 | `5e9f816` | passed after local private-helper copies/imports |
| scoped `DeletionResult` assembler | 3/3 | `90dab56` | passed after local private-helper copies/imports |
| replay tag family | 1/1 | `108988b` | passed |
| tagged selected output surface | 2/2 | `df03f17` | passed |
| tagged post-close output surface | 1/1 | `572d1ed` | passed |
| tagged post-close base | 1/1 | `d0492ae` | passed |
| tagged kept prepend | 2/2 | `010e062` | passed after inlining the opaque fold constructor |
| tagged deleted prepend | 1/1 | `1d4d5e9` | passed |
| tag-authenticated deletion capital surface | 1/1 | `0341d4d` | passed |
| readiness-to-subsequence tag converter | 3/3 | — | stopped; fully removed |
| `with`-free rewrite of two copied tag helpers | 1/3 | — | failed; fully removed |
| O9 `enrichDeletionChainStepSpike` | 0/3 | — | not opened pending producer enrichment |
| O10 `deleteClosingEpisodesCoreSpike` | 0/3 | — | not opened; depends on O9 |
| O11 `assembleClosingFreeAccountingSpike` | 0/3 | — | not opened; depends on O10 |

## Fresh checks and frozen invariants

Fresh orphan cleanup preceded compiler invocations.  The final retained source
produced:

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
  idris2 --build dgamma.ipkg
  exit 0

src/DGamma/CP3.idr blob:
  2c697e532e83989de8591fa6a4378747c6a501c0

dgamma.ipkg blob:
  da0c007ee08c4648e459296eb6f0e72a40e2ac89

DeletionChain research blob:
  82e65d428fec2f6b6b345a5a2c22d8d43da14f2f

production diff from 34b21c9 over src/ + dgamma.ipkg:
  empty (git diff --quiet exit 0)

LocalDiamond diff from R161 start d804cde:
  empty (git diff --quiet exit 0)
```

`git diff --check` passes.  The research hole census remains 10:
CanonicalSort 2 / CrossTrace 4 / DeletionChain 3 / LocalDiamond 0 /
RenamingComposition 1.  The three DeletionChain holes remain exactly O9, O10,
and O11.

No `believe_me`, `assert_total`, postulate, partiality marker, or
`NoDependentClosingEpisode` cast was added.  The copied production post-close
fold currently retains five `with` occurrences (two small tag-classification
helpers and the fold's two decision splits).  A direct case-expression rewrite
was attempted and removed after it lost the proof equations supplied by
`with ... proof`.  This is explicitly recorded as remaining cleanup debt; it
is not hidden as a compliant no-`with` result.  The next implementation should
replace these with producer-owned decision views before the final R161 gate.

## Gate verdict

**SAFE PARTIAL GATE at committed HEAD `0341d4d`.**  The route-B semantic seam is
a landmark advance: selected folding, raw-predicate-free post-close folding,
and frozen `DeletionResult` assembly all typecheck.  O9 was deliberately not
started because its newly exposed RuleTag and recursive-invariant obligations
are not derivable from the old fold surfaces.  The authorized producer-owned
enrichment series has begun and is checked at every retained commit, but is not
complete; therefore O9/O10/O11 do not yet receive their final 3/3 passing
checks.

Next shift: finish tagged selected/post-close producers, add fold-output
registration-discipline and target replay-invariant retention, repair the
readiness-to-subsequence converter with one dependent elimination, remove the
five copied `with` blocks via explicit decision views, then fill O9 and run its
fresh 3/3 gate before opening O10 and O11.
