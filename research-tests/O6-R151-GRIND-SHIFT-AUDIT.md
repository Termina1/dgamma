# O6 R151 — append seams closed, operational-tag stop audit

## Coordinate, scope, and order

R151 began on branch `cp5-thm73-scoping` at the mandated exact HEAD
`080e1ca7350042c6d36d6bf30cab8483ee9e3134`.  The only initial untracked
artifacts were the permitted `paper/cordis-paper.pdf`,
`paper/cordis-paper.txt`, and `review-o6-body-adversarial.md`; all three remain
untouched and untracked.

The shift followed the ratified route-B order from
`O6-R146-STRATEGY-MEMO.md`:

1. probe the `before | episode` append seam P1′;
2. only after P1′ passes, probe `episode | after` P2;
3. only after P2 passes, probe whole-trace recomposition P3;
4. retain the checked append and exact occurrence-origin capital;
5. open a fresh composed `deletionStepOperationalOccurrenceFoldSpike` body
   unit with its own strict three-attempt budget;
6. proceed to scanner discard and chain enrichment only if that body passes.

No production source, `dgamma.ipkg`, O14, O17, O19, or O21 withdrawal branch
was edited.  No build-tree deletion or from-scratch rebuild was performed.

## P1′ — `before | episode` append seam (pass 2/3)

The disposable `DGamma.R151BeforeEpisodeSeamProbe` checked a fully explicit,
producer-owned append occurrence classification.  Its verdict was **pass on
attempt 2/3**.

1. The first spelling correctly classified head versus tail, but the ordinal
   projection remained stuck after structurally prepending the occurrence.
2. `R151PrependedOccurrence` made the prepended occurrence and its exact
   successor-ordinal equation constructor-owned.  The same classifier then
   checked.

The probe source and generated TTC/TTM files were removed; its transcript copy
was kept outside the repository under `/tmp/dgamma-r151-probes/`.

## P2 — `episode | after` append seam (pass 1/3)

The disposable `DGamma.R151EpisodeAfterSeamProbe` reused the checked generic
append classifier at the second boundary.  Its verdict was **pass on attempt
1/3**.  No new dependent-index repair was needed.

The probe source and generated TTC/TTM files were removed; its transcript copy
was kept outside the repository under `/tmp/dgamma-r151-probes/`.

## P3 — whole survivor recomposition (pass 3/3)

The disposable `DGamma.R151WholeTraceRecompositionProbe` classified every
located action occurrence in
`appendTransitions before (appendTransitions episode after)` into its exact
before, episode, or after segment, with the required ordinal offsets.  Its
verdict was **pass on attempt 3/3**.

1. Attempt 1 reached the arithmetic proof but lacked the direct `Data.Nat`
   import for `plusAssociative`.
2. Attempt 2 supplied the import and exposed the associativity equation in the
   opposite orientation.
3. Attempt 3 reversed that equation and checked the complete three-way view.

The probe source and generated TTC/TTM files were removed; its transcript copy
was kept outside the repository under `/tmp/dgamma-r151-probes/`.

## Retained append and occurrence-origin capital

Every passing retained unit was seed-checked and committed immediately.

### Commit `3bb32d9` — append occurrence classification

`research: classify deletion append occurrences` retains 450 lines in
`CP5ConfluenceDeletionChainSpike.idr`, including:

- `DeletionLocatedAppendClassification`;
- the producer-owned head/tail packages and embeddings;
- `DeletionPrependedOccurrence` with its exact ordinal law; and
- `DeletionWholeTraceOccurrenceClassification` plus
  `deletionWholeTraceOccurrenceClassification`.

This is the checked P1′–P3 capital.  All append states, action indices,
segments, and whole occurrences are explicit constructor telescope data.

### Commit `32ce94d` — exact segment origins

`research: retain exact deletion segment origins` retains 272 lines, including:

- `GenerationSubsequenceLocatedOrigin`; and
- `generationSubsequenceLocatedOriginExact` with explicit keep, delete, and
  prefix helpers.

Its first direct helper check failed because the `kept`/`deleted` evidence used
by the recursive constructor was not present in the helper telescope.  The
second spelling threaded those values explicitly and passed.  The resulting
package owns both the exact source occurrence and the equation returned by
`generationSubsequenceSourceOrdinal`.

### Commit `6267d37` — global source gluing

`research: glue deletion segment occurrence origins` retains 541 lines,
including:

- `DeletionSourceOccurrenceAtOrdinal`;
- exact source embeddings for the before, episode, and after segments;
- `DeletionWholeOccurrenceOrigin`; and
- `deletionWholeOccurrenceOrigin`.

This unit passed on attempt 2/3.  Attempt 1 found only spelling/order defects:
three `delection...` equation-name typos, one unnamed local-occurrence binder,
and placement of the global package before
`DeletionSurvivingOrdinalEmbedding`.  The second spelling corrected those
explicit-telescope issues and passed.

The final producer classifies the survivor occurrence once, obtains its exact
segment source from the corresponding `GenerationActionSubsequence`, embeds
that source directly in the original trace through
`locatedDecomposition`, and returns the exact O9
`DeletionSurvivingOrdinalEmbedding`.  It does not search by raw action equality.

## Composed operational body (failed 3/3)

Only after P1′–P3 and the final global-origin producer had checked was the
fresh composed `deletionStepOperationalOccurrenceFoldSpike` body unit opened.
Its verdict is **failed at 3/3**.  The disposable module was
`DGamma.R151DeletionOperationalBodyProbe`; it was removed with all generated
TTC/TTM files after exhaustion.

### Attempt 1/3 — direct RuleTag field

The checked whole-origin producer was supplied under the full operational-body
telescope and its first residual generic-correspondence field was attempted by
`Refl`.  Idris rejected the dependent endpoints before it could identify the
leaf tags:

```text
Error: While processing right hand side of
r151DeletionOperationalTagAttempt1. Can't solve constraint between:
    result .survivingFinal
and:
    finalState.
exit 1
```

This showed that an opaque projection from the producer package was still too
weak for direct reflexivity, despite occurrence and ordinal gluing now being
complete.

### Attempt 2/3 — eliminate both located occurrences

A single-elimination helper unpacked `DeletionWholeOccurrenceOrigin`, the
source located occurrence, and the survivor located occurrence.  Endpoint
noise disappeared and Idris exposed the exact remaining obligation:

```text
Error: While processing right hand side of
r151TagFromWholeOriginAttempt2. When unifying:
    transitionTag ... survivorTransition
and:
    transitionTag ... sourceTransition
Mismatch between: survivorTransition and sourceTransition.
exit 1
```

The whole-origin certificate proves equal actions and exact ordinal embedding;
it does not make the two checked transitions definitionally identical.

### Attempt 3/3 — exact retained-head evidence

The final spelling isolated precisely the evidence present in a
`KeepGenerationAction` head: a source transition, a survivor transition, and
`sameAction`.  Eliminating `sameAction` still leaves two independent `RuleTag`
indices:

```text
Error: While processing right hand side of
r151KeepGenerationHeadTagAttempt3. When unifying:
    survivorTag = survivorTag
and:
    sourceTag = survivorTag
Mismatch between: survivorTag and sourceTag.
exit 1
```

This is the binding R151 boundary.  `GenerationActionSubsequence` retains
`sameAction` but no source/survivor tag equality.  The concrete CP4 replay
construction had stronger `GenerationReplayReady`/retained-boundary evidence,
but `DeletionResult` stores only the resulting subsequences.  Therefore the
next sound producer must recover or preserve the concrete retained-head replay
tag witness; action equality cannot be silently promoted to tag equality.
The independent finite generation-permutation field remains later O9 debt, but
this body budget stopped at the earlier tag field and did not reopen R149's
exhausted finite-bijection probe.

## Ordered stop and downstream disposition

Because the mandatory composed body failed 3/3, the binding stop fired before
all later route-B units:

- `deletedClassificationForcesLeftScannerDiscardSpike`: **0/3**, not opened;
- `deletedClassificationForcesRightScannerDiscardSpike`: **0/3**, not opened;
- `enrichDeletionChainStepSpike`: **0/3**, not opened; and
- enriched deletion-chain steps (b)–(d): **0/3**, not opened.

The R146 semantic route-change condition did **not** fire.  No checked case
admitted a selected `LUnload` while an installed committed consumer remained,
and no route-B generation-location hypothesis was refuted.  The stop is a
missing operational proof carrier at the O9 boundary, not evidence against the
ratified scanner-discard route.

## Holes, restrictions, and final evidence

The research-hole census remains **13**, split exactly:

- CanonicalSort: 2
- CrossTrace: 4
- DeletionChain: 6
- LocalDiamond: 0
- RenamingComposition: 1

No hole was filled or added.  No postulate, `believe_me`, `assert_total`, unsafe
operation, `partial`/`covering` annotation, retained local `let`, retained
`with` block, or hidden signature was introduced.  `%default total` and the
quantity discipline remain unchanged.

Fresh seeded final evidence after disposable-probe removal:

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
  empty (git diff --quiet exit 0)

local-diamond diff from R151 start 080e1ca:
  empty (git diff --quiet exit 0)

adjacentSwapSuffixSpike full definition:
  1470 bytes
  SHA-256 2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf

adjacentSwapSuffixSpike statement prefix:
  1154 bytes
  SHA-256 3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf
```

The frozen hashes use the R128 byte convention.  `git diff --check` passes.
Apart from this audit before commit, the only untracked paths are the three
permitted initial artifacts.  One Idris process ran at a time, with an orphan
process check before every fresh compiler invocation.

## Gate verdict

**STOP at the O9 retained-head RuleTag field after closing P1′–P3 and retaining
exact global occurrence/ordinal gluing.**  R151 added three seed-checked capital
commits, exhausted exactly 3/3 attempts in the mandatory composed body, and
opened zero downstream scanner/enrichment attempts.  Continuation requires a
freshly authorized producer that carries the concrete CP4 retained replay tag
witness into the O9 action correspondence; it must not infer tag equality from
`sameAction` alone.
