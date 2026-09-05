# O6 R166 — B26 cured; live enriched folds and endpoint transport checked

## Baseline, scope, and safe time gate

Started **2026-09-05 15:28:24 UTC**, on `cp5-thm73-scoping`, at exact short
HEAD **`58d3642`**. Initial status contained only permitted untracked `paper/`
and `review-o6-body-adversarial.md`; the initial process scan found no Idris
process. Idris reports **0.8.0**. `idris2 --help` verified `--source-dir <dir>`
and `--check` before the first invocation. Read R165 first, then R164, R162,
R161 and the R146 strategy memo. The extracted paper was also read in full.

All proof edits are in `research/DGamma/CP5ConfluenceDeletionChainSpike.idr`.
This audit is the only other changed file. Production `src/` and `dgamma.ipkg`
are byte-identical to `34b21c9`; LocalDiamond is unchanged. No O14/O17/O19
bodies, O21 withdrawal branches, semantic route change, raw-name-global cast,
or use of frozen `deletionTheoremProof` was added. No new `with`, let alias,
proof hole, `believe_me`, `assert_total`, postulate, or partial definition.
`%default total` remains in force.

**Safe partial time gate at proof HEAD `946203d`.** The final implementation
invocation started at **18:38:59 UTC** and passed at **18:39:45 UTC**. Gate
validation began at 18:40:52. The no-new-attempt guard starts at 18:48:24, and
the mandatory safe-gate deadline is 19:13:24 (four-hour timeout 19:28:24).
Rather than begin the remaining multi-producer totality migration with less
than nine minutes of the attempt window left, this shift entered audit and
validation at an already committed boundary. No proof attempt followed that
boundary. This is **not** a 3/3 failure stop or a structural impossibility
claim. All opened micro-units passed within budget; O9/O10/O11 remain unopened.

The producer outputs and several recursive invariant clauses are now proved,
but **there is still no final target `ReplayInvariantBundle` assembler**.
The old `scopedDeletionResultFromSelectedFold` remains the inherited untagged
adapter; the new enriched folds must still be connected to the final O9 result
and operational-capital package. In particular, `TraceComponentsTotal` is not
proved for the target. This is not called a complete deletion chain.

## Unit A — B26 cure complete

The prescribed design worked, with no fallback and no new elimination
exemption. The R165 B26 transcripts identified three distinct failed spellings:

- attempt 1: `Mismatch between: checkedEq and Refl` at the alignment constructor;
- attempt 2: the explicitly spelled firing equation again required `checkedEq`
  to unify with generated `Refl`;
- attempt 3: matching the evaluator equation at `Nothing` could not unify the
  stuck `checkedApplyAction` case-expression with `Nothing`.

The revised constructor separates two proofs of the same checked-firing
proposition:

```idris
MkScopedNamedAligned :
  -- all universes, dictionaries, action and pre-state explicitly bound
  (afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  {0 stored : (checkedApplyAction ... action before = Just (tag, afterState))} ->
  (0 checked : (checkedApplyAction ... action before = Just (tag, afterState))) ->
  ScopedNamedAligned ... action before
    (MkNamedTransition afterState tag (Fired nameEq keyEq action tag stored) Refl)
```

The ellipses above abbreviate the fully bound checked source signature; they
are documentation, not Idris declarations. The `Fired` index owns `stored`,
while `checked` is an **explicit erased constructor argument** emitted by the
producer. No equality between these proof terms is requested. In the observed
successful branch the stored proof may be generated `Refl` while the explicit
field is `checkedEq`.

`scopedNamedAlignedAt` now accepts the observed evaluator result and its
explicit equation, rewrites the firing *observation*, and supplies that
`checkedEq` field. `scopedNamedAligned` instantiates the observation with the
actual evaluator and `Refl`. Neither matches the stuck checked equation nor
assumes proof irrelevance. The `Nothing` branch uses its observed equation to
contradict a successful named firing.

### A clause map (citing R165 B26)

| Former clause | R166 clause | Consumer / status |
|---|---|---|
| `checked` both supplied field and proof term indexing `Fired` | implicit erased constructor-owned `stored` indexes `Fired`; separate explicit erased `checked` has the same proposition | Proof terms need not converge; neither checked proposition nor dictionary authentication is lost. |
| Constructor demanded `Fired ... checkedEq` after evaluator rewrite produced `Fired ... Refl` | Producer infers `stored` from the exact named-transition index and explicitly supplies `checkedEq` | `scopedNamedAlignedAt`, `137e088`, passed 1/3. |
| No successful firing-to-alignment producer | Exact successful `fireNamed` wrapper | `scopedNamedAligned`, `b678554`, passed 1/3. |
| No checked-equation consumer | Project explicit `checked` | `scopedNamedChecked`, `153d1f3`, passed 1/3. |
| No aligned-trace consumer | Project the constructor-owned stored proof into `AlignedStep` | `scopedNamedPrependAligned`, `e50d494`, passed 1/3. |

A1 surface revision `6256b77` and A2–A5 all passed **1/3**, five invocations in
five immediate commits. The former alignment surface had no consumers, so A1
had no existing consumer ripple. No second alignment micro-unit died 3/3;
the supervisor's observed-evaluator fallback was not needed. The only existing
EXEMPT-LADVANCE block is unchanged.

## Unit B — producer integration and invariant clause map

| Item | Gate status | Checked capital and remaining boundary |
|---|---|---|
| Selected retained-head tags | **COMPLETE** | `scopedPackageTaggedForeignLifecycleEpisodeStep` retains the actual raw control equation; the live owner/exclusion/lifecycle chain returns `ScopedTaggedSelectedHead`. `scopedTaggedReplayRetainedEpisodeHead` covers every action. LAdvance consumes its operational producer, not an action-only tag assumption. |
| Selected kept parent-control bridges | **COMPLETE** | `ScopedSelectedBirthsComplete`, `scopedSelectedBirthAtHead`, tail/prefix census transport, and `scopedSelectedKeptParentDistinct` use the exact registration ordinal, including raw-name reissue. `scopedSelectedParentControls` combines this exclusion with reloading-parent plan preservation and ordered foreign controls. |
| Selected interior producer | **COMPLETE** | `scopedTaggedSelectedEpisodeLocalReplayer`, `scopedSelectedInteriorFoldEnriched` (`dd6cb1d`), and `scopedSelectedInteriorEnrichedFromPremises` (`e7f9611`) build the real enriched interior output from authenticated global premises. It retains canonical ready tags, parent controls and **surviving-trace** discipline. |
| Selected closing / selected closed output | **COMPLETE** | `scopedAppendSelectedCloseFinalSame` / `TraceSame` prove that deleting the close leaves the canonical survivor unchanged. Separate tags/control/discipline append lemmas feed `scopedAssembleSelectedClosedOutput`, `scopedSelectedClosedOutputFromInterior`, and the live root `scopedSelectedClosedOutputFromPremises` (`f0748c5`). |
| Post-close producer | **COMPLETE at enriched output** | `scopedPostCloseSuffixFoldEnriched` (`00a1b30`) covers deleted steps, all foreign actions, selected O-Retire, selected O-Remove and L-Begin switches to the enriched relational fallback, and impossible selected insertion/other lifecycle cases. Every actual kept constructor retains its tag and parent-control bridge, and derives survivor discipline. |
| Relational fallback producer | **COMPLETE at enriched output** | `scopedRelationalSuffixFoldOutput` (`ed84b7c`) and its kept/deleted continuation workers. All-action tag agreement uses non-advance uniqueness plus `scopedRelatedAdvanceTagsAtOwners`, which projects the existing operational runtime-outcome producer. Parent yields survive the inactive plan and ordered controls. |
| Source discipline restriction needed by selected producer | **COMPLETE** | No-recovery and retirement provenance prefix lemmas, `scopedRegistrationStepPrefix`, `scopedRegistrationDisciplinePrefix` (`5bafd63`), and `scopedSelectedInsideDiscipline` (`f5b6d28`). A retirement outside the prefix becomes an honestly proved no-recovery prefix rather than a fictional in-prefix retirement. |
| Surviving `AlignedTransitions` | **COMPLETE for canonical ready traces** | `scopedReadyAligned` (`2540bc5`) uses constructor-owned named alignment on every kept head. Final whole-result binding/append assembly is not yet wired. |
| Surviving `TraceComponentsTotal` | **NOT COMPLETED / not opened** | Per-kept target actor table/active-total transport must still be retained or proved at the local next-boundary producers, then threaded through the folds. Tags, same actions and registration discipline alone do not supply this clause. |
| Endpoint `noFailedFibers` | **COMPLETE at canonical enriched post-close/relational endpoints** | Lifecycle/fiber/ordered-control equality; universal entry-deletion and inactive-plan preservation; `scopedRelationalBoundaryNoFailure`; `scopedReadyFinalExact`; `scopedPostCloseOutputNoFailure` (`9f2e7af`). Source-final no-failure is transported through the actual final boundary. |
| Endpoint `quiet` | **COMPLETE at canonical enriched post-close/relational endpoints** | Inactive deletion leaves every target view unchanged. Universal quiet predicates survive plans; full runtime sources and related lifecycle controls preserve quiet entries. `scopedRelationalBoundaryQuiet` (`05ea85d`) and `scopedPostCloseOutputQuiet` (`946203d`) close the exact canonical endpoint clause. |
| Final target `ReplayInvariantBundle`, whole-result producer capital, `nextPremises` | **NOT COMPLETED** | The bundle's full type is unchanged. The old public/raw result is not treated as if it already owned the new certificates. The enriched folds are not yet wired into the complete `DeletionResult` / `DeletionProducerOperationalCapital` assembler. No source-discipline substitution or weaker bundle was introduced. |

### Additional surface revisions and consumer mapping

1. **B17 (`05bb683`)** adds `selectedOutputParentControls` and
   `postCloseOutputParentControls`, indexed by the exact canonical ready
   subsequence. Selected and post-close outputs still require their surviving
   discipline fields. Post-close end/kept/deleted constructors emit the exact
   corresponding control-family constructor; kept prepend now explicitly
   accepts the kept-site parent lookup bridge. No field was dropped.
2. **B25 (`d2d54e4`)** changes the live foreign post-close lifecycle producer
   to return `ScopedTaggedPostCloseHead`. Its five pre-existing calls in the
   inherited untagged post-close path explicitly project `taggedPostCloseStep`.
   The new enriched post-close fold consumes the tagged producer, not these
   projections. This temporary coexistence is openly accounted for until the
   final whole-result assembler is migrated.
3. **B46 (`551b039`)** changes the selected foreign lifecycle owner/exclusion
   workers and `scopedForeignLifecycleRetainedHead` to the tagged selected
   output. Their five old foreign-dispatch call sites explicitly project
   `taggedSelectedHead`; the new tagged selected local replayer consumes the
   actual tagged LAdvance result. Non-advance branches have independently
   proved successful tag uniqueness. Revised workers explicitly bind their
   universe/state parameters and dependent lookup instances.
4. **B31 (`661b5fc`)** centralizes the post-close/relational kept discipline
   assembler in `scopedCertifiedPrependKept`. The relational wrapper supplies
   the locally derived tag/control fields. The selected counterpart uses the
   episode-scoped deletion predicate and its original erased retirement/fresh
   birth adapters. Both preserve the survivor-side, not source-side, clause.

The selected birth-census issue was a **missing producer connection**, not a
new public assumption or semantic obstruction: `RegisteredGenerationsDuring`
was already supplied by the selected closed root. Its second clause authenticates
exact current births. A generic selected boundary alone does not rule out a
child insertion under the selected parent; the authenticated census plus the
kept witness does. That is now derived locally. The R146 verbatim route-change
condition was not met.

## O9 / O10 / O11

| Unit | Attempts | Outcome |
|---|---:|---|
| O9 `enrichDeletionChainStepSpike` | **0/3** | Unopened: target totality and the final whole-result invariant/capital assembler remain incomplete. |
| O10 `deleteClosingEpisodesCoreSpike` | **0/3** | Unopened; depends on O9. |
| O11 `assembleClosingFreeAccountingSpike` | **0/3** | Unopened; depends on O10. |

The hole census is unchanged: **10 = CanonicalSort 2 / CrossTrace 4 /
DeletionChain 3 / LocalDiamond 0 / RenamingComposition 1**. Delta **0**.
The three deletion holes remain their original statements; no intermediate
proof obligation was hidden behind a new hole.

## Incremental protocol and test evidence

- **115 checked proof commits**, **124 implementation invocations**:
  115 passes and 9 failed spellings, all corrected within the same micro-unit.
- Git declaration-set comparison verifies **at most one new top-level
  declaration per checked commit**: 111 new declarations, and four surface-only
  commits (A1, B17, B25, B46). Every implementation invocation had the same
  one-declaration-or-surface scope; no multi-declaration probe was compiled.
- All checks were sequential. The wrapper inspected Idris runtime processes
  before each invocation and would terminate an orphan or block on another
  owned process. No orphan was encountered, no concurrent compiler was run,
  and no child/subagent worker was launched.
- Existing TTC/TTM seed was retained. **No build directory or interface file
  was deleted**, no from-scratch rebuild, no standalone proof probe module.
  Changed source naturally forced every implementation check; gate source and
  fixture mtimes were touched to force their fresh checks.
- Every successful implementation log includes its own
  `Building DGamma.CP5ConfluenceDeletionChainSpike` marker and exit 0, not a
  cached no-op. The single pre-existing `surviving` shadowing warning remains.
- No fixture was added or edited. The positive R11 projection fixture and all
  three targeted rejecting boundaries were freshly checked. The wider R11
  suite was not rerun; the complete **seeded production closure** was checked.

The common per-commit command was:

```sh
idris2 --source-dir src --source-dir research --check \
  research/DGamma/CP5ConfluenceDeletionChainSpike.idr
```

Gate commands/results (UTC):

```text
18:40:52–18:41:38  fresh DeletionChain direct check: exit 0, Building marker
18:41:38–18:41:39  R11DeletionCertificateProjectionPositive: exit 0, Building marker
18:41:48–18:41:49  R11DirectDeletionStepCloneNegative: exit 1 (expected)
18:41:49–18:41:49  R11DeletionFillerMapCertificateNegative: exit 1 (expected)
18:41:49–18:41:50  R10DeletionStepMapCloneNegative: exit 1 (expected)
18:41:50–18:42:05  idris2 --build dgamma.ipkg: exit 0 (seeded closure)
```

Fixtures used the same source flags plus `--source-dir research-tests` and
`--check research-tests/DGamma/<fixture>.idr`. Intended rejection fragments:

- `cloneDeletionStepWithAlternateMap`: `occurrences and alternate`;
- `fillerMapCannotConstructDeletionCertificate`: `generationSubsequenceSourceOrdinal`;
- `replaceDeletionStepOccurrenceMap`: `alternate and step .deletionOccurrenceCorrespondence`.

The temporary audit validator had two non-proof reporting issues, corrected
before the asserting gate report: running a script from `/tmp` picked up an
unrelated pre-existing `nt.py`, so it was rerun with Python isolated mode `-I`
without touching that file; and a whitespace-spanning `with` regex counted the
pre-existing newline-form block as well. **Same-line `with (` is 8 -> 8;
including the existing newline form is 9 -> 9.** Both prove no new block. The
prior R165 audit's lexical count of eight is not a count of all multiline forms.
These validator retries were not compiler/proof attempts and changed no source.

## Fresh-check ledger

The table below maps each micro-unit to its immediately committed checked
content. Times are successful invocation end times in UTC. `surface` means no
new top-level declaration; details are in the clause maps above.

| Unit | Declaration / surface | Attempts | Commit | Check ended (UTC) |
|---|---|---:|---|---|
| A1 | surface — separate named alignment stored and supplied firing equations | 1/3 | `6256b77` | 15:31:57 |
| A2 | `scopedNamedAlignedAt` | 1/3 | `137e088` | 15:33:19 |
| A3 | `scopedNamedAligned` | 1/3 | `b678554` | 15:34:24 |
| A4 | `scopedNamedChecked` | 1/3 | `153d1f3` | 15:35:49 |
| A5 | `scopedNamedPrependAligned` | 1/3 | `e50d494` | 15:36:55 |
| B1 | `scopedReadyAligned` | 1/3 | `2540bc5` | 15:38:27 |
| B2 | `scopedNamedRawTag` | 1/3 | `35b6b4e` | 15:44:25 |
| B3 | `scopedInsertViewTag` | 1/3 | `507c143` | 15:46:42 |
| B4 | `scopedInsertRawTag` | 1/3 | `24155ab` | 15:47:42 |
| B5 | `scopedRemoveViewTag` | 1/3 | `8bf84bf` | 15:48:38 |
| B6 | `scopedRemoveRawTag` | 1/3 | `7d29aa7` | 15:49:32 |
| B7 | `scopedNonAdvanceTagsSame` | 1/3 | `e45cdfb` | 15:51:36 |
| B8 | `scopedRelatedAdvanceTagsAtOwners` | 1/3 | `a087d87` | 15:53:25 |
| B9 | `scopedRelatedAdvanceTags` | 1/3 | `4c9af5a` | 15:54:31 |
| B10 | `scopedRelatedActionTags` | 1/3 | `7255071` | 15:55:54 |
| B11 | `scopedRelationalRetainedTagAtExact` | 1/3 | `6dbd7f9` | 15:58:04 |
| B12 | `scopedRelationalRetainedTag` | 1/3 | `f49968c` | 16:00:05 |
| B13 | `scopedParentYieldReloading` | 1/3 | `ebb7664` | 16:02:14 |
| B14 | `scopedRelationalYieldControls` | 1/3 | `df4cabc` | 16:03:56 |
| B15 | `scopedRelationalParentControls` | 1/3 | `79fa922` | 16:04:58 |
| B16 | `ScopedReadyParentControls` | 1/3 | `4f89b3e` | 16:06:56 |
| B17 | surface — retain canonical parent control bridges through enriched fold outputs | 1/3 | `05bb683` | 16:08:13 |
| B18 | `scopedRelationalPrependKept` | 2/3 | `afe6b16` | 16:12:02 |
| B19 | `scopedNoRegisteredHead` | 1/3 | `fd33b5e` | 16:13:40 |
| B20 | `scopedRelationalRetainedFoldStep` | 1/3 | `5d023d0` | 16:15:11 |
| B21 | `scopedRelationalFoldHead` | 1/3 | `0f8aee8` | 16:16:26 |
| B22 | `scopedRelationalSuffixFoldOutput` | 2/3 | `ed84b7c` | 16:18:45 |
| B23 | `ScopedTaggedPostCloseHead` | 1/3 | `5160896` | 16:22:16 |
| B24 | `scopedTagPostCloseHeadFromRaw` | 1/3 | `4083445` | 16:23:25 |
| B25 | surface — migrate live foreign post-close lifecycle producer to owned tags | 1/3 | `d2d54e4` | 16:24:36 |
| B26 | `scopedInactiveNotReloading` | 1/3 | `4b95b1f` | 16:25:51 |
| B27 | `scopedReloadingInactiveDistinct` | 1/3 | `7bc144e` | 16:26:54 |
| B28 | `scopedPostCloseYieldControls` | 1/3 | `5b3070d` | 16:28:08 |
| B29 | `scopedPostCloseParentControls` | 1/3 | `b6e8932` | 16:29:09 |
| B30 | `scopedTagPostCloseNonAdvance` | 1/3 | `d1a5790` | 16:30:55 |
| B31 | `scopedCertifiedPrependKept` | 1/3 | `661b5fc` | 16:32:33 |
| B32 | `scopedTaggedForeignPostCloseHead` | 1/3 | `37eb0ac` | 16:33:48 |
| B33 | `scopedPostCloseRetainedFoldStep` | 1/3 | `2714432` | 16:35:58 |
| B34 | `scopedTaggedSelectedPostCloseRetireAt` | 1/3 | `7b83f1c` | 16:37:52 |
| B35 | `scopedNamedActualTag` | 1/3 | `a4c47a6` | 16:39:11 |
| B36 | `scopedPostCloseSelectedRemoveFoldAt` | 1/3 | `1e497ed` | 16:40:37 |
| B37 | `scopedPostCloseSelectedBeginFoldAt` | 1/3 | `e436ef9` | 16:41:57 |
| B38 | `scopedPostCloseOwnedFoldHead` | 1/3 | `fce5ba2` | 16:44:35 |
| B39 | `scopedPostCloseSameOwnerFoldHead` | 1/3 | `4133c01` | 16:45:45 |
| B40 | `scopedPostCloseOwnerFoldHead` | 1/3 | `8403afb` | 16:46:54 |
| B41 | `scopedPostCloseFoldHead` | 1/3 | `4429828` | 16:48:09 |
| B42 | `scopedPostCloseSuffixFoldEnriched` | 1/3 | `00a1b30` | 16:49:40 |
| B43 | `ScopedTaggedSelectedHead` | 1/3 | `1165b6f` | 16:54:56 |
| B44 | `scopedTagSelectedHeadFromRaw` | 1/3 | `22d7ded` | 16:56:07 |
| B45 | `scopedPackageTaggedForeignLifecycleEpisodeStep` | 1/3 | `ef31d05` | 16:57:43 |
| B46 | surface — migrate live selected foreign lifecycle chain to tagged output | 1/3 | `551b039` | 16:59:40 |
| B47 | `scopedIsAdvanceAction` | 1/3 | `2e19d23` | 17:01:35 |
| B48 | `scopedTagSelectedNonAdvance` | 1/3 | `c53d849` | 17:02:37 |
| B49 | `scopedTaggedReplayRetainedEpisodeHead` | 1/3 | `44c6c41` | 17:04:01 |
| B50 | `ScopedSelectedBirthsComplete` | 1/3 | `259b151` | 17:06:52 |
| B51 | `scopedSelectedBirthAtHead` | 1/3 | `983d7d8` | 17:07:57 |
| B52 | `scopedSelectedBirthsTail` | 1/3 | `d60d20f` | 17:09:11 |
| B53 | `scopedSelectedKeptParentDistinct` | 1/3 | `88c368f` | 17:10:49 |
| B54 | `scopedSelectedYieldControls` | 1/3 | `e5e7f26` | 17:12:08 |
| B55 | `scopedSelectedParentControls` | 1/3 | `c972cb2` | 17:13:27 |
| B56 | `scopedNoParentRecoveryHead` | 1/3 | `4f1d237` | 17:17:09 |
| B57 | `scopedNoParentRecoveryPrefix` | 1/3 | `c40988e` | 17:18:07 |
| B58 | `scopedPrependRetirementProvenance` | 1/3 | `c936d62` | 17:19:06 |
| B59 | `scopedChildRetiresPrefixStep` | 1/3 | `87dab5a` | 17:20:10 |
| B60 | `scopedChildRetiresPrefix` | 1/3 | `3bef4b0` | 17:21:09 |
| B61 | `scopedRetirementProvenancePrefix` | 1/3 | `a0e9cc5` | 17:22:06 |
| B62 | `scopedRegistrationStepPrefix` | 1/3 | `0d71c3a` | 17:23:21 |
| B63 | `scopedRegistrationDisciplinePrefix` | 1/3 | `5bafd63` | 17:24:21 |
| B64 | `ScopedSelectedInteriorFoldOutput` | 1/3 | `aadba96` | 17:25:29 |
| B65 | `scopedPrependSelectedInteriorKeptOutput` | 1/3 | `2ac22f9` | 17:26:57 |
| B66 | `scopedPrependSelectedInteriorDeletedOutput` | 1/3 | `5dbcb8a` | 17:28:02 |
| B67 | `scopedSelectedCertifiedPrependKept` | 1/3 | `bed20e3` | 17:29:15 |
| B68 | `ScopedTaggedSelectedLocalReplayer` | 1/3 | `80831ac` | 17:30:42 |
| B69 | `scopedTaggedSelectedEpisodeLocalReplayer` | 2/3 | `82c6a1d` | 17:32:38 |
| B70 | `scopedInstalledHead` | 1/3 | `58858bf` | 17:34:11 |
| B71 | `scopedSelectedRetainedFoldStep` | 1/3 | `e7d78db` | 17:35:53 |
| B72 | `scopedSelectedInteriorFoldHead` | 1/3 | `d16f203` | 17:37:33 |
| B73 | `scopedSelectedInteriorFoldEnriched` | 1/3 | `dd6cb1d` | 17:39:51 |
| B74 | `scopedSelectedInsideDiscipline` | 1/3 | `f5b6d28` | 17:41:23 |
| B75 | `scopedSelectedBirthsPrefix` | 1/3 | `de7c69f` | 17:42:54 |
| B76 | `scopedSelectedInteriorEnrichedFromPremises` | 2/3 | `e7f9611` | 17:45:14 |
| B77 | `scopedAppendSelectedCloseFinalSame` | 1/3 | `7a9c9a0` | 17:48:20 |
| B78 | `scopedPrependTraceTransport` | 1/3 | `873f5b4` | 17:49:24 |
| B79 | `scopedAppendSelectedCloseTraceSame` | 1/3 | `8043327` | 17:50:55 |
| B80 | `scopedReadyKeptParentControls` | 1/3 | `a77aeca` | 17:52:21 |
| B81 | `scopedReadyDeletedParentControls` | 1/3 | `323d342` | 17:53:28 |
| B82 | `scopedAppendSelectedCloseParentControls` | 1/3 | `b5fdd13` | 17:54:49 |
| B83 | `scopedAppendSelectedCloseTags` | 1/3 | `5d06afe` | 17:55:58 |
| B84 | `scopedDisciplineAcrossTraceEnd` | 1/3 | `1a010dc` | 17:57:00 |
| B85 | `scopedAppendSelectedCloseDiscipline` | 1/3 | `4af765b` | 17:58:23 |
| B86 | `scopedAssembleSelectedClosedOutput` | 1/3 | `6bf1e1d` | 17:59:51 |
| B87 | `scopedSelectedClosedOutputFromInterior` | 1/3 | `1e27e60` | 18:01:18 |
| B88 | `scopedSelectedClosedOutputFromPremises` | 1/3 | `f0748c5` | 18:02:28 |
| B89 | `scopedLifecycleFibersNotFailed` | 2/3 | `0ea663b` | 18:08:37 |
| B90 | `scopedFiberControlNotFailed` | 1/3 | `a261d60` | 18:09:38 |
| B91 | `scopedOrderedControlsNoFailure` | 3/3 | `3e145cf` | 18:12:45 |
| B92 | `scopedAndRightTrue` | 1/3 | `bd09040` | 18:15:03 |
| B93 | `scopedAllDeleteHeadAt` | 2/3 | `e620035` | 18:17:22 |
| B94 | `scopedAllDeleteEntries` | 1/3 | `b53da11` | 18:18:23 |
| B95 | `scopedNoFailureDelete` | 1/3 | `ea85afb` | 18:19:31 |
| B96 | `scopedPlanNoFailure` | 2/3 | `8b7d920` | 18:21:37 |
| B97 | `scopedRelationalBoundaryNoFailure` | 1/3 | `76a9e4d` | 18:22:44 |
| B98 | `scopedReadyFinalExact` | 1/3 | `b5774ec` | 18:24:09 |
| B99 | `scopedPostCloseOutputNoFailure` | 1/3 | `9f2e7af` | 18:25:23 |
| B100 | `scopedQuietFiberTargetSame` | 1/3 | `881d08d` | 18:27:47 |
| B101 | `scopedQuietEntryInactiveDelete` | 1/3 | `40ba466` | 18:29:00 |
| B102 | `scopedAllRecursiveAsList` | 1/3 | `29bd640` | 18:30:05 |
| B103 | `scopedAllListPointwise` | 1/3 | `45330e0` | 18:31:08 |
| B104 | `scopedQuietInactiveDelete` | 1/3 | `2498384` | 18:32:36 |
| B105 | `scopedPlanQuiet` | 1/3 | `60757b6` | 18:33:43 |
| B106 | `scopedLifecycleFibersQuiet` | 1/3 | `f047d85` | 18:35:25 |
| B107 | `scopedRuntimeFiberQuiet` | 1/3 | `c1c7709` | 18:36:28 |
| B108 | `scopedOrderedControlsQuiet` | 1/3 | `4650c7f` | 18:37:37 |
| B109 | `scopedRelationalBoundaryQuiet` | 1/3 | `05ea85d` | 18:38:45 |
| B110 | `scopedPostCloseOutputQuiet` | 1/3 | `946203d` | 18:39:45 |

## Exact failed compiler diagnostics

The failed spellings below are absent from the retained source. Each was a
revision of the one in-flight declaration, not an extra untracked probe. All
units eventually passed within their original 3-attempt budgets. The repeated
pre-existing shadowing warning is omitted; error diagnostics are verbatim.

### B18 attempt 1/3

```text
Error: While processing type of scopedRelationalPrependKept. Can't bind implicit DGamma.CP5ConfluenceDeletionChainSpike.{original:210694} of type (DGamma.Calculus.SystemState name[26] key[25] value[22] world[24] error[23])

DGamma.CP5ConfluenceDeletionChainSpike:19931:1--19959:21
 19931 | ||| The kept relational producer assembles both canonical controls and survivor discipline.
 19932 | 0 scopedRelationalPrependKept :
 19933 |   (name, key, world, error : Type) -> (value : key -> Type) ->
 19934 |   (protocol : RegistrationProtocol key value world error) ->
 19935 |   (nameEq : DecEq name) -> (keyEq : DecEq key) ->
 19936 |   (registered : List (RegistrationGeneration name)) ->

Error: While processing right hand side of scopedRelationalPrependKept. DGamma.CP5ConfluenceDeletionChainSpike.scopedPrependPostCloseKeptOutput is not accessible in this context.

DGamma.CP5ConfluenceDeletionChainSpike:19963:5--19963:37
 19959 |       rest) survivor
 19960 | scopedRelationalPrependKept name key world error value protocol nameEq keyEq
 19961 |   registered ordinal live unique action tag original originalAfter originalFinal
 19962 |   survivor checked rest stepDiscipline alignedRest retained boundary named fires folded =
 19963 |     scopedPrependPostCloseKeptOutput name key world error value protocol nameEq keyEq
             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

### B22 attempt 1/3

```text
Error: While processing left hand side of scopedRelationalSuffixFoldOutput. When unifying:
    AlignedTransitions ?name ?key ?world ?error ?value ?nameEq ?keyEq NoTransitions
and:
    AlignedTransitions ?name ?key ?world ?error ?value ?nameEq ?keyEq NoTransitions
Pattern variable original unifies with: ?originalFinal [no locals in scope].

DGamma.CP5ConfluenceDeletionChainSpike:20143:45--20143:67
       |
 20143 |   registered ordinal live bornBefore unique original originalFinal survivor _
       |                                             ^^^^^^^^ ^^^^^^^^^^^^^

Suggestion: Use the same name for both pattern variables, since they unify.
```

### B69 attempt 1/3

```text
Error: No type declaration for DGamma.CP5ConfluenceDeletionChainSpike.scopedTaggedScopedTaggedSelectedLocalReplayer.

DGamma.CP5ConfluenceDeletionChainSpike:21945:1--21953:47
 21945 | scopedTaggedScopedTaggedSelectedLocalReplayer name key world error value protocol nameEq
 21946 |   keyEq selected registered global globalDiscipline independent whole
 21947 |   selectedEpisode wholeInGlobal anchors =
 21948 |     MkScopedTaggedSelectedLocalReplayer
 21949 |       (scopedReplayDeletedEpisodeHead name key world error value protocol nameEq
 21950 |         keyEq selected registered global globalDiscipline whole wholeInGlobal)
Did you mean: scopedTaggedSelectedEpisodeLocalReplayer?
```

### B76 attempt 1/3

```text
Error: While processing right hand side of scopedSelectedInteriorEnrichedFromPremises. Undefined name locatedAfterClose. 

DGamma.CP5ConfluenceDeletionChainSpike:22282:10--22282:27
 22278 |       (scopedSelectedInsideDiscipline name key world error value protocol nameEq keyEq selected global
 22279 |         discipline located)
 22280 |       (scopedSelectedBirthsPrefix name key world error value selected registered (S episodeStartOrdinal)
 22281 |         (closedStartState (locatedEpisode located)) (lastInstalledState (locatedEpisode located))
 22282 |         (locatedAfterClose located) (closedInside (locatedEpisode located))
                  ^^^^^^^^^^^^^^^^^
Did you mean: locatedAfter?
```

### B89 attempt 1/3

```text
Error: While processing right hand side of scopedLifecycleFibersNotFailed. When unifying:
    case fiberLifecycle (MkFiber component leftParent leftRetired leftTable (Inactive rightOutcome)) of
  { Inactive (Just errorValue) => False
  ; _ => True
  }
and:
    case fiberLifecycle (MkFiber component rightParent rightRetired rightTable (Inactive rightOutcome)) of
  { Inactive (Just errorValue) => False
  ; _ => True
  }
Mismatch between: leftTable and rightTable.

DGamma.CP5ConfluenceDeletionChainSpike:22854:5--22854:115
 22850 |   (fiberNotFailed (MkFiber component leftParent leftRetired leftTable leftLife) =
 22851 |     fiberNotFailed (MkFiber component rightParent rightRetired rightTable rightLife))
 22852 | scopedLifecycleFibersNotFailed name key world error value component leftParent rightParent leftRetired
 22853 |   rightRetired leftTable rightTable _ _ (InactiveControls same) =
 22854 |     cong (\outcome => fiberNotFailed (MkFiber component leftParent leftRetired leftTable (Inactive outcome))) same
             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

### B91 attempt 1/3

```text
Error: While processing type of scopedOrderedControlsNoFailure. Can't bind implicit DGamma.CP5ConfluenceDeletionChainSpike.{value:238275} of type ({arg:11033} : ?DGamma.CP5ConfluenceDeletionChainSpike.{key:238274}_[name[7], key[6], world[5], error[4], value[3], left[2], right[1], {arg:238256}[0]]) -> Type

DGamma.CP5ConfluenceDeletionChainSpike:22875:1--22879:85
 22875 | 0 scopedOrderedControlsNoFailure :
 22876 |   (name, key, world, error : Type) -> (value : key -> Type) ->
 22877 |   (left, right : List (Binding name (FiberAt name key value world error))) ->
 22878 |   OrderedRegistryControlsRelated name key world error value left right ->
 22879 |   (allList DGamma.CP3.notFailedEntry left = allList DGamma.CP3.notFailedEntry right)

Error: No type declaration for DGamma.CP5ConfluenceDeletionChainSpike.scopedOrderedControlsNoFailure.

DGamma.CP5ConfluenceDeletionChainSpike:22880:1--22880:88
 22876 |   (name, key, world, error : Type) -> (value : key -> Type) ->
 22877 |   (left, right : List (Binding name (FiberAt name key value world error))) ->
 22878 |   OrderedRegistryControlsRelated name key world error value left right ->
 22879 |   (allList DGamma.CP3.notFailedEntry left = allList DGamma.CP3.notFailedEntry right)
 22880 | scopedOrderedControlsNoFailure name key world error value _ _ OrderedControlsNil = Refl
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Did you mean: scopedFiberControlNotFailed?
```

### B91 attempt 2/3

```text
Error: While processing right hand side of scopedOrderedControlsNoFailure. Can't solve constraint between: Bool and Lazy Bool.

DGamma.CP5ConfluenceDeletionChainSpike:22886:8--22886:74
 22882 | scopedOrderedControlsNoFailure name key world error value _ _ OrderedControlsNil = Refl
 22883 | scopedOrderedControlsNoFailure name key world error value _ _
 22884 |   (OrderedControlsCons actor related rest) =
 22885 |     cong2 (&&) (scopedFiberControlNotFailed name key world error value _ _ related)
 22886 |       (scopedOrderedControlsNoFailure name key world error value _ _ rest)
                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

### B93 attempt 1/3

```text
Error: While processing right hand side of scopedAllDeleteHeadAt. Can't solve constraint between: rest and with block in deleteEntries key keyEq wanted current (Yes same) value cell rest.

DGamma.CP5ConfluenceDeletionChainSpike:22903:22--22903:104
 22899 |   (decEq @{keyEq} wanted current = observed) ->
 22900 |   (allList predicate (deleteEntries @{keyEq} wanted (Bind current cell :: rest)) = True)
 22901 | scopedAllDeleteHeadAt key value keyEq predicate wanted current cell rest source survivingTail
 22902 |   (Yes same) exact =
 22903 |     rewrite exact in scopedAndRightTrue (predicate (Bind current cell)) (allList predicate rest) source
                              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

### B96 attempt 1/3

```text
Error: While processing type of scopedPlanNoFailure. Can't bind implicit DGamma.CP5ConfluenceDeletionChainSpike.{value:238692} of type ({arg:3083} : ?DGamma.CP5ConfluenceDeletionChainSpike.{key:238689}_[name[8], key[7], world[6], error[5], value[4], nameEq[3], ambient[2], source[1], target[0]]) -> Type

DGamma.CP5ConfluenceDeletionChainSpike:22933:1--22939:104
 22933 | 0 scopedPlanNoFailure :
 22934 |   (name, key, world, error : Type) -> (value : key -> Type) ->
 22935 |   (nameEq : DecEq name) -> (ambient : world) ->
 22936 |   (source, target : Registry name key value world error) ->
 22937 |   InactiveLeafDeletionPlan nameEq source target ->
 22938 |   (noFailedFibers (the (SystemState name key value world error) (MkSystemState ambient source)) = True) ->

Error: No type declaration for DGamma.CP5ConfluenceDeletionChainSpike.scopedPlanNoFailure.

DGamma.CP5ConfluenceDeletionChainSpike:22940:1--22940:111
 22936 |   (source, target : Registry name key value world error) ->
 22937 |   InactiveLeafDeletionPlan nameEq source target ->
 22938 |   (noFailedFibers (the (SystemState name key value world error) (MkSystemState ambient source)) = True) ->
 22939 |   (noFailedFibers (the (SystemState name key value world error) (MkSystemState ambient target)) = True)
 22940 | scopedPlanNoFailure name key world error value nameEq ambient _ _ NoInactiveLeafDeletion noFailure = noFailure
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

## Frozen surfaces, seed, and hygiene

The full surface starts at `0 adjacentSwapSuffixSpike :`, excludes `public
export`, and ends at the last non-newline byte. Its fixed-size extraction was
checked against both expected digests and its following newline; the statement
prefix ends in `adjacentSwapSuffixSpike =`.

```text
Frozen full: 1470 2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf
Frozen statement: 1154 3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf
Seeded TTC: 207 / 207 missing: []
CP3 blob: 2c697e532e83989de8591fa6a4378747c6a501c0
ipkg blob: da0c007ee08c4648e459296eb6f0e72a40e2ac89
Production diff vs 34b21c9: PASS
LocalDiamond diff: PASS
No staged files: PASS
Whitespace: PASS
with count baseline/current: 9 9
Same-line with count baseline/current: 8 8
Added prohibited \bbelieve_me\b : []
Added prohibited \bassert_total\b : []
Added prohibited ^\s*partial\b : []
Added prohibited \?\w+ : []
Added prohibited ^\s*let\b : []
Added prohibited \bwith\s*\( : []
Added prohibited \bdeletionTheoremProof\b : []
%default total: present
Holes CanonicalSort 2
Holes CrossTrace 4
Holes DeletionChain 3
Holes LocalDiamond 0
Holes RenamingComposition 1
Untouched review SHA-256: 61fc23ae4cea4565b442c840be39c41746ecbac73b8c2f73d04f1e3b4f4681e8
Intended rejection R11DirectDeletionStepCloneNegative : PASS
Intended rejection R11DeletionFillerMapCertificateNegative : PASS
Intended rejection R10DeletionStepMapCloneNegative : PASS
Gate deletion : PASS
Gate positive : PASS
Gate seeded : PASS
Proof commits: 115
Implementation invocations: 124 successful: 115 failed: 9
Failed invocations: B18-1, B22-1, B69-1, B76-1, B89-1, B91-1, B91-2, B93-1, B96-1
Working tree: ?? paper/
?? review-o6-body-adversarial.md
```

A separate git declaration-set audit found 111 new top-level declarations
across 115 checked proof commits, with no commit adding more than one. The
four surface-only commits are A1 `6256b77`, B17 `05bb683`, B25 `d2d54e4`, and
B46 `551b039`. Only proof source and this audit are staged for their respective
commits; no staged files remain after the audit commit. The only untracked
paths at the gate remain `paper/` and `review-o6-body-adversarial.md`.

Source diff from `58d3642`: **3906 insertions / 41 deletions**, one Idris file.
The review file was never modified, staged, committed, or removed. Temporary
R166 source snippets, scripts and logs lived outside the repository; no stray
untracked research file or compiled standalone probe was created. The exact
failed compiler transcripts and all commit/check mappings are retained above.

## Status

**Fully proved this shift:** the B26 constructor-field cure and successful
named alignment producer/consumers; canonical ready alignment; all-action
relational tag preservation including operational LAdvance outcomes; exact
selected-birth census transport and kept-parent exclusion; live tagged,
control-bridged, surviving-discipline selected interior/closed, post-close and
relational fold producers; source discipline prefix restriction; canonical
closing-append endpoint/trace equality with retained certificates; no-failure
and quiescence transport through inactive plans and ordered runtime controls,
and at the canonical enriched post-close/relational endpoint.

**Partial:** the overall O9 producer integration. The enriched producer
endpoints are complete as described, but the inherited untagged whole-result
adapter has not been replaced by the final target-bundle/operational-capital
assembler. `TraceComponentsTotal` still requires source-derived per-kept
active-table transport at the local next-boundary producers. No proof of that
clause or completed `nextPremises` is claimed.

**Merely stated:** the same ten research holes, split **2/4/3/0/1**. O9/O10/O11
retain their original holes with **0/3 attempts**. This checked prefix does not
establish Theorem 73 or reduce the hole count.

**Next after reviewer/owner gate:** derive and retain target component-totality
at selected/post-close/relational kept boundaries; thread it with the already
proved surviving discipline, alignment, and endpoint quiet/no-failure clauses;
assemble the exact whole-result `ReplayInvariantBundle` and producer operational
capital from these outputs; only then open O9, O10, and O11 in order. Never infer
totality from tags alone, infer producer tags from a bare public result, call
frozen `deletionTheoremProof`, or downgrade the required bundle.
