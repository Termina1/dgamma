# O6 R170 — exact external-orchestration producer and O9 closure

## Baseline and protocol

Started **2026-09-06 03:51:08 UTC**, branch `cp5-thm73-scoping`, required HEAD
**`66f17c1`** verified. Initial tree: only permitted untracked `paper/` and
`review-o6-body-adversarial.md`. Idris **0.8.0**; `idris2 --help` verified
`--source-dir <dir>` and `--check` before the first invocation. R169 (all 622
lines), R168, R167 and R146 were read first; the full extracted paper was read,
including the two initially truncated opening lines in a subsequent read.

No-new-attempt boundary **07:11:08 UTC**, safe-gate deadline **07:36:08 UTC**,
timeout **07:51:08 UTC**. Every check is sequential, target-fresh, seeded, and
preceded by process inspection; no orphan compiler was encountered or killed.
No build directory or TTC/TTM was removed, no from-scratch rebuild, no concurrent
Idris compiler. Source/fixture mtimes are touched for target checks; production
files are neither edited nor touched. Temporary scripts and transcripts are
under `/tmp/dgamma-r170*`, outside the repository. No subagent launched.

Only DeletionChain and this audit change. LocalDiamond is byte-identical to
`66f17c1`, no visibility exception used. `src/` and `dgamma.ipkg` are
byte-identical to `34b21c9`. No new `with`, let alias, nonlinear pattern,
unchecked axiom, partial definition, postulate, `believe_me`, `assert_total`,
or retained proof hole. `%default total` remains in force. Existing nine
with-blocks are unchanged. No frozen `deletionTheoremProof` invocation from
this chain, no raw-name exclusion cast, no O14/O17/O19 or O21 withdrawal edit.
The R146 route-change condition has not been met and no route change was made.

The first Python script launch failed before writing source or invoking Idris:
`/private/tmp/nt.py` shadowed the standard-library Windows import while pathlib
loaded, producing `AttributeError: partially initialized module 'pathlib' ...
has no attribute 'PurePath'`. All subsequent scripts use `python3 -I`; the
unrelated file was not modified. A bounded read-only fast-context search failed
with `fetch failed`; no source or proof invocation was involved. These are
preparation/tool failures, not hidden compiler attempts.

## Unit A — SameExternalOrchestration COMPLETE

**Exact producer: `scopedEnrichedExternalOrchestration`, `f85b763`.**
**Full step assembler unconditional: `scopedEnrichedStepFromExternal`, `e00e4b6`.**
The former explicit SameExternal input is removed, not moved to the O9 caller.

### State-sensitive kept root roles

`scopedRootObservation` reads O-Insert's actual parent and the actual owner-cell
parent lookup at O-Retire/O-Remove; lifecycle actions observe false. Its two
checked directions (`scopedRootObserved`, `scopedObservedRoot`) connect this
executable observation to the unchanged `RootOrchestrationStep`. Explicit
observed values and equations are used throughout; no new with-block or
post-hoc computed-view elimination is required.

`ScopedRootRoleSeal` owns the exact source/target observation equation as an
erased constructor field. `scopedExternalKeep` consumes that field and the
already-owned action equality, matching root inputs or skipping both internal
heads. It never treats matching action/tag alone as root-role agreement.

`scopedPlannedActionRoot` authenticates the kept actor's exact current generation
via `retainedNonInsertOutsideCurrentRegistered`, then frames its actual lookup
through the current deletion plan. Ordered controls preserve actual parent
fields, including selected static controls where lifecycle states differ.
`scopedRelationalActionRoot` (`0f39577`), `scopedSelectedActionRoot` (`ca93c4d`)
and `scopedPostCloseActionRoot` (`60cbc8e`) produce these equations from the
actual live boundaries. This includes selected O-Retire and O-Remove, with no
extra root-role premise or equality of source and target evaluator proof terms.

### Deleted generations are actually non-root

`ScopedDeletedRootSeal` owns the exact false observation. The source scanner
maintains `ScopedCurrentRootExclusion`: for each *actual* current generation
lookup belonging to the selected set, the corresponding actual fiber-parent
lookup is non-root. Accepted local updates preserve parent roles; source
Inactive lookup witnesses rule out insertion into an already-current selected
cell. Foreign actions frame both actual registry and generation lookups.
Insertion and removal handle new/deleted current generations exactly; a later
raw-name reissue is not conflated with a selected birth.

`ScopedActionAt` and positional uniqueness connect every selected birth to
R169's exact `DeletedGenerationClassification`. A source root insertion at that
same birth ordinal would equal the classified child insertion; observing its
parent proves non-root. `scopedRootBirthInputs` carries explicit count offsets,
and `scopedCandidateOwnedRootSeals` (`c63b8c6`) discharges the scanner's birth
inputs from the actual candidate. This producer is source-only and takes no
caller-provided non-root evidence. It consumes `selectedChildrenHaveNoEpisode`
to maintain the authentic current Inactive cells during the scan.

### Live retention and exact whole assembly

| Live result | Field / producer | Commit |
|---|---|---|
| Post-close AND relational folds | `postCloseOutputExternal` | `a59376f` |
| Selected interior folds | `interiorOutputExternal` | `024c845` |
| Selected closed fold, deleted opening and close | `selectedOutputExternal` | `ed8611e` |
| Source seals at the exact before/center cut | `scopedCandidateRootSealsAfterBefore` | `53a9213` |
| Full exact SameExternal at enriched DeletionResult | `scopedEnrichedExternalOrchestration` | `f85b763` |
| Full enriched step with the last input discharged | `scopedEnrichedStepFromExternal` | `e00e4b6` |

The three output fields are erased transformers from the exact source
`ScopedOwnedRootSeals` family to SameExternal at their canonical ready trace,
analogous to the inherited source-totality transformers. Their inputs are
**actually discharged** by `scopedCandidateOwnedRootSeals` and exact scan cuts
in the whole assembler. Kept clauses produce seals at the local boundary;
deleted clauses project the source-owned generation seal (selected lifecycle
deletions emit their exact false equation). No caller-selected origin, inferred
root role, or unproduced whole external correspondence remains.

The full SURVIVING-trace RegistrationDiscipline fields are unchanged. The full
TARGET ReplayInvariantBundle still feeds `nextPremises`; no rank, support,
provenance, totality, semantic-replay or target-discipline clause is downgraded.
The operational certificate and registration accounting remain exactly at the
R169 frozen whole-origin function and global two-sided generation bijection.

## Unit B — O9 CLOSED; mandatory mid-shift gate

`enrichDeletionChainStepSpike` closed **1/3** at **`89435dc`**, fresh check
**05:53:00–05:54:21 UTC**. Its original signature is unchanged. The body applies
the now-unconditional full assembler to `scopedEnrichedDeletionFoldsFromPremises`
with the original scoped `noDependent` argument. It does not call the frozen
public deletion theorem.

Fresh O9 census: **9 = CanonicalSort 2 / CrossTrace 4 / DeletionChain 2 /
LocalDiamond 0 / RenamingComposition 1**, delta **-1**. O10/O11 bodies are still
unchanged, **0/3**, at this checkpoint. No O10/O11 attempt is authorized by this
audit itself: the mandatory supervisor/reviewer milestone gate comes first.

Fresh sequential O9 gate checks after `89435dc`: DeletionChain passed;
`R11DeletionCertificateProjectionPositive` passed;
`R11DirectDeletionStepCloneNegative` rejected at `cloneDeletionStepWithAlternateMap`
with `occurrences and alternate`;
`R11DeletionFillerMapCertificateNegative` rejected at
`fillerMapCannotConstructDeletionCertificate` with
`generationSubsequenceSourceOrdinal`;
`R10DeletionStepMapCloneNegative` rejected at `replaceDeletionStepOccurrenceMap`
with `alternate and step .deletionOccurrenceCorrespondence`.
All negative diagnostics were checked explicitly, not merely their exit codes.
Seeded `idris2 --build dgamma.ipkg` passed, **207/207** TTC files present.
Gate batch: **05:54:58–05:56:59 UTC**. No test fixture added or edited; the wider
R11 suite and runtime execution were not run.

## Incremental ledger and failed attempts

One new top-level declaration maximum per invocation; surface units A50, A51,
A59, A64 and O9 introduce no new declaration. Every passing implementation
invocation has a fresh `Building DGamma.CP5ConfluenceDeletionChainSpike` marker
and exit 0, followed by an immediate commit. The per-commit declaration-set
validator confirms 60 new declarations across 65 checked implementation commits.
Four rejected spellings were corrected on their second attempts (no exhausted
3/3 unit). Full errors follow the ledger. Source proofs use erased quantities
where appropriate; the two executable root observation functions are total.

Common direct check, verified CLI spelling:

```sh
idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr
```

Fixture commands add `--source-dir research-tests` and check the exact fixture
filenames listed above. All final fresh checks retain the production seed.

| Unit | Declaration/surface | Attempts | Commit | Fresh check ended UTC |
|---|---|---:|---|---|
| A1 | `scopedParentRoot` | 1/3 | `5942ded` | 03:56:49 |
| A2 | `scopedRootObservation` | 1/3 | `20be30a` | 03:58:18 |
| A3 | `scopedRootObserved` | 1/3 | `865e4bc` | 03:59:48 |
| A4 | `scopedRootParentExact` | 1/3 | `3491645` | 04:01:11 |
| A5 | `scopedObservedRootCell` | 2/3 | `ed9ad23` | 04:04:08 |
| A6 | `scopedRootCellUse` | 1/3 | `8ff0115` | 04:05:46 |
| A7 | `scopedObservedRoot` | 1/3 | `ef64ede` | 04:07:17 |
| A8 | `ScopedRootRoleSeal` | 1/3 | `6d8723b` | 04:08:51 |
| A9 | `scopedExternalKeepAt` | 1/3 | `7a70458` | 04:10:28 |
| A10 | `scopedExternalKeep` | 1/3 | `ada693f` | 04:12:10 |
| A11 | `ScopedDeletedRootSeal` | 1/3 | `3094f91` | 04:13:33 |
| A12 | `scopedExternalDelete` | 1/3 | `96c24b4` | 04:14:56 |
| A13 | `scopedControlParentExact` | 1/3 | `d35641f` | 04:16:56 |
| A14 | `scopedStaticParentExact` | 1/3 | `9e8dd28` | 04:18:15 |
| A15 | `scopedSelectedParentExact` | 1/3 | `1c13875` | 04:19:37 |
| A16 | `scopedLookupRootMatched` | 1/3 | `c398a74` | 04:21:31 |
| A17 | `scopedLookupRootHeadAt` | 1/3 | `3b17c60` | 04:22:59 |
| A18 | `scopedSelectedOrderedRoot` | 1/3 | `4d78907` | 04:24:31 |
| A19 | `scopedSelectedRegistryRoot` | 1/3 | `36b9049` | 04:26:27 |
| A20 | `scopedControlLookupRoot` | 1/3 | `007731c` | 04:27:54 |
| A21 | `scopedOutsidePlanRootLookup` | 1/3 | `3a3e73d` | 04:29:40 |
| A22 | `scopedPlannedActionRoot` | 2/3 | `10c9429` | 04:32:36 |
| A23 | `scopedRootSealAtAction` | 1/3 | `4720ee3` | 04:34:15 |
| A24 | `scopedRelationalActionRoot` | 1/3 | `0f39577` | 04:35:43 |
| A25 | `scopedSelectedActionRoot` | 1/3 | `ca93c4d` | 04:37:13 |
| A26 | `scopedPostCloseActionRoot` | 1/3 | `60cbc8e` | 04:38:45 |
| A27 | `ScopedCurrentRootExclusion` | 1/3 | `6a045b0` | 04:44:12 |
| A28 | `ScopedRootBirthInputs` | 1/3 | `3727d0e` | 04:45:42 |
| A29 | `ScopedOwnedRootSeals` | 1/3 | `be0c56b` | 04:47:08 |
| A30 | `scopedPresentRootFalseAfterUpdate` | 2/3 | `2f740bd` | 04:50:10 |
| A31 | `scopedInactiveRootFalseAfterAction` | 1/3 | `25fb869` | 04:52:04 |
| A32 | `scopedOwnedRootAfterAction` | 1/3 | `60e2bbf` | 04:54:04 |
| A33 | `scopedRootExclusionStepAt` | 1/3 | `5abc5d7` | 04:55:45 |
| A34 | `scopedRootExclusionStep` | 1/3 | `5a313e9` | 04:57:25 |
| A35 | `scopedOwnedRootObservation` | 1/3 | `878c625` | 04:59:25 |
| A36 | `scopedOwnedRootSeal` | 1/3 | `f7805cc` | 05:00:54 |
| A37 | `scopedSourceOwnedRootSeals` | 1/3 | `bda0de8` | 05:03:09 |
| A38 | `ScopedActionAt` | 1/3 | `725da2d` | 05:05:30 |
| A39 | `scopedActionHeadExact` | 1/3 | `e9a7014` | 05:06:55 |
| A40 | `scopedActionTail` | 1/3 | `a166c2d` | 05:08:18 |
| A41 | `scopedActionAtUnique` | 1/3 | `6911fe3` | 05:09:44 |
| A42 | `scopedActionAppendRight` | 1/3 | `ad7d4c5` | 05:11:15 |
| A43 | `scopedLocatedActionAt` | 1/3 | `1a28fc0` | 05:12:48 |
| A44 | `scopedClassifiedBirthNonRoot` | 1/3 | `f36136c` | 05:14:35 |
| A45 | `scopedRootBirthInputs` | 2/3 | `c66c9a8` | 05:17:35 |
| A46 | `scopedCandidateOwnedRootSeals` | 1/3 | `c63b8c6` | 05:19:08 |
| A47 | `scopedNamedRootSeal` | 1/3 | `4e6d246` | 05:21:43 |
| A48 | `scopedLifecycleRootFalse` | 1/3 | `baf1868` | 05:23:09 |
| A49 | `scopedEpisodeDeletedRootSeal` | 1/3 | `147a1fd` | 05:24:38 |
| A50 | `surface` | 1/3 | `a59376f` | 05:27:05 |
| A51 | `surface` | 1/3 | `024c845` | 05:29:36 |
| A52 | `scopedExternalAppend` | 1/3 | `cb2d6e0` | 05:32:00 |
| A53 | `scopedAppendTraceEmpty` | 1/3 | `e4828d9` | 05:33:35 |
| A54 | `scopedRootSealsAppendLeft` | 1/3 | `fe2c471` | 05:35:14 |
| A55 | `scopedRootSealsAppendRight` | 1/3 | `b45e3e1` | 05:36:42 |
| A56 | `scopedExternalAcrossTraceEnd` | 1/3 | `2973cd0` | 05:38:07 |
| A57 | `scopedExternalAppendDeleted` | 1/3 | `53bfb9f` | 05:39:42 |
| A58 | `scopedAppendSelectedCloseExternal` | 1/3 | `9fbeaf7` | 05:41:34 |
| A59 | `surface` | 1/3 | `ed8611e` | 05:43:26 |
| A60 | `scopedExternalReflexive` | 1/3 | `8621b1f` | 05:45:28 |
| A61 | `scopedEnrichedExternalJoin` | 1/3 | `a6220f3` | 05:47:22 |
| A62 | `scopedCandidateRootSealsAfterBefore` | 1/3 | `53a9213` | 05:49:01 |
| A63 | `scopedEnrichedExternalOrchestration` | 1/3 | `f85b763` | 05:50:56 |
| A64 | `surface` | 1/3 | `e00e4b6` | 05:52:29 |
| B-O9 | `surface` | 1/3 | `89435dc` | 05:54:21 |

### Exact failed compiler diagnostics

#### A5-1

```text
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  scopedParentRoot is shadowing DGamma.CP5ConfluenceDeletionChainSpike.scopedParentRoot
  fiberParent is shadowing DGamma.Calculus.fiberParent

DGamma.CP5ConfluenceDeletionChainSpike:19899:3--19903:102
 19899 | 0 scopedObservedRootCell :
 19900 |   (name, key, world, error : Type) -> (value : key -> Type) ->
 19901 |   (observed : Maybe (Fiber name key value world error)) ->
 19902 |   (maybe False (scopedParentRoot . fiberParent) observed = True) ->
 19903 |   (fiber : Fiber name key value world error ** ((observed = Just fiber), (fiberParent fiber = Root)))

Error: While processing type of scopedObservedRootCell. Can't solve constraint between: ?type_of_fiberParent [no locals in scope] and Fiber name key value world error -> ?b.

DGamma.CP5ConfluenceDeletionChainSpike:19902:36--19902:47
 19898 |
 19899 | 0 scopedObservedRootCell :
 19900 |   (name, key, world, error : Type) -> (value : key -> Type) ->
 19901 |   (observed : Maybe (Fiber name key value world error)) ->
 19902 |   (maybe False (scopedParentRoot . fiberParent) observed = True) ->
                                            ^^^^^^^^^^^

Error: No type declaration for DGamma.CP5ConfluenceDeletionChainSpike.scopedObservedRootCell.

DGamma.CP5ConfluenceDeletionChainSpike:19904:1--19904:79
 19900 |   (name, key, world, error : Type) -> (value : key -> Type) ->
 19901 |   (observed : Maybe (Fiber name key value world error)) ->
 19902 |   (maybe False (scopedParentRoot . fiberParent) observed = True) ->
 19903 |   (fiber : Fiber name key value world error ** ((observed = Just fiber), (fiberParent fiber = Root)))
 19904 | scopedObservedRootCell name key world error value Nothing truth = absurd truth
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

#### A22-1

```text
Error: Unsolved holes:
DGamma.CP5ConfluenceDeletionChainSpike.{key:213316} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:20123:6--20123:126
 20119 |   (scopedRootObservation name key world error value nameEq action source = scopedRootObservation name key world error value nameEq action target)
 20120 | scopedPlannedActionRoot name key world error value nameEq registered ordinal live unique (OInsert actor parent component) retained source target plan roots = Refl
 20121 | scopedPlannedActionRoot name key world error value nameEq registered ordinal live unique (ORetire actor) retained source target plan roots =
 20122 |   scopedOutsidePlanRootLookup name key world error value nameEq actor registered live (registry source) (registry target) plan
 20123 |     (retainedNonInsertOutsideCurrentRegistered nameEq registered ordinal live unique (ORetire actor) NonInsertRetire retained) (roots actor)
              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{world:213317} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:20123:6--20123:126
 20119 |   (scopedRootObservation name key world error value nameEq action source = scopedRootObservation name key world error value nameEq action target)
 20120 | scopedPlannedActionRoot name key world error value nameEq registered ordinal live unique (OInsert actor parent component) retained source target plan roots = Refl
 20121 | scopedPlannedActionRoot name key world error value nameEq registered ordinal live unique (ORetire actor) retained source target plan roots =
 20122 |   scopedOutsidePlanRootLookup name key world error value nameEq actor registered live (registry source) (registry target) plan
 20123 |     (retainedNonInsertOutsideCurrentRegistered nameEq registered ordinal live unique (ORetire actor) NonInsertRetire retained) (roots actor)
              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{error:213318} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:20123:6--20123:126
 20119 |   (scopedRootObservation name key world error value nameEq action source = scopedRootObservation name key world error value nameEq action target)
 20120 | scopedPlannedActionRoot name key world error value nameEq registered ordinal live unique (OInsert actor parent component) retained source target plan roots = Refl
 20121 | scopedPlannedActionRoot name key world error value nameEq registered ordinal live unique (ORetire actor) retained source target plan roots =
 20122 |   scopedOutsidePlanRootLookup name key world error value nameEq actor registered live (registry source) (registry target) plan
 20123 |     (retainedNonInsertOutsideCurrentRegistered nameEq registered ordinal live unique (ORetire actor) NonInsertRetire retained) (roots actor)
              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{value:213319} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:20123:6--20123:126
 20119 |   (scopedRootObservation name key world error value nameEq action source = scopedRootObservation name key world error value nameEq action target)
 20120 | scopedPlannedActionRoot name key world error value nameEq registered ordinal live unique (OInsert actor parent component) retained source target plan roots = Refl
 20121 | scopedPlannedActionRoot name key world error value nameEq registered ordinal live unique (ORetire actor) retained source target plan roots =
 20122 |   scopedOutsidePlanRootLookup name key world error value nameEq actor registered live (registry source) (registry target) plan
 20123 |     (retainedNonInsertOutsideCurrentRegistered nameEq registered ordinal live unique (ORetire actor) NonInsertRetire retained) (roots actor)
              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{key:213361} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:20126:6--20126:126
 20122 |   scopedOutsidePlanRootLookup name key world error value nameEq actor registered live (registry source) (registry target) plan
 20123 |     (retainedNonInsertOutsideCurrentRegistered nameEq registered ordinal live unique (ORetire actor) NonInsertRetire retained) (roots actor)
 20124 | scopedPlannedActionRoot name key world error value nameEq registered ordinal live unique (ORemove actor) retained source target plan roots =
 20125 |   scopedOutsidePlanRootLookup name key world error value nameEq actor registered live (registry source) (registry target) plan
 20126 |     (retainedNonInsertOutsideCurrentRegistered nameEq registered ordinal live unique (ORemove actor) NonInsertRemove retained) (roots actor)
              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{world:213362} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:20126:6--20126:126
 20122 |   scopedOutsidePlanRootLookup name key world error value nameEq actor registered live (registry source) (registry target) plan
 20123 |     (retainedNonInsertOutsideCurrentRegistered nameEq registered ordinal live unique (ORetire actor) NonInsertRetire retained) (roots actor)
 20124 | scopedPlannedActionRoot name key world error value nameEq registered ordinal live unique (ORemove actor) retained source target plan roots =
 20125 |   scopedOutsidePlanRootLookup name key world error value nameEq actor registered live (registry source) (registry target) plan
 20126 |     (retainedNonInsertOutsideCurrentRegistered nameEq registered ordinal live unique (ORemove actor) NonInsertRemove retained) (roots actor)
              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{error:213363} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:20126:6--20126:126
 20122 |   scopedOutsidePlanRootLookup name key world error value nameEq actor registered live (registry source) (registry target) plan
 20123 |     (retainedNonInsertOutsideCurrentRegistered nameEq registered ordinal live unique (ORetire actor) NonInsertRetire retained) (roots actor)
 20124 | scopedPlannedActionRoot name key world error value nameEq registered ordinal live unique (ORemove actor) retained source target plan roots =
 20125 |   scopedOutsidePlanRootLookup name key world error value nameEq actor registered live (registry source) (registry target) plan
 20126 |     (retainedNonInsertOutsideCurrentRegistered nameEq registered ordinal live unique (ORemove actor) NonInsertRemove retained) (roots actor)
              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{value:213364} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:20126:6--20126:126
 20122 |   scopedOutsidePlanRootLookup name key world error value nameEq actor registered live (registry source) (registry target) plan
 20123 |     (retainedNonInsertOutsideCurrentRegistered nameEq registered ordinal live unique (ORetire actor) NonInsertRetire retained) (roots actor)
 20124 | scopedPlannedActionRoot name key world error value nameEq registered ordinal live unique (ORemove actor) retained source target plan roots =
 20125 |   scopedOutsidePlanRootLookup name key world error value nameEq actor registered live (registry source) (registry target) plan
 20126 |     (retainedNonInsertOutsideCurrentRegistered nameEq registered ordinal live unique (ORemove actor) NonInsertRemove retained) (roots actor)
              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

#### A30-1

```text
Error: While processing right hand side of scopedPresentRootFalseAfterUpdate. When unifying:
    fiberComponent next = fiberComponent oldFiber
and:
    fiberComponent next = fiberComponent oldFiber
Mismatch between: Component key value world error and Parent ?name.

DGamma.CP5ConfluenceDeletionChainSpike:20234:37--20234:49
 20230 |   void (nothingIsNotJust (trans (sym absent) found))
 20231 | scopedPresentRootFalseAfterUpdate name key world error value nameEq actor source _
 20232 |   (LocalReplace {oldFiber} @{oldFound} @{staticParent} next) present found nonRoot =
 20233 |     trans (cong (maybe False (scopedParentRoot . fiberParent)) (lookupReplacedFiber @{nameEq} actor oldFiber next source oldFound))
 20234 |       (trans (cong scopedParentRoot staticParent)
                                             ^^^^^^^^^^^^
```

#### A45-1

```text
Error: While processing right hand side of scopedRootBirthInputs. Can't solve constraint between: S (plus ordinal index) and plus ordinal (S index).

DGamma.CP5ConfluenceDeletionChainSpike:28569:134--28569:140
 28565 |         actionSame (ScopedActionHere transition rest))
 28566 |       (replace {p = \position => Elem (MkRegistrationGeneration child position) registered} (sym (plusZeroRightNeutral ordinal)) member)),
 28567 |    scopedRootBirthInputs name key world error value registered (S ordinal) _ finalState rest
 28568 |      (\index, child, parent, component, atBirth, member => births (S index) child parent component (ScopedActionLater transition rest atBirth)
 28569 |        (replace {p = \position => Elem (MkRegistrationGeneration child position) registered} (sym (plusSuccRightSucc ordinal index)) member)))
                                                                                                                                              ^^^^^^
```

## Frozen surfaces and seeded evidence at O9

```json
{
  "head": "89435dc",
  "fullSurfaceBytes": 1470,
  "fullSurfaceSHA": "2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf",
  "statementBytes": 1154,
  "statementSHA": "3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf",
  "seeded": "207/207",
  "missing": [],
  "CP3Blob": "2c697e532e83989de8591fa6a4378747c6a501c0",
  "ipkgBlob": "da0c007ee08c4648e459296eb6f0e72a40e2ac89",
  "productionDiffEmpty": true,
  "reviewSHA": "61fc23ae4cea4565b442c840be39c41746ecbac73b8c2f73d04f1e3b4f4681e8",
  "holes": {
    "CanonicalSort": 2,
    "CrossTrace": 4,
    "DeletionChain": 2,
    "LocalDiamond": 0,
    "RenamingComposition": 1
  },
  "holeDelta": -1,
  "withCounts": [
    9,
    9
  ],
  "proofCommits": 65,
  "newDeclarations": 60,
  "implementationInvocations": 69,
  "implementationFailures": [
    "A5-1",
    "A22-1",
    "A30-1",
    "A45-1"
  ],
  "noStagedFiles": true,
  "LocalDiamond": "UNCHANGED byte-for-byte versus 66f17c1; no visibility exports",
  "prohibitedAdditions": {
    "\\bbelieve_me\\b": [],
    "\\bassert_total\\b": [],
    "^\\s*partial\\b": [],
    "\\?\\w+": [],
    "^\\s*let\\b": [],
    "\\bwith\\s*\\(": [],
    "\\bdeletionTheoremProof\\b": [],
    "\\bpostulate\\b": []
  },
  "status": "?? paper/\n?? review-o6-body-adversarial.md"
}
```

## Status at O9 checkpoint

**Fully proved:** exact source-derived kept/deleted root-role certificates; live selected/post-close/relational retention; full SameExternalOrchestration at the exact enriched result; unconditional full enriched step assembler; **O9** at `89435dc`.

**Partial:** the iterative deletion chain, pending O10/O11 and their mandatory gates.

**Merely stated:** nine research holes, split **2/4/2/0/1**. No new hole or escape hatch. Theorem 73 is not claimed.

**Next:** await the mandatory supervisor/reviewer O9 milestone ruling, then O10 and O11 in order under fresh 3-attempt budgets. Reviewer acceptance is required; these are reproducible self-checks, not independent review.

## O9 milestone ruling and Unit C — O10 CLOSED

The supervisor ratified O9 at `c0619b6`, independently checking HEAD, production
and LocalDiamond byte equality, clean permitted tree, no compiler process, the
three-line O9 body and the fresh **9 = 2/4/2/0/1** census. The ruling explicitly
authorized O10 and then O11 under the unchanged budgets/time guard. No O10
attempt occurred before that reply.

**O10 `deleteClosingEpisodesCoreSpike` closed 1/3 at `dd3ed2d`.** Fresh check
**06:44:46–06:46:06 UTC**. Its original signature is unchanged; the body is a
three-line application of `scopedClosingCoreAccessible` using Nat's checked
`WellFounded LT` instance and the actual `traceLength`.

O10 required real history capital, not merely a recursive call. In particular,
an arbitrary action correspondence does not imply that the mapped parent close
still follows the mapped child birth. `scopedOrdinalPathOrder` (`ee14a6b`)
proves strict temporal monotonicity of actual subsequence paths, and
`scopedDeletionOriginsOrdered` (`bb03809`) applies it to the **frozen whole
occurrence origin's stored embeddings** at the actual three segment shapes.
No ordinal map is substituted and no order law is silently added to the public
correspondence record.

`scopedLocatedActionAfter` (`22b6032`) extracts a genuine occurrence in the
actual after-birth suffix from strict positional order. `scopedAfterBirthOccurrence`
(`86bf895`) constructs the target parent-close location and its exact strict
birth-offset equation together. `scopedDeletionClassifiedOriginAt` (`26cddd3`)
and `scopedPullDeletedClassification` (`c8234de`) then pull each later deleted
classification to its authentic source birth, **including its later parent
close**. Raw names are not used to identify generations.

`scopedClassifiedGenerations` enumerates every current selected birth with its
actual classification. `scopedClosingFreeCoreStep` (`e548640`) prepends that list
to the pullback of **every** entry in the recursively produced history. It
retains the exact target trace, the full target premises, closing-freeness,
SameExternal, semantic replay, and the actual recursive deletion derivation.
No empty-history shortcut or omission of later history was used (the identity
base alone has empty history). As in the existing surface, Core itself has no
separate completeness equation for the list; O11 must assemble its exact
cumulative accounting rather than infer such an equation from an arbitrary
Core constructor.

`scopedClosingCoreChoice` eliminates the actual O7/O8/O9 choice once.
`scopedClosingCoreAccessible` (`a6d7b1a`) performs total accessibility recursion,
retaining an explicit measure equation in its goal and using O9's strictly
shorter actual survivor for the recursive call. No fuel exhaustion case,
partiality escape or new assumption is introduced.

All **C1–C21 passed 1/3**, as did the O10 body. The C21 draft's lambda binder was
renamed from `nextPremises` to `nextCapital` before its sole invocation to avoid
shadowing; no extra probe/check was involved. O11 remains unchanged **0/3** at
this mandatory milestone checkpoint.

Fresh post-O10 census: **8 = CanonicalSort 2 / CrossTrace 4 / DeletionChain 1 /
LocalDiamond 0 / RenamingComposition 1**, delta **-2** from the shift baseline.
The complete six-check gate batch was rerun sequentially at `dd3ed2d`,
**06:46:21–06:48:22 UTC**: fresh DeletionChain and R11 positive passed, all three
negative fixtures rejected at the same intended diagnostics, and seeded
`idris2 --build dgamma.ipkg` passed with **207/207** TTCs. No fixture changed.

### Unit C fresh-check ledger

| Unit | Declaration/surface | Attempts | Commit | Fresh check ended UTC |
|---|---|---:|---|---|
| C1 | `scopedClosingFreeCoreDone` | 1/3 | `0beafb5` | 06:04:13 |
| C2 | `scopedOrdinalKeptPositive` | 1/3 | `bf8cb21` | 06:06:09 |
| C3 | `scopedOrdinalKeptLaterOrder` | 1/3 | `1cb736b` | 06:08:24 |
| C4 | `scopedOrdinalDeletedLaterOrder` | 1/3 | `1491341` | 06:10:10 |
| C5 | `scopedOrdinalPathOrder` | 1/3 | `ee14a6b` | 06:12:10 |
| C6 | `scopedDeletionOriginsOrdered` | 1/3 | `bb03809` | 06:14:06 |
| C7 | `scopedActionPositionOccurs` | 1/3 | `2f5704c` | 06:16:57 |
| C8 | `scopedActionBeyondHead` | 1/3 | `83bebe9` | 06:18:38 |
| C9 | `scopedActionDropHeadAfter` | 1/3 | `bb8d122` | 06:20:21 |
| C10 | `scopedActionAfterCut` | 1/3 | `40b9adb` | 06:22:06 |
| C11 | `scopedLocatedActionAfter` | 1/3 | `22b6032` | 06:23:49 |
| C12 | `scopedLocateActionOccurs` | 1/3 | `e53fc87` | 06:26:47 |
| C13 | `ScopedAfterBirthOccurrence` | 1/3 | `1aff607` | 06:28:25 |
| C14 | `scopedAfterBirthOccurrence` | 1/3 | `86bf895` | 06:30:25 |
| C15 | `scopedGeneratedAfterActionOccurrence` | 1/3 | `7b55b3b` | 06:32:26 |
| C16 | `scopedDeletionClassifiedOriginAt` | 1/3 | `26cddd3` | 06:34:20 |
| C17 | `scopedPullDeletedClassification` | 1/3 | `c8234de` | 06:36:29 |
| C18 | `scopedClassifiedGenerations` | 1/3 | `1d69127` | 06:38:15 |
| C19 | `scopedClosingFreeCoreStep` | 1/3 | `e548640` | 06:40:10 |
| C20 | `scopedClosingCoreChoice` | 1/3 | `0cd4dfb` | 06:42:06 |
| C21 | `scopedClosingCoreAccessible` | 1/3 | `a6d7b1a` | 06:44:08 |
| C-O10 | `surface` | 1/3 | `dd3ed2d` | 06:46:06 |

### O10 frozen/seeded self-validation

```json
{
  "head": "dd3ed2d",
  "fullSurfaceBytes": 1470,
  "fullSurfaceSHA": "2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf",
  "statementBytes": 1154,
  "statementSHA": "3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf",
  "seeded": "207/207",
  "missing": [],
  "CP3Blob": "2c697e532e83989de8591fa6a4378747c6a501c0",
  "ipkgBlob": "da0c007ee08c4648e459296eb6f0e72a40e2ac89",
  "productionDiffEmpty": true,
  "reviewSHA": "61fc23ae4cea4565b442c840be39c41746ecbac73b8c2f73d04f1e3b4f4681e8",
  "holes": {
    "CanonicalSort": 2,
    "CrossTrace": 4,
    "DeletionChain": 1,
    "LocalDiamond": 0,
    "RenamingComposition": 1
  },
  "holeDelta": -2,
  "withCounts": [
    9,
    9
  ],
  "proofCommits": 87,
  "newDeclarations": 81,
  "implementationInvocations": 91,
  "implementationFailures": [
    "A5-1",
    "A22-1",
    "A30-1",
    "A45-1"
  ],
  "noStagedFiles": true,
  "LocalDiamond": "UNCHANGED byte-for-byte versus 66f17c1; no visibility exports",
  "prohibitedAdditions": {
    "\\bbelieve_me\\b": [],
    "\\bassert_total\\b": [],
    "^\\s*partial\\b": [],
    "\\?\\w+": [],
    "^\\s*let\\b": [],
    "\\bwith\\s*\\(": [],
    "\\bdeletionTheoremProof\\b": [],
    "\\bpostulate\\b": []
  },
  "status": "?? paper/\n?? review-o6-body-adversarial.md"
}
```

## Status at O10 checkpoint

**Fully proved:** Unit A, **O9** (`89435dc`), and the complete total **O10 core** (`dd3ed2d`) including full original-trace classification history.

**Partial:** cumulative endpoint and bidirectional registration accounting, the O11 obligation.

**Merely stated:** eight remaining research holes, **2/4/1/0/1**. O11 is untouched **0/3** at this gate.

**Next:** await mandatory O10 milestone ruling before O11. No new attempt after 07:11:08 UTC. Independent reviewer acceptance remains required.
