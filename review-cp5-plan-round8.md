# Theorem 73 scoping plan — adversarial review round 8

Review target: branch `cp5-thm73-scoping`, commit `2c40827833394a90411922972d1dae23ec8fae71`.

Method: repository read-only except this report; all elaboration probes are copied to `/tmp/thm73-review8-probes/`; Idris processes are serialized.

## Probe log

### Probe 1 — immutable production baseline and worktree preflight

**Command:**

```sh
cd /Users/vyacheslavshebanov/Work/dgamma
git branch --show-current
git rev-parse HEAD
git status --short
git diff --exit-code 34b21c9..2c40827 -- src dgamma.ipkg
git rev-parse 2c40827:src/DGamma/CP3.idr
```

**Result:** branch and head are exact. `git diff` exits 0. The target CP3 blob is exactly `2c697e532e83989de8591fa6a4378747c6a501c0`. Initial worktree has only the pre-existing untracked `paper/` directory; no tracked or staged changes.

**Classification:** note — production source and immutable target passed the preflight.

### Probe 2 — prior rejection front and revision-8 plan reconstruction

**Command:** full reads of `review-cp5-plan-round1.md` through `review-cp5-plan-round7.md`, emphasizing round 7 Probes 27/29/50/81 and its exact required changes; full read of `THM73-PLAN.md`.

**Result:** the narrowing front is reconstructed rather than accepted from prose. Round 7's checked attacks were (a) a caller-replaceable `canonicalToOriginal` map surviving into `IndependentCanonicalSchedule` and the bridge, and (b) action/tag-only source-position labels allowing the same concrete node to claim repeated positions. Revision 8 claims exact occurrence authentication against a deletion+sorting correspondence, enriched-capital-only bridge inputs, and prefix-composed occurrence labels. These are the primary type-level attack targets below.

**Classification:** note — documentary inventory only; no claimed repair is accepted yet.

### Probe 3 — revision-8 change surface and declaration inventory

**Command:**

```sh
cd /Users/vyacheslavshebanov/Work/dgamma
git diff --stat --name-status 139237a..2c40827
git log --oneline 139237a..2c40827
wc -l research/DGamma/CP5Confluence*Spike.idr THM73-PLAN.md
grep declaration anchors for authentication, accounting, block labels, and bridge
```

**Result:** production remains untouched. The changed interface surface is the plan plus canonical-sort, cross-trace, deletion-chain, and renaming spikes; local diamonds are unchanged. Actual declarations exist for `AuthenticatedCanonicalRegistrationMap`, `deletionSortingOccurrenceCorrespondence`, `OneTraceOrchestrationAccounting`, enriched `IndependentCanonicalSchedule`, `NodeCrossesSourceBlockPosition`, prefix-indexed `DerivationCrossesBlockPositions`, and enriched-capital-only `ReplayedCanonicalEndpointBridge`. This confirms only presence, not soundness or inhabitability.

**Classification:** note.

### Probe 4 — immutable external release and spike trees

**Command:** archive commit `2c40827` into `/tmp/thm73-review8-probes/release`; copy it to `spikes`; copy exactly the five CP5 research spike modules; compare hashes/counts and check for active Idris processes.

**Result:** release tree contains 207 Idris modules; spike tree contains 212. Both CP3 copies have blob `2c697e532e83989de8591fa6a4378747c6a501c0`; all copied spike files match the repository bytes; no `.git` directory and no active Idris process exists under the probe setup.

**Classification:** note — all following elaboration occurs outside the repository.

### Probe 5 — local-diamond spike elaboration

**Command:** `idris2 --source-dir src --check src/DGamma/CP5ConfluenceLocalDiamondSpike.idr` in the exact external spike tree.

**Result:** exit 0; closure reaches `31/31`. The occurrence-replay identity/composition functions and finite adjacent-swap families elaborate.

**Classification:** note — pass.

### Probe 6 — deletion-chain spike elaboration, first attempt

**Command:** `idris2 --source-dir src --check src/DGamma/CP5ConfluenceDeletionChainSpike.idr` with a 900-second harness timeout.

**Result:** harness timeout at production dependency `94/165`; no Idris process survived. The log contains warnings only and a partial TTC cache was retained.

**Classification:** note — infrastructure timeout, inconclusive; retry required.

### Probe 7 — deletion-chain spike elaboration, retry

**Command:** same serial check using the retained exact-tree TTC cache.

**Result:** Idris was killed by signal 9 (`exit 137`) before emitting a new module line; no process survived. This is the same resource behavior documented in earlier rounds and is not yet an interface result.

**Classification:** note — resource failure, inconclusive; another serialized retry is required.

### Probe 8 — deletion-chain spike elaboration with byte-identical dependency cache

**Command:** verify `/tmp/dgamma-cp5-r8-release/src` is byte-identical to the exact 207-module production tree and its five archived research sources are exact; seed its production TTC cache into the external tree, delete the deletion-spike TTC/TTM, then rerun the serial check.

**Result:** exit 0; the target is freshly built at `165/165`. Probes 6–7 are conclusively resource noise rather than an interface defect.

**Classification:** note — pass.

### Probe 9 — canonical-sort/authentication spike elaboration

**Command:** delete the exact cache's canonical-spike TTC/TTM and run `idris2 --source-dir src --check src/DGamma/CP5ConfluenceCanonicalSortSpike.idr`.

**Result:** exit 0; freshly reaches `166/166`. The authentication companion, exact deletion/sorting composition, indexed accounting, and enriched-capital assembler elaborate.

**Classification:** note — pass; elaboration alone does not establish producer derivability.

### Probe 10 — enriched bridge/O21 spike elaboration

**Command:** delete the renaming-spike TTC/TTM and run its external serial `--check`.

**Result:** exit 0; freshly reaches `167/167`. The bridge accepts enriched capitals and the complete scanner/O21 wrappers remain type-correct.

**Classification:** note — pass.

### Probe 11 — occurrence-authenticated cross-trace spike elaboration

**Command:** delete the cross-trace TTC/TTM and run its external serial `--check`.

**Result:** exit 0; freshly reaches `168/168` (with pre-existing lowercase-shadow warnings only). The prefix-indexed node labels, whole-block record, sealed O19/O20 path, and enriched bridge consumption elaborate.

**Classification:** note — pass.

### Probe 12 — coherent canonical-pair forgery, first construction

**Command:** check a new external `R8CoherentPairForgeryPositive.idr` which (1) replaces only the generated-registration half of an `ActionRegistrationReplayCorrespondence`, and (2) attempts to clone an enriched capital with a coherently replaced tree/map pair.

**Result:** expected construction reached the final authentication field but failed because a local `let` hid the definitional equality between the named alternate correspondence and its generated-origin projection.

**Classification:** note — probe elaboration issue, no interface conclusion.

### Probe 13 — coherent pair forgery retry with projection lemma

**Command:** add a proved projection lemma for the retargeted generated origin and retry.

**Result:** still failed at the same local-let opacity: Idris could not identify the let-bound correspondence projection with `alternateOrigins`.

**Classification:** note — probe elaboration issue, no interface conclusion.

### Probe 14 — coherent pair forgery retry with explicit authentication helper

**Command:** remove the let, introduce an explicitly indexed authentication helper, and retry.

**Result:** failed because the helper's exactness argument accidentally auto-bound one fixed dependent occurrence family instead of quantifying over all child/parent/component families.

**Classification:** note — probe signature error, no interface conclusion.

### Probe 15 — coherent synthetic `(tree, correspondence)` pair reaches enriched capital

**Command:** quantify the helper's exactness premise over all dependent generated-occurrence families and rerun `idris2 --source-dir src --check src/DGamma/R8CoherentPairForgeryPositive.idr`.

**Result:** exit 0 at `167/167`. The checked module exposes two facts:

1. `retargetGeneratedOrigins` keeps the legitimate all-action origin/tag fields but replaces the generated-registration origin independently using any generation bijection and ordinal equation.
2. `replaceCapitalWithCoherentPair` installs an alternate CP3 tree plus that alternate generated-origin correspondence and exact pair authentication, while reusing every other schedule, replay, block, endpoint, bundle, independence, and classification field. The resulting `IndependentCanonicalSchedule` contains no reduction/order/sorted index.

Thus `OneTraceOrchestrationAccounting` pins its own authentication to `deletionSortingOccurrenceCorrespondence reduction sorted`, but that producer provenance is forgotten by the public enriched-capital type. Consumers authenticate only an internally coherent caller pair, not necessarily the actual deletion+sorting fold pair.

**Classification:** blocker — authentication laundering survives one level up. The strong equality closes tree-only replacement but does not make `IndependentCanonicalSchedule` producer-authentic.

### Probe 16 — round-7 Probe-81 tree-only enriched clone

**Command:** stage the revision-8 `R8AuthenticatedCapitalCloneNegative.idr` in the exact external tree and run an expected-failure check.

**Result:** exit 1 at `canonicalRegistrationAuthentication capital`, with mismatch between the old tree and `alternate`. A tree cannot be changed while retaining the old occurrence correspondence/authentication.

**Classification:** note — pass negative. This narrow repair is real, but Probe 15 changes the tree and generated-origin map coherently and still succeeds.

### Probe 17 — project the exact fold pin from one-trace accounting, first attempt

**Command:** check `R8OneTraceFoldPinPositive.idr`, projecting that accounting's tree origin equals the definitional `deletionSortingOccurrenceCorrespondence reduction sorted` origin.

**Result:** diagnostics report missing direct `DecEq` import and an inaccessible projection cascading from that scope error (Idris anomalously returned process code 0 despite the diagnostics).

**Classification:** note — probe scope failure, no interface conclusion; retry required and diagnostics, not exit code alone, are authoritative.

### Probe 18 — one-trace fold-pin projection retry

**Command:** add direct `Decidable.Equality` import and rerun, treating any `Error:` diagnostic as failure regardless of Idris's exit code.

**Result:** direct scope now also requires `CP5ConfluenceDeletionChainSpike`; the dependent reduction type is undefined and the projection error cascades.

**Classification:** note — probe import failure, no interface conclusion.

### Probe 19 — one-trace accounting genuinely pins the fold

**Command:** add the direct deletion-chain import and rerun the projection check.

**Result:** exit 0 with no error diagnostics. For every canonical generated occurrence, `accountedGeneratedRegistrations` maps exactly to `replayGeneratedRegistrationOrigin (deletionSortingOccurrenceCorrespondence reduction sorted)`.

**Classification:** note — pass. This precisely localizes the residual: `OneTraceOrchestrationAccounting` is pinned, while the public `IndependentCanonicalSchedule` produced afterward forgets the reduction/order/sorted provenance and admits Probe 15's coherent repackage.

### Probe 20 — public synthetic schedule at enriched bridge input

**Command:** run revision-8 `R8PublicScheduleCannotReachBridgeNegative.idr` as an expected-failure check.

**Result:** exit 1 in the bridge type itself: `CanonicalSchedule ...` does not unify with `IndependentCanonicalSchedule ...`. Rejection occurs before the body or a birth equation.

**Classification:** note — pass negative. It does not close Probe 15, whose coherently forged value has the required enriched type.

### Probe 21 — authenticated bridge actual-direction constructor

**Command:** external positive check of `R8BridgeAuthenticatedDirectionPositive.idr`.

**Result:** exit 0 at `168/168`. The operational replay → canonical-left → left original → accepted-forward → right original direction is constructible for enriched capitals.

**Classification:** note — pass positive.

### Probe 22 — fixed-capital arbitrary right birth

**Command:** expected-failure check of `R8BridgeWrongBirthNegative.idr`.

**Result:** exit 1 exactly at the missing accepted generation equation; `()` cannot inhabit the equality between the authenticated left/right replay-origin generations.

**Classification:** note — pass negative for fixed capitals.

### Probe 23 — same block, same node, position 0→1

**Command:** expected-failure check of `R8WholeBlockShiftedNodeNegative.idr`.

**Result:** exit 1 with the advertised `Mismatch between: 0 and 1` at direct reuse of the label.

**Classification:** note — pass negative for a fixed selected block and fixed prefix occurrence map.

### Probe 24 — authenticated 1×1 whole-block wrapper

**Command:** positive check of `R8WholeBlockSingletonPositive.idr`.

**Result:** exit 0 at `169/169`. One nonempty finite node plus one recursively authenticated `(0,0)` label and exact block/node counts constructs `WholeBlockSwapDerivation`.

**Classification:** note — pass positive.

### Probe 25 — authenticated 2×1 whole-block wrapper

**Command:** positive check of `R8WholeBlockTwoByOnePositive.idr`.

**Result:** exit 0 at `169/169`. Two real finite nodes, recursive labels `[(0,0),(1,0)]`, and exact counts discharge all Cartesian fields.

**Classification:** note — pass positive.

### Probe 26 — authenticated 2×2 whole-block wrapper

**Command:** positive check of `R8WholeBlockTwoByTwoPositive.idr`.

**Result:** exit 0 at `169/169`. Four finite nodes and the strengthened recursive fold-label output alone (plus exact block/node counts) construct the exact Cartesian whole-block record; no action/tag premise remains.

**Classification:** note — pass positive at the wrapper boundary. The probe assumes rather than constructs the nontrivial recursive labels.

### Probe 27 — shifted block-start / compensating local-position alias

**Command:** check new `R8BlockStartAliasingPositive.idr`. It transports the exact same node between two `LocatedOpenEpisodeBlock` indices whenever their `start + localPosition` ordinals are equal, then specializes to starts 1/2 and positions 1/0.

**Result:** exit 0 at `169/169`. The isolated `NodeCrossesSourceBlockPosition` record treats `(block,start-local)` only through the resulting global ordinal, so `(start=1,pos=1)` aliases `(start=2,pos=0)` if the caller can prove both block-prefix equalities.

The whole-block wrapper does not allow per-node block choice: its block indices are definitionally the exact two `decomposedBlock sourceBlocks ...` values, its positions are bounded, and `safetyBlocksOrdered` supplies a `BlockBefore` proof for those selected blocks. Thus this conditional transport is not yet a checked whole-block forgery; a real attack would additionally need two authoritative selected blocks with overlapping in-bounds ordinals, which the located-block decompositions/order are designed to exclude.

**Classification:** major residual risk, not a blocker by itself — the node record's ordinal law is alias-prone in isolation, and the anti-alias argument is only implicit in upstream block decomposition/order. A complete O6 proof must derive and use disjoint selected-block ordinal ranges; the current positive wrappers assume labels rather than checking that derivation.

### Probe 28 — literal duplicate Cartesian label

**Command:** expected-failure check of retained `R7DuplicateLabelNegative.idr`.

**Result:** exit 1; `UniqueKeys` cannot certify `[(0,0),(0,0)]`.

**Classification:** note — pass negative.

### Probe 29 — zero-node operational block step

**Command:** expected-failure check of `R8ZeroDerivationOperationalStepNegative.idr`.

**Result:** exit 1; `FiniteAdjacentSwapDone` does not inhabit the required `WholeBlockSwapDerivation` field.

**Classification:** note — pass negative.

### Probe 30 — arbitrary identity-root substitution

**Command:** expected-failure check of new `R8BlockPrefixIdentityNegative.idr`, attempting to reuse labels indexed by an arbitrary source-to-source correspondence where whole-block labels require the concrete identity constructor.

**Result:** exit 1 with mismatch between `alternateRoot` and the fully reduced identity `MkActionRegistrationReplayCorrespondence ...`.

**Classification:** note — pass negative. The fold root is definitionally fixed.

### Probe 31 — nontrivial one-trace authentication producer search

**Command:** search the exact external source and all staged/prior probe modules for constructor uses of `MkDeletionChainStep`, `MkClosingFreeReduction`, `MkOneTraceOrchestrationAccounting`, and `MkCanonicalRegistrationCorrespondence` outside their declarations.

**Result:** no concrete constructor use exists. In particular, there is no checked trace with two generated registrations and one withdrawal that runs deletion → sorting → canonical-tree construction and supplies the new strong occurrence equality. The existing scanner fixtures operate only on abstract registration-index events, not `Transitions` or one-trace accounting.

**Classification:** major derivability risk — the strong interface is consistent at declaration level and the exact assembler projects correctly, but no nontrivial actual producer path validates that O16 can derive exact dependent occurrence equality after deletion and sorting. This is not a counterexample because O16 is explicitly a hole, but Phase F cannot be treated as calibrated.

### Probe 32 — retained old pure-certificate pollution

**Command:** expected-failure check of `R6OldPollutionNegative.idr` against revision 8.

**Result:** exit 1 at pure `CertifiedActorPermutation` versus sealed `CertifiedOperationalCanonicalPermutation`.

**Classification:** note — pass negative.

### Probe 33 — retained outer sealed-package pollution

**Command:** expected-failure check of `R6OuterPollutionNegative.idr`.

**Result:** exit 1; the old operational realization cannot be reindexed under a swap/inverse-polluted outer certificate.

**Classification:** note — pass negative.

### Probe 34 — retained current-state safety detachment

**Command:** expected-failure check of `R6SafetyDetachmentNegative.idr`.

**Result:** exit 1; exact trace/blocks/premises indices prevent detaching safety to another current state.

**Classification:** note — pass negative.

### Probe 35 — retained generated-child licensing rejection

**Command:** positive check of `R6GeneratedChildSafetyPositive.idr`.

**Result:** exit 0 at `169/169`; a headed generated-child insertion contradicts `NoGeneratedChild` before O20.

**Classification:** note — pass positive.

### Probe 36 — retained wrong operational bridge trace

**Command:** expected-failure check of `R8WrongTraceBridgeNegative.idr`.

**Result:** exit 1 at exact operational target final versus `otherFinal`; a convergence bridge cannot detach to another replayed trace.

**Classification:** note — pass negative.

### Probe 37 — retained wrong occurrence relation

**Command:** expected-failure check of `R8WrongOccurrenceBridgeNegative.idr`.

**Result:** exit 1 with exact mismatch between occurrence correspondences `first` and `second`.

**Classification:** note — pass negative.

### Probe 38 — retained stale quotient

**Command:** expected-failure check of `R6StaleQuotientNegative.idr`.

**Result:** exit 1; an endpoint quotient indexed by `firstOp` cannot be reused under `secondOp`.

**Classification:** note — pass negative.

### Probe 39 — retained mixed enriched schedule

**Command:** expected-failure check of `R6MixedScheduleNegative.idr`.

**Result:** exit 1 with `leftCapital` versus `otherLeft`; O21 cannot substitute an unrelated enriched schedule.

**Classification:** note — pass negative.

### Probe 40 — first two concrete scanner orderings

**Command:** positive check of `R6ScannerRetainedFixturesPositive.idr`.

**Result:** exit 0 at `168/168`; both orderings expose identical exact final index values and deleted-generation lists.

**Classification:** note — pass positive.

### Probe 41 — third concrete scanner ordering

**Command:** positive check of `R6ScannerThirdOrdering.idr` (L6,R9,R14,L18).

**Result:** exit 0 at `168/168`; it reaches the same full indexes and exact deleted lists.

**Classification:** note — pass positive.

### Probe 42 — wrong scanner generation

**Command:** expected-failure check of `R6ScannerWrongGenerationNegative.idr`.

**Result:** exit 1 with birth-ordinal mismatch `12` versus `0`; same raw name cannot conflate generations.

**Classification:** note — pass negative.

### Probe 43 — one/moved-intermediate static variants

**Command:** positive check of `R6FourFiberStatic.idr`.

**Result:** exit 0 at `169/169`; static one/moved-intermediate and licensing-parent exclusion artifacts remain valid, without claiming a reachable O19/O20 run.

**Classification:** note — pass positive.

### Probe 44 — two-intermediate static variant

**Command:** positive check of `R6TwoIntermediateStatic.idr`.

**Result:** exit 0 at `169/169`; the two withdrawn-intermediate static/interface model remains valid.

**Classification:** note — pass positive.

### Probe 45 — source-sensitive O/A application

**Command:** positive check of retained `R4OADiamondApplication.idr`.

**Result:** exit 0 at `32/32`; the O-then-A local theorem remains externally applicable at its source-sensitive indices.

**Classification:** note — pass positive.

### Probe 46 — two-step occurrence composition

**Command:** positive check of `R6OccurrenceFoldPositive.idr`.

**Result:** exit 0 at `32/32`; action and generated-registration origins compose in the advertised direction.

**Classification:** note — pass positive.

### Probe 47 — recursive operational occurrence fold

**Command:** positive check of `R6OperationalOccurrenceFoldPositive.idr`.

**Result:** exit 0 at `169/169`; step/rest occurrence maps compose through operational actor recursion.

**Classification:** note — pass positive.

### Probe 48 — vestigial simultaneous assembly

**Command:** positive check of adapted `R4VestigialSimultaneous.idr`.

**Result:** exit 0 at `167/167`; the assembler consumes the newly authenticated accounting and retains an original-present/reduced-absent retired clean child.

**Classification:** note — pass positive at the abstract-capital boundary.

### Probe 49 — accepted scanner-capital consumers

**Command:** positive check of `R4ScannerProducerConsumers.idr`.

**Result:** exit 0 at `168/168`; exact accepted correspondence and both withdrawal-to-deleted-list projections require no external scanner premise.

**Classification:** note — pass positive.

### Probe 50 — independently callable deletion boundaries

**Command:** positive check of `R7DeletionBoundariesPositive.idr`.

**Result:** exit 0 at `166/166`; O7 scan, O8 selector, O9 enriched step, O10 core, O11 accounting, and complete compatibility wrappers remain externally composable.

**Classification:** note — pass positive.

### Probe 51 — operational current-state threading

**Command:** positive check of `R7OperationalThreadingPositive.idr`.

**Result:** exit 0 at `169/169`; a strengthened whole-block step threads its exact target trace, blocks, and premise bundle into recursion.

**Classification:** note — pass positive.

### Probe 52 — immutable outer schedules

**Command:** positive check of `R6OuterSchedulesPositive.idr`.

**Result:** exit 0 at `169/169`; the immutable result retains the exact original left/right canonical schedule values.

**Classification:** note — pass positive.

### Probe 53 — full producer/consumer pipeline

**Command:** positive check of `R8FullPipeline.idr`.

**Result:** exit 0 at `169/169`. Starting only from the two upstream `CanonicalizationPremises` bundles and `SameOrchestrationModuloGenerated`, the wrapper composes deletion, sorting, exact accounting/authentication, enriched capitals, O19, O20, authenticated O21 bridge/scanner composition, and the immutable `ConfluenceResult`. No extra external premise is introduced.

**Classification:** note — pass composition. All hard producers remain named holes, and Probe 15 shows the public enriched type is wider than the intended producer image.

### Probe 54 — exact named-hole inventory

**Command:** regex-scan the five exact research spikes for unique `?*_rhs` identifiers and independently list every question-mark identifier.

**Result:** exact split is canonical 6, cross 4, deletion 10, local 8, renaming 2; total and global uniqueness are both 30. No extra question-mark identifier exists in the five modules.

**Classification:** note — pass count.

### Probe 55 — forward/reverse O1–O23 reconciliation

**Command:** map every hole from Probe 54 to its declaration/output type, then reverse-check every obligation row in the plan.

**Result:** the published numerical mapping is exact:

- O1=5, O2=2, O3=1, O4=2, O5=1, O6=2;
- O7–O12 each=1; O13=0; O14–O18 each=1;
- O19=2, O20=1, O21=3, O22=0, O23=0.

O9/O10/O11 outputs retain deletion occurrence provenance; O17 retains sorting occurrence provenance; O16's one hole must construct the strong fold-indexed authentication; O18's hole consumes the accounting and the complete assembler carries its map. No new top-level hole was silently added.

However, Probe 15 exposes missing *interface work* rather than a hidden hole count: the O18 output type forgets the O16 reduction/sorting provenance and accepts a coherently forged pair through its public constructor. Repairing that output/index is not represented by a new hole today.

**Classification:** major estimate/scope caveat — count/reverse mapping passes syntactically, but authentication laundering is hidden in the strength of O18's output rather than charged as an obligation.

### Probe 56 — phase arithmetic and grade credibility

**Command:** parse all eight phase rows and sum endpoints; verify all three mandatory gate phrases.

**Result:** rows are A 4–8, B 18–31, C 10–18, D 10–19, E 7–13, F 12–21, G 31–48, H 2–5; raw sum is exactly **94–163**, with no overlap deduction. All three gates are present.

Arithmetic passes. Grade credibility does not: B's only nontrivial 2×2 check assumes the recursive authenticated labels and Probe 27 leaves the selected-block disjoint-range argument uncalibrated; F has no concrete two-generation/one-withdrawal producer; G consumes an enriched type that Probe 15 can coherently forge, so its bridge proof burden is understated until provenance is sealed/indexed.

**Classification:** major — exact arithmetic, not authorization-ready grading.

### Probe 57 — exact release package build, cache-backed pass

**Command:** copy the full TTC cache whose 207 production sources were byte-compared to the exact archived release, then run `idris2 --build dgamma.ipkg` in `/tmp/thm73-review8-probes/release`.

**Result:** exit 0 with no rebuild lines because every package module was current in the exact cache. The first ad-hoc line parser undercounted the multiline `modules` stanza and is not used as evidence.

**Classification:** note — package pass, but a freshly rebuilt terminal module and correct graph count are still required.

### Probe 58 — exact 207/207 external release build

**Command:** correctly parse the multiline package stanza (207 modules), delete the exact cache's `CP4ProgressProof` TTC/TTM, and rerun `idris2 --build dgamma.ipkg`.

**Result:** exit 0 with `207/207: Building DGamma.CP4ProgressProof`. The exact release graph passes and its terminal proof module was freshly elaborated.

**Classification:** note — pass.

### Probe 59 — escape/reachability/immutability and repository hygiene, first scan

**Command:** scan production for named holes/escapes/partial defaults, package sources for research reachability, research for non-hole escapes; then inspect CP3 blob, HEAD, status, staged/tracked diffs, and active Idris processes.

**Result:** all hygiene checks pass except the naive case-insensitive word scan reports one `postulate` token at `CP3.idr:745`. Inspection shows it is documentation text: “no postulate or escape hatch is used,” not a declaration. CP3 blob/head are exact; no research reachability or research non-hole escape exists; no staged/tracked change and no active Idris process exists. Worktree contains only pre-existing untracked `paper/` and this mandated report.

**Classification:** note — one scanner false positive; corrected source-aware rescan required.

### Probe 60 — corrected source-aware hygiene scan

**Command:** strip Idris line/doc/block comments before scanning code; recheck release diff, tracked worktree, and index counts.

**Result:** production forbidden-code count 0; research non-hole escape count 0; research reachability remains empty; `git diff 34b21c9..2c40827 -- src dgamma.ipkg` exits 0; tracked worktree and staged counts are both 0.

**Classification:** note — hygiene pass.

### Probe 61 — round-7 CP3 tree and public-schedule forgery constructions

**Command:** extract the first two checked constructions from round-7 Probe 27 into `R8PublicTreeForgeryStillPositive.idr` and run against the exact revision-8 types.

**Result:** exit 0 at `168/168`. A no-withdrawal CP3 tree can still be composed with a generation-preserving original-occurrence permutation, and an alternate tree can still be installed in a public `CanonicalSchedule` while reusing all other fields. Probe 20 correctly prevents that public schedule alone from entering the bridge; Probe 16 prevents tree-only enriched cloning; Probe 15 shows coherent tree+map enriched cloning remains possible.

**Classification:** note for the immutable/public layers; blocker evidence when combined with Probe 15's enriched repackage.

### Probe 62 — nontrivial exactly-two occurrence permutation core

**Command:** adapt and check round-7 Probe 29 against the revision-8 public permutation module.

**Result:** exit 0 at `169/169`. For a dependent generated-occurrence family known to contain exactly two births with distinct generation ordinals, the swap is involutive and genuinely exchanges both generations. This remains conditional occurrence algebra, not a concrete reachable canonical trace fixture.

**Classification:** blocker-supporting evidence for Probe 15; major derivability caveat remains for concrete reachability.

### Probe 63 — coherently forged enriched capital at the bridge, first attempt

**Command:** extend `R8CoherentPairForgeryPositive.idr` with a complete bridge constructor whose left input is the coherently repackaged capital, then check it.

**Result:** probe fails on missing direct `DGamma.Metatheory` scope for `effectTables`, followed by a constructor-inference cascade.

**Classification:** note — probe import failure; no interface conclusion yet.

### Probe 64 — coherently forged capital at bridge, retry

**Command:** add the direct metatheory import and rerun.

**Result:** the bridge signature used an occurrence correspondence indexed by the old capital's projection; opaque projection reduction did not identify that final-state index with the forged capital's projection.

**Classification:** note — probe index formulation failure; retry with correspondence explicitly indexed by the forged capital.

### Probe 65 — coherently forged enriched capital is accepted by the bridge

**Command:** move the forged capital into the dependent telescope and index the replay correspondence directly by `canonicalTrace (canonicalSchedule forged)`; rerun.

**Result:** exit 0 at `168/168`. With ordinary endpoint/table/control fields and the bridge's own accepted-generation match function, the coherent synthetic capital is a valid left input. No deletion reduction, support ordering, sorted trace, or one-trace accounting value appears at the bridge consumer.

**Classification:** blocker — confirms Probe 15 is not merely a standalone record repackage; the forged enriched pair reaches the repaired bridge interface.

### Probe 66 — exact source anchors for findings

**Command:** line-numbered inspection of canonical authentication/accounting/capital, action correspondence, bridge, block-label fold, whole-block wrapper, and plan estimate/hole tables.

**Result:** principal anchors are:

- `CP5ConfluenceLocalDiamondSpike.idr:146–172` — generated origin is an independent public record field constrained only by its generation-bijection equation;
- `CP5ConfluenceCanonicalSortSpike.idr:205–221` — strong pair-relative equality;
- `...CanonicalSortSpike.idr:226–269` — exact fold and genuinely pinned one-trace accounting;
- `...CanonicalSortSpike.idr:293–312` — public enriched capital stores only an arbitrary correspondence plus pair-relative authentication, with no reduction/sorted index;
- `...RenamingCompositionSpike.idr:125–182` — bridge consumes that enriched capital and its stored occurrence map;
- `...CrossTraceSpike.idr:150–172,293–350,356–383` — ordinal labels, exact prefix composition, and identity-root whole-block wrapper;
- `THM73-PLAN.md:269–309` — exact 30-hole and 94–163 tables.

**Classification:** note — anchors recorded.

### Probe 67 — final repository state before closure

**Command:** inspect branch/HEAD/CP3 blob, status, staged and tracked-worktree counts, active Idris processes, and report presence.

**Result:** branch/head and CP3 remain exact; staged count 0; tracked worktree count 0; no Idris process remains. Only pre-existing untracked `paper/` and this mandated report are present.

**Classification:** note — hygiene pass.

## Claimed-fix disposition

| # | Revision-8 claim | Checked disposition |
|---:|---|---|
| 1 | Strong authenticated canonical map tied to exact deletion+sorting fold | **Pinned in `OneTraceOrchestrationAccounting`, then forgotten.** Probe 19 confirms the accounting index. Probes 15/65 construct an internally coherent alternate `(tree, generated-origin map)` enriched capital and feed it to the bridge without any reduction/order/sorted/accounting value. |
| 2 | Enriched-capital-only bridge blocks public forgery | **Narrowly true, globally false.** Public schedule rejection, tree-only enriched clone rejection, actual direction, and fixed-capital wrong birth all pass. A coherently forged enriched capital nevertheless has the accepted input type and reaches the bridge. |
| 3 | Occurrence-authenticated Cartesian labels | **Substantial repair, incomplete calibration.** Action/tag authority is gone; fixed-block 0→1, arbitrary root, zero-node, and literal duplicate attacks fail; 1×1/2×1/2×2 wrappers pass. But generated/action halves of the underlying correspondence are not coherent, coordinate aliases transport across changed blocks, and nontrivial positives assume the recursive label fold rather than build it. |
| 4 | Exactly 30 holes and 94–163 | **Counts/arithmetic pass exactly.** Grade readiness fails because the O18 output provenance defect and absence of nontrivial O16/O6 producer fixtures are not calibrated. |
| 5 | Prior suite retained | **Pass at tested boundaries.** All requested pollution, detachment, scanner, static, O/A, occurrence-fold, deletion-boundary, threading, outer-schedule, and full-pipeline checks were rerun serially. |

## Numbered findings

1. **blocker — O16 fold provenance is lost at the public O18 output, and a coherent synthetic pair reaches the bridge** (`CP5ConfluenceCanonicalSortSpike.idr:226–269,293–312`; `CP5ConfluenceRenamingCompositionSpike.idr:125–182`). `OneTraceOrchestrationAccounting` is correctly indexed by the exact reduction/order/sorted values and its authentication uses the definitional deletion+sorting fold (Probe 19). `IndependentCanonicalSchedule`, however, stores only an arbitrary `ActionRegistrationReplayCorrespondence` and a proof that its CP3 tree agrees with that arbitrary map. It carries no reduction, ordering, sorted result, accounting value, or equality tying its field to one. `replaceCapitalWithCoherentPair` typechecks while changing the tree and generated-origin map together and reusing all other fields (Probe 15); `coherentPairCanEnterBridge` then typechecks at the exact repaired bridge input (Probe 65). Therefore the statement in the plan that enriched consumers compare *producer-authenticated deletion/sorting origins* is stronger than the actual consumer types.

2. **blocker — generated-registration origins are independently replaceable from all-action origins** (`CP5ConfluenceLocalDiamondSpike.idr:146–172`). The public correspondence record has separate `replayActionOrigin` and `replayGeneratedRegistrationOrigin` fields but no law connecting an O-Insert's generated occurrence to the same located action occurrence. `retargetGeneratedOrigins` is a checked constructor that leaves the full action-origin map and tag preservation untouched while replacing only generated origins under any generation bijection/ordinal equation (Probe 15). Node-label authentication uses the action half; canonical-map authentication and the bridge use the generated half. Thus “the occurrence correspondence” is not one coherent occurrence map, making the laundering attack materially cheaper and leaving the block/bridge uses capable of referring to different original occurrences.

3. **major — selected-block coordinate injectivity is not calibrated by the positive wrappers** (`CP5ConfluenceCrossTraceSpike.idr:150–172,293–350,356–390`). The fixed-block same-node 0→1 attack fails and fold/root indices are genuinely stronger. Yet `R8BlockStartAliasingPositive` checks that the same node transports from `(start=1,pos=1)` to `(start=2,pos=0)` whenever two located-block prefix equations provide the equal global ordinal. The whole wrapper should rule this out through its exact selected blocks, bounds, and `BlockBefore`; no checked lemma actually derives disjoint ordinal ranges. Moreover the 2×1/2×2 positives receive `DerivationCrossesBlockPositions` as a premise instead of constructing it from concrete `AdjacentSwapResult` nodes. This is a derivability/producer risk, not a demonstrated whole-wrapper forgery.

4. **major — the strong O16 authentication has no nontrivial producer calibration.** No source or probe constructs a concrete deletion step, closing-free reduction, one-trace accounting, or CP3 canonical tree. Consequently there is no two-generation/one-withdrawal trace showing that deletion → sorting can prove exact dependent occurrence equality. Abstract assembly and projections pass, but the first actual O16 proof may expose over-strength or missing coherence capital.

5. **major — the 94–163 sum is exact but the phase grades are not proof-grind ready** (`THM73-PLAN.md:296–309`). Phase B assumes the hard recursive Cartesian labels in its nontrivial positives; Phase F lacks the required nontrivial authentication fixture; Phase G consumes the forgeable O18 output. The repaired types must be re-probed before B/F/G can be defended. No replacement numeric range is justified by the available evidence.

## Positive results / non-findings

- Immutable `confluenceTheorem` production target remains CP3 blob `2c697e532e83989de8591fa6a4378747c6a501c0`; production/package diff from `34b21c9` is empty.
- All five research spikes were freshly checked at their terminal modules; exact release build reaches 207/207.
- Production/reachable code has no named holes, `believe_me`, `assert_total`, postulate declaration, or `%default partial`; research is package-unreachable and has no non-hole escape.
- Exact hole split is 6/4/10/8/2 = 30, with the published reverse O1–O23 count.
- Tree-only enriched cloning and arbitrary public schedules do fail before the bridge; actual bridge direction and fixed-capital wrong-birth rejection pass.
- Direct same-block relabeling, arbitrary identity-root substitution, zero-node operational steps, and literal duplicate pairs fail.
- 1×1, 2×1, and 2×2 whole-block wrappers elaborate with exact counts; no action/tag authority remains.
- Full intended producer/consumer pipeline reaches immutable `ConfluenceResult` from upstream bundles only.
- Exact scanner generation/order fixtures and every requested retained boundary pass.

## Residual risks

- All 30 hard research bodies remain holes by design; type elaboration is not theorem proof.
- The universal sealed O19 operational selector for withdrawn-intermediate schedules remains unproved.
- O/A and O/O applicability and both accepted scanner inductions remain XL mathematical gates.
- The exact-two occurrence permutation is checked conditionally, not instantiated by a reachable canonical trace.
- Static one/moved/two-intermediate models remain interface fixtures, not concrete O19/O20 executions.
- First deletion checks hit timeout/SIGKILL resource noise; exact cache seeding followed by fresh target elaboration passed.
- Worktree intentionally contains untracked `paper/` and this report; tracked paths and index are clean.

## Estimate assessment

- **Arithmetic:** PASS — exact raw 94–163, no overlap subtraction.
- **Hole reconciliation:** PASS numerically — exactly 30 and exact reverse O-map.
- **Gates:** present and concrete in prose.
- **Grade credibility:** FAIL for authorization. B needs a real recursive 2×2/repeated-Iter label construction and selected-block no-alias lemma; F needs a real two-generation/one-withdrawal authentication producer; G needs a producer-indexed/sealed enriched capital and bridge regression. Re-estimate only after those interfaces and fixtures elaborate.

## Exact changes required for round 9

1. **Preserve producer provenance in the bridge-facing capital.** Make `IndependentCanonicalSchedule` (or a new sealed bridge-facing wrapper) carry the exact `reduction`, `ordering`, `sorted`, and `OneTraceOrchestrationAccounting` values and definitionally derive its occurrence correspondence as `deletionSortingOccurrenceCorrespondence reduction sorted`; remove the free occurrence-map field from the trusted consumer boundary. A coherent `(tree,map)` pair without the exact producer chain must fail before O19/O20/O21.
2. **Unify generated and all-action occurrence origins.** Add a conversion from `LocatedGeneratedRegistration` to its exact `LocatedActionOccurrence (OInsert child (ChildOf parent) component)` and require the correspondence's generated origin to equal the converted `replayActionOrigin` result. `retargetGeneratedOrigins` must fail unless the all-action map changes coherently too.
3. **Repeat all three forgery negatives at the new sealed/indexed type.** Public schedule, tree-only enriched clone, and coherent tree+map clone must each fail before the bridge; retain actual-direction and fixed-capital wrong-birth/wrong-generation positives/negatives.
4. **Close the block-coordinate calibration gap.** Provide a checked lemma that the two authoritative selected `BlockBefore` ranges are disjoint and that bounded `(block,position)` coordinates are injective; add a shifted-block-start/compensating-position negative at the whole-wrapper boundary. Supply an actual recursive two-node/four-node label fold, not only a wrapper consuming prebuilt labels.
5. **Add a nontrivial one-trace producer fixture.** At minimum: two generated registrations, one withdrawal, deletion occurrence fold, sorting occurrence fold, CP3 tree, and exact strong authentication, all checked without assuming `OneTraceOrchestrationAccounting` itself.
6. **Reconcile and re-estimate after the type changes.** Keep the exact forward/reverse hole table, but account for any new producer/sealing/coherence work in O1/O16/O18/O20 and phases A/B/F/G.
7. **Retain closure/hygiene.** Re-run all five spikes, the complete negative/scanner/static/pipeline suite, exact CP3/source diff, research isolation, 207/207 external build, and clean tracked/index checks.

## Final verdict

**REJECT.** Revision 8 genuinely fixes tree-only cloning, public-schedule bridge entry, fixed-block repeated-action relabeling, prefix authority, and the retained regression front. It is not ready for the proof grind: the exact fold authentication is discarded at the public enriched output, a coherent caller-controlled tree/generated-origin pair can be repackaged and accepted by the bridge, and the generated/action halves of the occurrence correspondence have no coherence law.

**Final verdict: REJECT**
