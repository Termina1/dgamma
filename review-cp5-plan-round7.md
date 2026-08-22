# Theorem 73 Scoping Plan — Adversarial Review Round 7

- Reviewer: fresh-context adversarial reviewer
- Target branch/commit: `cp5-thm73-scoping` / `139237a`
- Review date: 2026-03-09

## Probe log (append-only)

### Probe 1 — repository identity and initial worktree

Command: `git branch --show-current && git rev-parse HEAD && git status --short`
```
cp5-thm73-scoping
139237a1dd714b9cf55b3f4c10d19cee79484e59
?? paper/
?? review-cp5-plan-round7.md
```
Result: PASS. Branch and commit match the requested target. Only pre-existing untracked `paper/` plus this permitted report are present.

Classification: **note** — no tracked worktree changes at start.

### Probe 2 — prior-report inventory and size

Command: `wc -l review-cp5-plan-round{1..6}.md THM73-PLAN.md`
```
     146 review-cp5-plan-round1.md
     157 review-cp5-plan-round2.md
     227 review-cp5-plan-round3.md
     432 review-cp5-plan-round4.md
     369 review-cp5-plan-round5.md
     826 review-cp5-plan-round6.md
     325 THM73-PLAN.md
    2482 total
```
Result: PASS. All six prior reports and current plan are present.

Classification: **note**.

### Probe 3 — read prior report round 1 in full

Command: `read review-cp5-plan-round1.md`

Result: PASS. Extracted the original interface-gap front: replay independence, local diamonds, O/O swaps, original-endpoint support transport, cross-trace capital, and exact endpoint bridge.

Classification: **note** — documentary baseline only.

### Probe 4 — read prior report round 2 in full

Command: `read review-cp5-plan-round2.md`

Result: PASS. Recorded the second-round blockers: missing O/A orientation, over-strong unrestricted support-path transports, opaque enriched schedule endpoint, dropped replay bundle, and missing typed scanner deletion links.

Classification: **note** — documentary baseline only.

### Probe 5 — read prior report round 3 in full

Command: `read review-cp5-plan-round3.md`

Result: PASS. Recorded the third-round front: left-operational permutation state/namespace, operational result coupling, scanner-capital producer, and exact classification/scanner linkage.

Classification: **note** — documentary baseline only.

### Probe 6 — read prior report round 4 in full

Command: `read review-cp5-plan-round4.md`

Result: PASS. Recorded the checked intermediate-vestigial countermodel and the requirement to replace full support-path transport with an operational/local crossing relation; scanner producer and endpoint coupling were otherwise accepted.

Classification: **note** — documentary baseline only.

### Probe 7 — read prior report round 5 in full

Command: `read review-cp5-plan-round5.md`

Result: PASS. Recorded certificate pollution, absent one-step operational derivation, lost generated-birth occurrence capital, weak scanner interleaving fixture, and estimate arithmetic issues.

Classification: **note** — documentary baseline only.

### Probe 8 — read prior report round 6 in full

Command: `read review-cp5-plan-round6.md` (two paginated reads)

Result: PASS. The exact round-7 attack front is reconstructed: accepted-generation bridge equation and canonical-map authenticity, concrete nonempty Cartesian block crossing, independently callable O7–O11 boundaries, retained complete negative/scanner suites, and bidirectional 30-hole reconciliation.

Classification: **note** — documentary baseline only.

### Probe 9 — immutable production delta and CP3 target

Command: `git diff --exit-code 34b21c9..139237a -- src dgamma.ipkg; git rev-parse 139237a:src/DGamma/CP3.idr; git hash-object src/DGamma/CP3.idr`
```
diff_exit=0
target_blob=2c697e532e83989de8591fa6a4378747c6a501c0
worktree_blob=2c697e532e83989de8591fa6a4378747c6a501c0
```
Result: PASS. Required production diff is empty and CP3 has the immutable blob.

Classification: **note**.

### Probe 10 — revision-7 change surface

Command: `git diff --stat/name-status b220287..139237a; git log --oneline b220287..139237a`
```
 THM73-PLAN.md                                      | 495 ++++++------
 research/DGamma/CP5ConfluenceCrossTraceSpike.idr   | 163 +++-
 .../DGamma/CP5ConfluenceDeletionChainSpike.idr     | 180 ++++-
 research/DGamma/CP5ConfluenceLocalDiamondSpike.idr |  58 ++
 .../CP5ConfluenceRenamingCompositionSpike.idr      |  62 +-
 review-cp5-plan-round6.md                          | 826 +++++++++++++++++++++
 6 files changed, 1524 insertions(+), 260 deletions(-)
M	THM73-PLAN.md
M	research/DGamma/CP5ConfluenceCrossTraceSpike.idr
M	research/DGamma/CP5ConfluenceDeletionChainSpike.idr
M	research/DGamma/CP5ConfluenceLocalDiamondSpike.idr
M	research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
A	review-cp5-plan-round6.md
139237a Revise Theorem 73 plan after round 6
fee3278 Expose executable CP5 deletion scanner handles
7df16cc Split CP5 deletion scan selection and accounting gates
0b208ab Index CP5 whole-block swaps by Cartesian crossings
06758cf Require nonempty CP5 adjacent derivation heads
26e6663 Couple CP5 bridge matches by accepted generation
6af04b6 Record CP5 plan adversarial review round 6
```
Result: PASS. Revision 7 changes the plan plus canonical-sort, cross-trace, deletion-chain, local-diamond, and renaming spike files, and records round 6; production is untouched.

Classification: **note**.

### Probe 11 — read revision-7 plan in full

Command: `read THM73-PLAN.md`

Result: PASS as an inventory. The plan claims exact 30-hole mapping, five deletion producers, a generation-forward bridge over `canonicalToOriginal`, Cartesian whole-block evidence, and raw 82–142. None is accepted from prose; the following probes target their actual types.

Classification: **note**.

### Probe 12 — exact external release and spike trees

Command: `git archive 139237a` to `/tmp/thm73-review7-probes/release`; copy release `src` plus exactly five spikes to `spikes/src`; hash/count/preflight
```
release_idris_files=207
spike_tree_idris_files=212
release_cp3=2c697e532e83989de8591fa6a4378747c6a501c0
spike_cp3=2c697e532e83989de8591fa6a4378747c6a501c0
active_idris=none
```
Result: PASS. Exact immutable external trees are established; five research modules are added only in the spike tree.

Classification: **note**.

### Probe 13 — full local-diamond interface inspection

Command: `read research/DGamma/CP5ConfluenceLocalDiamondSpike.idr`

Result: PASS as declaration inventory. `NonEmptyFiniteAdjacentSwapDerivation` exposes a first real node; tail termination remains finite. Replay and action/registration folds are complete. Cartesian block indexing is downstream in the cross-trace module and must be attacked there.

Classification: **note**.

### Probe 14 — cross-trace whole-block interface inspection

Command: `read research/DGamma/CP5ConfluenceCrossTraceSpike.idr`

Result: Declaration inventory complete. The strengthened record ties one label pair to each finite derivation node, enforces in-bounds coverage/unique label pairs/count, and indexes source blocks/safety. Attack hypothesis: `TraceActionTagAt` identifies only action and tag—not occurrence identity—so repeated identical steps may let a concrete node be mislabeled as another selected-block position. This must be tested with checked probes.

Classification: **major attack hypothesis**, pending elaboration.

### Probe 15 — bridge/scanner and deletion/canonical producer inspection

Command: full reads of `CP5ConfluenceRenamingCompositionSpike.idr`, `CP5ConfluenceDeletionChainSpike.idr`, and `CP5ConfluenceCanonicalSortSpike.idr`

Result: The five new deletion producers are separately declared and both compatibility wrappers have complete bodies. The bridge equation is syntactically over original occurrences through each schedule's `canonicalRegistrationTree`. New attack hypothesis: immutable `CanonicalRegistrationCorrespondence` constrains `canonicalToOriginal` only as a generation-level bijection/accounting map among same-action occurrences; it may permit a synthetic schedule to permute repeated generations and thereby satisfy the bridge equation with the wrong canonical occurrence. A generic checked schedule-tree permutation probe is required.

Classification: **major attack hypothesis**, pending probe.

### Probe 16 — local-diamond spike elaboration

Command: `idris2 --source-dir src --check src/DGamma/CP5ConfluenceLocalDiamondSpike.idr` in external spike tree
```
20/31: Building DGamma.CP4DeletionFilterSuccess (src/DGamma/CP4DeletionFilterSuccess.idr)
21/31: Building DGamma.CP4DeletionReadiness (src/DGamma/CP4DeletionReadiness.idr)
22/31: Building DGamma.CP4DeletionInactiveInvariant (src/DGamma/CP4DeletionInactiveInvariant.idr)
23/31: Building DGamma.CP4DeletionPlanBoundary (src/DGamma/CP4DeletionPlanBoundary.idr)
24/31: Building DGamma.CP4DeletionChildlessInvariant (src/DGamma/CP4DeletionChildlessInvariant.idr)
25/31: Building DGamma.CP4DeletionPlanComplete (src/DGamma/CP4DeletionPlanComplete.idr)
26/31: Building DGamma.CP4DeletionRetainedAction (src/DGamma/CP4DeletionRetainedAction.idr)
27/31: Building DGamma.CP4RuntimeBindings (src/DGamma/CP4RuntimeBindings.idr)
28/31: Building DGamma.CP4DeletionNoEpisodeReplay (src/DGamma/CP4DeletionNoEpisodeReplay.idr)
29/31: Building DGamma.CP4DeletionRelationalBoundary (src/DGamma/CP4DeletionRelationalBoundary.idr)
30/31: Building DGamma.CP4Support (src/DGamma/CP4Support.idr)
31/31: Building DGamma.CP5ConfluenceLocalDiamondSpike (src/DGamma/CP5ConfluenceLocalDiamondSpike.idr)
exit=0
```
Result: PASS. Local/finite/nonempty declaration closure elaborates.

Classification: **note**.

### Probe 17 — deletion-chain spike elaboration

Command: `idris2 --source-dir src --check src/DGamma/CP5ConfluenceDeletionChainSpike.idr` in external spike tree
```

152/165: Building DGamma.CP4DeletionSelectedForeignLifecycleReplay (src/DGamma/CP4DeletionSelectedForeignLifecycleReplay.idr)
153/165: Building DGamma.CP4DeletionSelectedOwnDispatch (src/DGamma/CP4DeletionSelectedOwnDispatch.idr)
154/165: Building DGamma.CP4DeletionSelectedEpisodeReplay (src/DGamma/CP4DeletionSelectedEpisodeReplay.idr)
155/165: Building DGamma.CP4DeletionCommittedProviderPersistence (src/DGamma/CP4DeletionCommittedProviderPersistence.idr)
156/165: Building DGamma.CP4DeletionSelectedForeignLifecycleCrossing (src/DGamma/CP4DeletionSelectedForeignLifecycleCrossing.idr)
157/165: Building DGamma.CP4DeletionSelectedEpisodeAnchors (src/DGamma/CP4DeletionSelectedEpisodeAnchors.idr)
158/165: Building DGamma.CP4DeletionSelectedStart (src/DGamma/CP4DeletionSelectedStart.idr)
159/165: Building DGamma.CP4DeletionSelectedEpisodeFold (src/DGamma/CP4DeletionSelectedEpisodeFold.idr)
160/165: Building DGamma.CP4DeletionWithdrawalCurrent (src/DGamma/CP4DeletionWithdrawalCurrent.idr)
161/165: Building DGamma.CP4DeletionRetirementPersistence (src/DGamma/CP4DeletionRetirementPersistence.idr)
162/165: Building DGamma.CP4DeletionWithdrawalJoin (src/DGamma/CP4DeletionWithdrawalJoin.idr)
163/165: Building DGamma.CP4DeletionTheorem (src/DGamma/CP4DeletionTheorem.idr)
165/165: Building DGamma.CP5ConfluenceDeletionChainSpike (src/DGamma/CP5ConfluenceDeletionChainSpike.idr)
exit=0
```
Result: PASS. All split scan/selection/enrichment/core/accounting signatures and complete wrappers elaborate.

Classification: **note**.

### Probe 18 — canonical-sort spike elaboration

Command: external serial `idris2 --check CP5ConfluenceCanonicalSortSpike.idr`
```
166/166: Building DGamma.CP5ConfluenceCanonicalSortSpike (src/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
exit=0
```
Result: PASS.

Classification: **note**.

### Probe 19 — bridge/scanner spike elaboration

Command: external serial `idris2 --check CP5ConfluenceRenamingCompositionSpike.idr`
```
167/167: Building DGamma.CP5ConfluenceRenamingCompositionSpike (src/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
exit=0
```
Result: PASS. New schedule-indexed bridge equation elaborates.

Classification: **note**.

### Probe 20 — cross-trace/whole-block spike elaboration

Command: external serial `idris2 --check CP5ConfluenceCrossTraceSpike.idr`
```
 684 | 0 permutationOccurrenceCorrespondence :
 685 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 686 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 687 |       rightCapital matching} ->
 688 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 689 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->

exit=0
```
Result: PASS. `WholeBlockSwapDerivation` and bridge-consuming convergence interfaces elaborate.

Classification: **note**.

### Probe 21 — prior external-probe artifact inventory

Command: `find /tmp/thm73-review6-probes -name R6*.idr`
```
/tmp/thm73-review6-probes/spikes/src/DGamma/R6BridgeRightOccurrencePollution.idr
/tmp/thm73-review6-probes/spikes/src/DGamma/R6BridgeSourcePositive.idr
/tmp/thm73-review6-probes/spikes/src/DGamma/R6FourFiberStatic.idr
/tmp/thm73-review6-probes/spikes/src/DGamma/R6FullPipeline.idr
/tmp/thm73-review6-probes/spikes/src/DGamma/R6GeneratedChildSafetyPositive.idr
/tmp/thm73-review6-probes/spikes/src/DGamma/R6MixedScheduleNegative.idr
/tmp/thm73-review6-probes/spikes/src/DGamma/R6OccurrenceFoldPositive.idr
/tmp/thm73-review6-probes/spikes/src/DGamma/R6OldPollutionNegative.idr
/tmp/thm73-review6-probes/spikes/src/DGamma/R6OperationalOccurrenceFoldPositive.idr
/tmp/thm73-review6-probes/spikes/src/DGamma/R6OuterPollutionNegative.idr
/tmp/thm73-review6-probes/spikes/src/DGamma/R6OuterSchedulesPositive.idr
/tmp/thm73-review6-probes/spikes/src/DGamma/R6SafetyDetachmentNegative.idr
/tmp/thm73-review6-probes/spikes/src/DGamma/R6ScannerRetainedFixturesPositive.idr
/tmp/thm73-review6-probes/spikes/src/DGamma/R6ScannerThirdOrdering.idr
/tmp/thm73-review6-probes/spikes/src/DGamma/R6ScannerWrongGenerationNegative.idr
/tmp/thm73-review6-probes/spikes/src/DGamma/R6StaleQuotientNegative.idr
/tmp/thm73-review6-probes/spikes/src/DGamma/R6TwoIntermediateStatic.idr
/tmp/thm73-review6-probes/spikes/src/DGamma/R6WrongOccurrenceBridgeNegative.idr
/tmp/thm73-review6-probes/spikes/src/DGamma/R6WrongTraceBridgeNegative.idr
/tmp/thm73-review6-probes/spikes/src/DGamma/R6ZeroDerivationOperationalStep.idr
```
Result: PASS. Prior round-6 probe sources remain available as reference-only inputs and will be copied/adapted into the exact revision-7 external tree.

Classification: **note**.

### Probe 22 — round-7/whole-block prior artifact search

Command: `find /tmp ... R7*.idr, *WholeBlock*.idr, *Bridge*Positive*.idr`
```
```
Result: Inventory only. Any found files are untrusted and will be run only after copying into the exact target tree.

Classification: **note**.

### Probe 23 — round-6 wrong-right-birth reconstruction at the new bridge

Command: external expected-failure check of `R7BridgeWrongBirthNegative.idr`
```
 52 |       (replayGeneratedRegistrationOrigin occurrences replayedOccurrence **
 53 |         (Refl, (alternate replayedOccurrence ** ()))))
                                                      ^^

If MkUnit: When unifying:
    ()
and:
    generationForward (generatedGenerationBijection sameInputs) (registrationGeneration (canonicalToOriginal (canonicalRegistrationTree leftSchedule) ?fst)) = registrationGeneration (canonicalToOriginal (canonicalRegistrationTree rightSchedule) ?fst)
Mismatch between: () and generationForward (generatedGenerationBijection sameInputs) (registrationGeneration (canonicalToOriginal (canonicalRegistrationTree leftSchedule) ?fst)) = registrationGeneration (canonicalToOriginal (canonicalRegistrationTree rightSchedule) ?fst).

DGamma.R7BridgeWrongBirthNegative:53:49--53:51
 49 |     (replayBridgeTables bridge)
 50 |     (replayBridgeControls bridge)
 51 |     (\replayedOccurrence =>
 52 |       (replayGeneratedRegistrationOrigin occurrences replayedOccurrence **
 53 |         (Refl, (alternate replayedOccurrence ** ()))))
                                                      ^^

exit=1
```
Result: PASS negative. The old arbitrary same-action replacement now fails at the missing original-generation equation.

Classification: **note**.

### Probe 24 — bridge actual-direction constructor

Command: external check of `R7BridgeDirectionPositive.idr`
```
168/168: Building DGamma.R7BridgeDirectionPositive (src/DGamma/R7BridgeDirectionPositive.idr)
exit=0
```
Result: PASS. The replay→canonical-left→original-left→accepted-forward→original-right constructor direction elaborates.

Classification: **note**.

### Probe 25 — synthetic canonicalToOriginal permutation

Command: external check of `R7CanonicalMapPermutationPositive.idr`
```
Error: While processing type of bridgeAcceptsSyntheticLeftScheduleMap. Undefined name effectTables. 

DGamma.R7CanonicalMapPermutationPositive:144:8--144:20
 140 |   ((n : name) -> (k : key) ->
 141 |     lookupBinding {key = key} {value = value} k
 142 |       (effectTables (projectEffectState @{nameEq} replayedFinal) n) =
 143 |     lookupBinding {key = key} {value = value} k
 144 |       (effectTables (projectEffectState @{nameEq} (canonicalFinal rightSchedule))
              ^^^^^^^^^^^^

Error: While processing right hand side of bridgeAcceptsSyntheticLeftScheduleMap. Can't solve constraint between: ?_ [locals in scope: leftSchedule, alternateLeftTree, occurrences, rightSchedule] and NameBijection ?name.

DGamma.R7CanonicalMapPermutationPositive:168:39--168:48
 164 |       (replaceScheduleCanonicalMap leftSchedule alternateLeftTree)
 165 |       replayed occurrences rightSchedule
 166 | bridgeAcceptsSyntheticLeftScheduleMap leftSchedule alternateLeftTree occurrences
 167 |   rightSchedule bijection fixed ambient tables controls match =
 168 |     MkReplayedCanonicalEndpointBridge bijection fixed ambient tables controls
                                             ^^^^^^^^^

exit=1
```
Result: Probe did not elaborate; inspect before classification.

Classification: **note**.

### Probe 26 — synthetic canonicalToOriginal permutation retry

Command: add direct `DGamma.Metatheory` import, rerun external check
```
Error: While processing type of bridgeAcceptsSyntheticLeftScheduleMap. Can't bind implicit DGamma.R7CanonicalMapPermutationPositive.{value:5406} of type ({arg:10199} : ?DGamma.R7CanonicalMapPermutationPositive.{key:5405}_[name[24], key[23], world[22], error[21], value[20], protocol[19], nameEq[18], keyEq[17], initial[16], leftFinal[15], rightFinal[14], replayedFinal[13], leftTrace[12], rightTrace[11], sameInputs[10], leftSchedule[9], alternateLeftTree[8], replayed[7], occurrences[6], rightSchedule[5], bijection[4], {arg:5292}[3], {arg:5326}[2], {arg:5353}[1], n[0]]) -> Type

DGamma.R7CanonicalMapPermutationPositive:115:1--166:41
 115 | ||| Consequently the bridge constructor accepts a synthetic schedule map. The
 116 | ||| only new premise is its equation relative to that synthetic map; no accepted
 117 | ||| scanner/correspondence field pins the map to a trace occurrence.
 118 | public export
 119 | 0 bridgeAcceptsSyntheticLeftScheduleMap :
 120 |   {name, key, world, error : Type} -> {value : key -> Type} ->

Error: While processing right hand side of bridgeAcceptsSyntheticLeftScheduleMap. Can't solve constraint between: ?_ [locals in scope: leftSchedule, alternateLeftTree, occurrences, rightSchedule] and NameBijection ?name.

DGamma.R7CanonicalMapPermutationPositive:169:39--169:48
 165 |       (replaceScheduleCanonicalMap leftSchedule alternateLeftTree)
 166 |       replayed occurrences rightSchedule
 167 | bridgeAcceptsSyntheticLeftScheduleMap leftSchedule alternateLeftTree occurrences
 168 |   rightSchedule bijection fixed ambient tables controls match =
 169 |     MkReplayedCanonicalEndpointBridge bijection fixed ambient tables controls
                                             ^^^^^^^^^

exit=1
```
Result: Still not elaborated; no conclusion yet.

Classification: **note**.

### Probe 27 — synthetic canonicalToOriginal permutation retry 2

Command: make dependent lookup parameters explicit and rerun
```
168/168: Building DGamma.R7CanonicalMapPermutationPositive (src/DGamma/R7CanonicalMapPermutationPositive.idr)
exit=0
```
Result: ATTACK PASSES. A schedule can install a generation-permuted `canonicalToOriginal`, and the bridge consumes an equation through that caller-controlled map.

Classification: **blocker**.

### Probe 28 — concrete two-occurrence generation swap algebra

Command: external check of `R7TwoOccurrencePermutationPositive.idr`
```
Error: While processing right hand side of generationOf. When unifying:
    LocatedGeneratedRegistration child parent component trace -> RegistrationGeneration name
and:
    LocatedGeneratedRegistration child parent component trace -> RegistrationGeneration name
Mismatch between: name (implicitly bound at DGamma.R7TwoOccurrencePermutationPositive:11:1--11:13) and name.

DGamma.R7TwoOccurrencePermutationPositive:11:16--11:38
 07 | %default total
 08 | 
 09 | 0 generationOf : LocatedGeneratedRegistration child parent component trace ->
 10 |   RegistrationGeneration name
 11 | generationOf = registrationGeneration
                     ^^^^^^^^^^^^^^^^^^^^^^

exit=1
```
Result: Probe failed; no added evidence.

Classification: **note**.

### Probe 29 — concrete two-occurrence generation swap algebra retry

Command: remove unused auto-implicit helper and rerun
```
169/169: Building DGamma.R7TwoOccurrencePermutationPositive (src/DGamma/R7TwoOccurrencePermutationPositive.idr)
exit=0
```
Result: PASS. Exactly-two same-action occurrences admit a checked nontrivial involutive generation swap.

Classification: **blocker evidence** augmenting Probe 27.

### Probe 30 — round-6 zero-node whole-block producer

Command: external expected-failure check of adapted `R7ZeroDerivationOperationalStepNegative.idr`
```
169/169: Building DGamma.R7ZeroDerivationOperationalStepNegative (src/DGamma/R7ZeroDerivationOperationalStepNegative.idr)
Error: While processing right hand side of zeroDerivationOperationalStepStillAccepted. When unifying:
    FiniteAdjacentSwapDerivation ?name ?key ?world ?error ?value ?protocol ?nameEq ?keyEq ?trace ?trace
and:
    WholeBlockSwapDerivation name key world error value ?protocol ?nameEq ?keyEq ?orderSwap ?sourceTrace ?sourceBlocks ?sourcePremises ?safety sourceTrace
Mismatch between: FiniteAdjacentSwapDerivation ?name ?key ?world ?error ?value ?protocol ?nameEq ?keyEq ?trace ?trace and WholeBlockSwapDerivation name key world error value ?protocol ?nameEq ?keyEq ?orderSwap ?sourceTrace ?sourceBlocks ?sourcePremises ?safety sourceTrace.

DGamma.R7ZeroDerivationOperationalStepNegative:40:7--40:29
 36 |     orderSwap sourceTrace sourceBlocks sourcePremises safety
 37 | zeroDerivationOperationalStepStillAccepted {sourceFinal} {sourceTrace} {sourcePremises}
 38 |   safety targetBlocks endpoint sameInputs =
 39 |     MkOperationalAdjacentBlockSwap sourceFinal sourceTrace
 40 |       FiniteAdjacentSwapDone targetBlocks endpoint sourcePremises sameInputs
            ^^^^^^^^^^^^^^^^^^^^^^

exit=1
```
Result: PASS negative. The old zero-node record construction is rejected because the field now requires `WholeBlockSwapDerivation`.

Classification: **note**.

### Probe 31 — singleton-block positive whole-block witness

Command: external check of `R7WholeBlockSingletonPositive.idr`
```
DGamma.R7WholeBlockSingletonPositive:49:3--50:32
 49 |   blockBody (decomposedBlock sourceBlocks (actorLeft orderSwap)
 50 |     (safetyLeftInOrder safety)) = NoTransitions ->

Error: While processing right hand side of singletonWholeBlockWitness. When unifying:
    Nat
and:
    Type
Mismatch between: Nat and Type.

DGamma.R7WholeBlockSingletonPositive:62:22--62:34
 58 |     derivation
 59 |     [(0, 0)]
 60 |     labels
 61 |     (\leftPosition, rightPosition, leftBound, rightBound =>
 62 |       let leftZero : leftPosition = 0
                           ^^^^^^^^^^^^

exit=1
```
Result: Positive singleton producer failed; inspect.

Classification: **major**.

### Probe 32 — singleton-block positive retry

Command: restate singleton block sizes by exact transition counts and rerun
```
 86 |     derivation
 87 |     [(the Nat 0, the Nat 0)]
 88 |     labels
          ^^^^^^
Did you mean: Transition?
Error: indexBelowOneIsZero is not covering.

DGamma.R7WholeBlockSingletonPositive:18:1--18:45
 14 | 0 noElemNil : Elem x [] -> Void
 15 | noElemNil Here impossible
 16 | noElemNil (There later) impossible
 17 | 
 18 | 0 indexBelowOneIsZero : LTE (S n) 1 -> n = 0
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Missing cases:
    indexBelowOneIsZero _

exit=1
```
Result: Positive singleton still fails.

Classification: **major**.

### Probe 33 — singleton-block positive retry 2

Command: use `fromLteSucc`, case-based dependent elimination, and direct Metatheory import; rerun
```
169/169: Building DGamma.R7WholeBlockSingletonPositive (src/DGamma/R7WholeBlockSingletonPositive.idr)
Error: Couldn't parse declaration.

DGamma.R7WholeBlockSingletonPositive:20:1--20:20
 16 | noElemNil Here impossible
 17 | noElemNil (There later) impossible
 18 | 
 19 | 0 indexBelowOneIsZero : LTE (S n) 1 -> n = 0
 20 | indexBelowOneIsZero proof = case fromLteSucc proof of
      ^^^^^^^^^^^^^^^^^^^

exit=1
```
Result: Positive singleton still fails.

Classification: **major**.

### Probe 34 — singleton-block positive retry 3

Command: rename reserved probe binder and rerun
```
DGamma.R7WholeBlockSingletonPositive:31:31--31:59
 27 |   LTE (S leftPosition) leftCount -> LTE (S rightPosition) rightCount ->
 28 |   Elem (leftPosition, rightPosition) [(the Nat 0, the Nat 0)]
 29 | singletonComplete leftCount rightCount leftOne rightOne leftPosition rightPosition
 30 |   leftBound rightBound =
 31 |     case indexBelowOneIsZero (rewrite leftOne in leftBound) of
                                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Error: While processing right hand side of singletonWholeBlockWitness. Rewriting by actorBlockTransitionCount (decomposedBlock sourceBlocks (actorLeft orderSwap) (safetyLeftInOrder safety)) = 1 did not change type nonEmptyAdjacentSwapNodeCount derivation = actorBlockTransitionCount (decomposedBlock sourceBlocks (actorLeft orderSwap) (safetyLeftInOrder safety)) * actorBlockTransitionCount (decomposedBlock sourceBlocks (actorRight orderSwap) (safetyRightInOrder safety)).

DGamma.R7WholeBlockSingletonPositive:104:6--104:52
 100 |       (actorBlockTransitionCount (decomposedBlock sourceBlocks
 101 |         (actorRight orderSwap) (safetyRightInOrder safety)))
 102 |       leftOne rightOne)
 103 |     (UniqueCons noElemNil UniqueNil)
 104 |     (rewrite leftOne in rewrite rightOne in oneNode)
            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

exit=1
```
Result: Positive singleton still fails.

Classification: **major**.

### Probe 35 — singleton-block positive retry 4

Command: correct rewrite orientation for count equalities and rerun
```
DGamma.R7WholeBlockSingletonPositive:44:38--44:53
 40 |   (LTE (S leftPosition) leftCount, LTE (S rightPosition) rightCount)
 41 | singletonSound leftCount rightCount leftOne rightOne leftPosition rightPosition
 42 |   present = case present of
 43 |     Here => (rewrite sym leftOne in LTESucc LTEZero,
 44 |              rewrite sym rightOne in LTESucc LTEZero)
                                           ^^^^^^^^^^^^^^^

Error: While processing right hand side of singletonWholeBlockWitness. Rewriting by 1 = ?x did not change type nonEmptyAdjacentSwapNodeCount derivation = actorBlockTransitionCount (decomposedBlock sourceBlocks (actorLeft orderSwap) (safetyLeftInOrder safety)) * actorBlockTransitionCount (decomposedBlock sourceBlocks (actorRight orderSwap) (safetyRightInOrder safety)).

DGamma.R7WholeBlockSingletonPositive:104:6--104:60
 100 |       (actorBlockTransitionCount (decomposedBlock sourceBlocks
 101 |         (actorRight orderSwap) (safetyRightInOrder safety)))
 102 |       leftOne rightOne)
 103 |     (UniqueCons noElemNil UniqueNil)
 104 |     (rewrite sym leftOne in rewrite sym rightOne in oneNode)
            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

exit=1
```
Result: Positive singleton still fails.

Classification: **major**.

### Probe 36 — singleton-block positive retry 5

Command: use explicit `replace` transports and product equality; rerun
```
DGamma.R7WholeBlockSingletonPositive:44:38--44:53
 40 |   (LTE (S leftPosition) leftCount, LTE (S rightPosition) rightCount)
 41 | singletonSound leftCount rightCount leftOne rightOne leftPosition rightPosition
 42 |   present = case present of
 43 |     Here => (replace (sym leftOne) (LTESucc LTEZero),
 44 |              replace (sym rightOne) (LTESucc LTEZero))
                                           ^^^^^^^^^^^^^^^

Error: While processing right hand side of singletonWholeBlockWitness. Can't solve constraint between: transitionCount (blockBody (decomposedBlock sourceBlocks (actorRight orderSwap) (safetyRightInOrder safety))) and plus (transitionCount (blockBody (decomposedBlock sourceBlocks (actorRight orderSwap) (safetyRightInOrder safety)))) (mult (assert_total (integerToNat 0)) (actorBlockTransitionCount (decomposedBlock sourceBlocks (actorRight orderSwap) (safetyRightInOrder safety)))).

DGamma.R7WholeBlockSingletonPositive:106:71--106:79
 102 |       leftOne rightOne)
 103 |     (UniqueCons noElemNil UniqueNil)
 104 |     (trans oneNode (sym (trans (cong (\count => count *
 105 |       actorBlockTransitionCount (decomposedBlock sourceBlocks
 106 |         (actorRight orderSwap) (safetyRightInOrder safety))) leftOne) rightOne)))
                                                                             ^^^^^^^^

exit=1
```
Result: Positive singleton still fails.

Classification: **major**.

### Probe 37 — singleton-block positive retry 6

Command: use explicit singleton pair equality and Nat multiplication-neutrality; rerun
```
DGamma.R7WholeBlockSingletonPositive:42:57--42:66
 38 |   LTE (S leftPosition) leftCount -> LTE (S rightPosition) rightCount ->
 39 |   Elem (leftPosition, rightPosition) [(the Nat 0, the Nat 0)]
 40 | singletonComplete leftCount rightCount leftOne rightOne leftPosition rightPosition
 41 |   leftBound rightBound =
 42 |     let leftZero = indexBelowOneIsZero (replace leftOne leftBound)
                                                              ^^^^^^^^^

Error: While processing right hand side of singletonSound. Can't solve constraint between: LTE 1 (S ?right) and ?p 1.

DGamma.R7WholeBlockSingletonPositive:57:40--57:55
 53 | singletonSound leftCount rightCount leftOne rightOne leftPosition rightPosition
 54 |   present =
 55 |     case singletonElemExact (leftPosition, rightPosition) present of
 56 |       Refl => (replace (sym leftOne) (LTESucc LTEZero),
 57 |                replace (sym rightOne) (LTESucc LTEZero))
                                             ^^^^^^^^^^^^^^^

exit=1
```
Result: Positive singleton still fails.

Classification: **major**.

### Probe 38 — singleton-block positive retry 7

Command: make all `replace` predicates explicit; rerun
```
    |
 29 |   (pair : (Nat, Nat)) -> Elem pair [(the Nat 0, the Nat 0)] ->
    |                                      ^^^^^^^^^^
 30 |   pair = (the Nat 0, the Nat 0)
 31 | singletonElemExact pair Here = Refl
    |                    ^^^^

Suggestion: Use the same name for both pattern variables, since they unify.
Error: While processing right hand side of singletonComplete. Can't solve constraint between: Elem ?x (?x :: ?xs) and ?p (the Nat 0, the Nat 0).

DGamma.R7WholeBlockSingletonPositive:45:33--45:37
 41 |   leftBound rightBound =
 42 |     let leftZero = indexBelowOneIsZero (replace {p = \count => LTE (S leftPosition) count} leftOne leftBound)
 43 |         rightZero = indexBelowOneIsZero (replace {p = \count => LTE (S rightPosition) count} rightOne rightBound)
 44 |         pairExact = pairZeroExact leftPosition rightPosition leftZero rightZero
 45 |      in replace (sym pairExact) Here
                                      ^^^^

exit=1
```
Result: Positive singleton still fails.

Classification: **major**.

### Probe 39 — singleton-block positive retry 8

Command: force singleton member pair and its replacement predicate; rerun
```
169/169: Building DGamma.R7WholeBlockSingletonPositive (src/DGamma/R7WholeBlockSingletonPositive.idr)
exit=0
```
Result: PASS. The 1×1 positive producer elaborates with exactly one node.

Classification: **note**.

### Probe 40 — 2×1 whole-block boundary

Command: external check of `R7WholeBlockTwoByOnePositive.idr`
```
 26 | data BelowTwo : Nat -> Type where
 27 |   BelowTwoZero : BelowTwo 0
 28 |   BelowTwoOne : BelowTwo 1
 29 | 
 30 | 0 belowTwo : LTE (S n) 2 -> BelowTwo n
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Calls non covering function DGamma.R7WholeBlockTwoByOnePositive.with block in belowTwo
Error: with block in belowTwo is not covering.

DGamma.R7WholeBlockTwoByOnePositive:31:1--33:36
 31 | belowTwo bound with (fromLteSucc bound)
 32 |   _ | LTEZero = BelowTwoZero
 33 |   _ | LTESucc LTEZero = BelowTwoOne

Missing cases:
    with block in belowTwo (S (S _)) _ _

exit=1
```
Result: Probe needs correction or exposes over-strength.

Classification: **note** pending retry.

### Probe 41 — 2×1 whole-block boundary retry

Command: add impossible LTE case and correct product equality; rerun
```
 50 |   (LTESucc (LTESucc LTEZero), LTESucc LTEZero)
 51 | labels21Sound left right (There (There later)) = void (noElemNil later)
                                                                       ^^^^^

Error: While processing right hand side of labels21Unique. When unifying:
    UniqueKeys [(the Nat 0, the Nat 0), (the Nat 1, the Nat 0)]
and:
    UniqueKeys labels21
Mismatch between: [(the Nat 0, the Nat 0), (the Nat 1, the Nat 0)] and labels21.

DGamma.R7WholeBlockTwoByOnePositive:58:18--58:73
 54 | pair00Not10 Here impossible
 55 | pair00Not10 (There later) = noElemNil later
 56 | 
 57 | 0 labels21Unique : UniqueKeys labels21
 58 | labels21Unique = UniqueCons pair00Not10 (UniqueCons noElemNil UniqueNil)
                       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

exit=1
```
Result: 2×1 positive still fails.

Classification: **major**.

### Probe 42 — 2×1 whole-block boundary retry 2

Command: remove lowercase-global auto-implicit ambiguity and rerun
```
169/169: Building DGamma.R7WholeBlockTwoByOnePositive (src/DGamma/R7WholeBlockTwoByOnePositive.idr)
Error: Couldn't parse declaration.

DGamma.R7WholeBlockTwoByOnePositive:33:1--33:2
 29 |   _ | LTEZero = BelowTwoZero
 30 |   _ | LTESucc LTEZero = BelowTwoOne
 31 |   _ | LTESucc (LTESucc impossibleBound) impossible
 32 | 
 33 | 0 [(the Nat 0, the Nat 0), (the Nat 1, the Nat 0)]Complete : (leftPosition, rightPosition : Nat) ->
      ^

exit=1
```
Result: 2×1 positive still fails.

Classification: **major**.

### Probe 43 — 2×1 whole-block boundary retry 3

Command: restore helper identifiers after literal substitution and rerun
```

Missing cases:
    labels21Sound 0 0 (There _)
    labels21Sound 0 0 (There _)
    labels21Sound 0 0 (There _)
    labels21Sound 0 0 (There _)

Error: twoByOneWholeBlockWitness is not covering.

DGamma.R7WholeBlockTwoByOnePositive:60:1--93:73
 60 | ||| Boundary producer for legitimate 2x1 blocks. It consumes exactly two actual
 61 | ||| derivation nodes already labeled (0,0) and (1,0), then discharges every
 62 | ||| Cartesian bound/coverage/uniqueness/count field without additional capital.
 63 | public export
 64 | 0 twoByOneWholeBlockWitness :
 65 |   {name, key, world, error : Type} -> {value : key -> Type} ->

Calls non covering function DGamma.R7WholeBlockTwoByOnePositive.labels21Sound
exit=1
```
Result: 2×1 positive still fails.

Classification: **major**.

### Probe 44 — 2×1 whole-block boundary retry 4

Command: replace partial dependent member patterns with a total label view; rerun
```

Missing cases:
    labels21View (0, 0) (There _)
    labels21View (0, 0) (There _)
    labels21View (0, 0) (There _)
    labels21View (0, 0) (There _)

Error: twoByOneWholeBlockWitness is not covering.

DGamma.R7WholeBlockTwoByOnePositive:72:1--105:73
 072 | ||| Boundary producer for legitimate 2x1 blocks. It consumes exactly two actual
 073 | ||| derivation nodes already labeled (0,0) and (1,0), then discharges every
 074 | ||| Cartesian bound/coverage/uniqueness/count field without additional capital.
 075 | public export
 076 | 0 twoByOneWholeBlockWitness :
 077 |   {name, key, world, error : Type} -> {value : key -> Type} ->

Calls non covering function DGamma.R7WholeBlockTwoByOnePositive.labels21Sound
exit=1
```
Result: 2×1 positive still fails.

Classification: **major**.

### Probe 45 — 2×1 whole-block boundary retry 5

Command: add explicit impossible mismatched singleton-tail member; rerun
```

Missing cases:
    labels21View (0, 0) (There _)
    labels21View (0, 0) (There _)
    labels21View (0, 0) (There _)
    labels21View (0, 0) (There _)

Error: twoByOneWholeBlockWitness is not covering.

DGamma.R7WholeBlockTwoByOnePositive:73:1--106:73
 073 | ||| Boundary producer for legitimate 2x1 blocks. It consumes exactly two actual
 074 | ||| derivation nodes already labeled (0,0) and (1,0), then discharges every
 075 | ||| Cartesian bound/coverage/uniqueness/count field without additional capital.
 076 | public export
 077 | 0 twoByOneWholeBlockWitness :
 078 |   {name, key, world, error : Type} -> {value : key -> Type} ->

Calls non covering function DGamma.R7WholeBlockTwoByOnePositive.labels21Sound
exit=1
```
Result: 2×1 positive still fails.

Classification: **major**.

### Probe 46 — 2×1 whole-block boundary retry 6

Command: use a generic two-element membership eliminator; rerun
```
DGamma.R7WholeBlockTwoByOnePositive:47:1--50:52
 47 | 0 labels21Sound : (leftPosition, rightPosition : Nat) ->
 48 |   Elem (leftPosition, rightPosition)
 49 |     [(the Nat 0, the Nat 0), (the Nat 1, the Nat 0)] ->
 50 |   (LTE (S leftPosition) 2, LTE (S rightPosition) 1)

Calls non covering function DGamma.R7WholeBlockTwoByOnePositive.case block in labels21Sound
Error: twoByOneWholeBlockWitness is not covering.

DGamma.R7WholeBlockTwoByOnePositive:66:1--99:73
 66 | ||| Boundary producer for legitimate 2x1 blocks. It consumes exactly two actual
 67 | ||| derivation nodes already labeled (0,0) and (1,0), then discharges every
 68 | ||| Cartesian bound/coverage/uniqueness/count field without additional capital.
 69 | public export
 70 | 0 twoByOneWholeBlockWitness :
 71 |   {name, key, world, error : Type} -> {value : key -> Type} ->

Calls non covering function DGamma.R7WholeBlockTwoByOnePositive.labels21Sound
exit=1
```
Result: 2×1 positive still fails.

Classification: **major**.

### Probe 47 — 2×1 whole-block boundary retry 7

Command: transport bounds through pair equality without dependent Refl coverage; rerun
```
169/169: Building DGamma.R7WholeBlockTwoByOnePositive (src/DGamma/R7WholeBlockTwoByOnePositive.idr)
exit=0
```
Result: PASS. Exactly two real labeled nodes can satisfy all 2×1 Cartesian obligations.

Classification: **note**.

### Probe 48 — 2×2 whole-block boundary

Command: external check of `R7WholeBlockTwoByTwoPositive.idr`
```
169/169: Building DGamma.R7WholeBlockTwoByTwoPositive (src/DGamma/R7WholeBlockTwoByTwoPositive.idr)
Error: While processing right hand side of twoByTwoWholeBlockWitness. When unifying:
    2 * 2 = 4
and:
    2 * 2 = 4
Mismatch between: 4 and S (plus (assert_total (integerToNat 1)) (mult (assert_total (integerToNat 1)) 2)).

DGamma.R7WholeBlockTwoByTwoPositive:155:54--155:63
 151 |       (trans fourNodes (sym (trans
 152 |         (cong (\count => count * actorBlockTransitionCount
 153 |           (decomposedBlock sourceBlocks (actorRight orderSwap)
 154 |             (safetyRightInOrder safety))) leftTwo)
 155 |         (trans (cong (\count => 2 * count) rightTwo) product22))))
                                                            ^^^^^^^^^

exit=1
```
Result: 2×2 positive fails.

Classification: **major**.

### Probe 49 — 2×2 whole-block boundary retry

Command: eliminate overloaded literal ambiguity in exact count and rerun
```
169/169: Building DGamma.R7WholeBlockTwoByTwoPositive (src/DGamma/R7WholeBlockTwoByTwoPositive.idr)
exit=0
```
Result: PASS. Four actual labeled nodes satisfy all 2×2 Cartesian obligations.

Classification: **note**.

### Probe 50 — repeated-action/tag position-label ambiguity

Command: external check of `R7WholeBlockDuplicateLabelAttack.idr`
```
169/169: Building DGamma.R7WholeBlockDuplicateLabelAttack (src/DGamma/R7WholeBlockDuplicateLabelAttack.idr)
exit=0
```
Result: ATTACK PASSES. The exact same adjacent-swap node can be certified at selected-block position 0 or 1 whenever both positions share action/tag. Therefore Cartesian uniqueness/count are only uniqueness/count of caller labels; they do not prove node-to-source-occurrence uniqueness and cannot reject a duplicate/degenerate derivation involving repeated Iter steps.

Classification: **blocker**.

### Probe 51 — complete external producer/consumer pipeline

Command: external check of adapted `R7FullPipeline.idr`
```
169/169: Building DGamma.R7FullPipeline (src/DGamma/R7FullPipeline.idr)
exit=0
```
Result: PASS. The published boundaries compose from two upstream bundles through split deletion, sorting, sealed O19/O20, generation-coupled O21, and exact immutable `ConfluenceResult` with no extra premise.

Classification: **note**.

### Probe 52 — independently callable O7–O11 boundaries

Command: external check of `R7DeletionBoundariesPositive.idr`
```
166/166: Building DGamma.R7DeletionBoundariesPositive (src/DGamma/R7DeletionBoundariesPositive.idr)
exit=0
```
Result: PASS. O7 scan, O8 selection, O9 enrichment, O10 recursion, and O11 accounting are externally callable using only upstream outputs; both legacy wrappers remain externally callable.

Classification: **note**.

### Probe 53 — exact named-hole inventory

Command: regex-scan all five CP5 research spikes for unique `?*_rhs` identifiers
```
CP5ConfluenceCanonicalSortSpike.idr 6
  canonicalSupportTransportSpike_rhs
  closingFreeTraceShapeSpike_rhs
  deletionSortingOrchestrationAccountingSpike_rhs
  independentCanonicalScheduleSpike_rhs
  sortClosingFreeTraceSpike_rhs
  supportOrderingSpike_rhs
CP5ConfluenceCrossTraceSpike.idr 4
  canonicalSchedulesConvergeSpike_rhs
  canonicalSupportOrdersMatchSpike_rhs
  operationalAdjacentBlockSwapSpike_rhs
  selectOperationalCanonicalPermutationSpike_rhs
CP5ConfluenceDeletionChainSpike.idr 10
  assembleClosingFreeAccountingSpike_rhs
  closingEpisodeOccurrenceScanSpike_rhs
  deleteClosingEpisodesCoreSpike_rhs
  deletedClassificationForcesLeftScannerDiscardSpike_rhs
  deletedClassificationForcesRightScannerDiscardSpike_rhs
  enrichDeletionChainStepSpike_rhs
  sameExternalOrchestrationReflexiveSpike_rhs
  sameExternalOrchestrationTransitiveSpike_rhs
  selectMaximalClosingEpisodeSpike_rhs
  traceIndependentAfterDeletionReplaySpike_rhs
CP5ConfluenceLocalDiamondSpike.idr 8
  activationActivationDiamondSpike_rhs
  activationOrchestrationDiamondSpike_rhs
  adjacentSwapSuffixSpike_rhs
  orchestrationActivationDiamondSpike_rhs
  orchestrationOrchestrationDiamondSpike_rhs
  relationalReplayEndpointReflexiveSpike_rhs
  relationalReplayEndpointTransitiveSpike_rhs
  traceIndependentAfterRelationalReplaySpike_rhs
CP5ConfluenceRenamingCompositionSpike.idr 2
  composeModuloVestigialEndpointSpike_rhs
  replayedCanonicalToOriginalEndpointSpike_rhs
TOTAL 30
```
Result: PASS. Exact phase split is canonical 6, cross 4, deletion 10, local 8, renaming 2; total 30.

Classification: **note**.

### Probe 54 — estimate arithmetic and named gates

Command: parse all eight phase rows and mandatory re-estimation gate text
```
[('A', 4, 8), ('B', 14, 24), ('C', 10, 18), ('D', 9, 17), ('E', 7, 13), ('F', 9, 16), ('G', 27, 41), ('H', 2, 5)]
SUM 82 142
first complete singleton and general True
first complete O7 scan plus O8 maximal selector plus O9 enriched D72 True
first complete accepted-correspondence same-name scanner proof True
```
Result: PASS arithmetic. Raw rows sum exactly 82–142 with no overlap deduction; all three stated gate phrases are present.

Classification: **note**. Defensibility is reassessed after interface attacks below.

### Probe 55 — retained-suite source staging

Command: copy the exact round-6 negative, scanner, static, occurrence-fold, and outer-schedule probe sources into the revision-7 external spike tree.

Result: PASS. Sixteen untrusted retained probes are staged outside the repository; each is run separately below.

Classification: **note**.

### Probe 56 — retained old pure-certificate pollution

Command: expected-failure check of `R6OldPollutionNegative.idr` against revision 7
```
Mismatch between: CertifiedActorPermutation name (supportOrder (canonicalSchedule leftCapital)) (map (renameBackward (currentNameBijection (endpointRenaming sameInputs))) (supportOrder (canonicalSchedule rightCapital))) and CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital ?matching.

DGamma.R6OldPollutionNegative:42:54--42:62
 38 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational)
 39 | oldPollutionReachesO20 {nameEq} {keyEq} {protocol} {leftTrace} {rightTrace}
 40 |   {sameInputs} {leftCapital} {rightCapital} matching polluted =
 41 |     (polluted ** canonicalSchedulesConvergeSpike nameEq keyEq protocol leftTrace
 42 |       rightTrace sameInputs leftCapital rightCapital polluted)
                                                           ^^^^^^^^

exit=1
```
Result: PASS negative. A pure certificate still cannot reach sealed O20.

Classification: **note**.

### Probe 57 — retained outer sealed-package pollution

Command: expected-failure check of `R6OuterPollutionNegative.idr`
```
Error: While processing right hand side of wrapPollutedOuter. Can't solve constraint between: base .selectedActorPermutation and ActorPermutationStep forward (ActorPermutationStep backward (selectedActorPermutation base)).

DGamma.R6OuterPollutionNegative:47:6--47:38
 43 |     (operationalTargetFinal base)
 44 |     (operationalTargetTrace base)
 45 |     (operationalTargetBlocks base)
 46 |     (operationalTargetPremises base)
 47 |     (selectedPermutationRealized base)
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

exit=1
```
Result: PASS negative. A sealed realization cannot be reindexed under a polluted outer actor certificate.

Classification: **note**.

### Probe 58 — retained current-state safety detachment

Command: expected-failure check of `R6SafetyDetachmentNegative.idr`
```
Mismatch between: firstPremises and secondPremises.

DGamma.R6SafetyDetachmentNegative:33:39--33:45
 29 |   AdjacentActorSwapSafety name key world error value protocol nameEq keyEq
 30 |     orderSwap firstTrace firstBlocks firstPremises ->
 31 |   AdjacentActorSwapSafety name key world error value protocol nameEq keyEq
 32 |     orderSwap secondTrace secondBlocks secondPremises
 33 | detachSafetyFromCurrentState safety = safety
                                            ^^^^^^

exit=1
```
Result: PASS negative. Safety remains tied to exact current trace/blocks/bundle.

Classification: **note**.

### Probe 59 — retained generated-child rejection

Command: positive check of `R6GeneratedChildSafetyPositive.idr`
```
169/169: Building DGamma.R6GeneratedChildSafetyPositive (src/DGamma/R6GeneratedChildSafetyPositive.idr)
exit=0
```
Result: PASS. Exact headed generated-child insertion contradicts block-swap safety before O20.

Classification: **note**.

### Probe 60 — retained wrong operational trace bridge

Command: expected-failure check of `R6WrongTraceBridgeNegative.idr`
```
                                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Error: While processing right hand side of wrongTraceBridge. Can't solve constraint between: ?_ [no locals in scope] and CanonicalConvergenceResult ?name ?key ?world ?error ?value ?protocol ?nameEq ?keyEq ?leftTrace ?rightTrace ?sameInputs ?leftCapital ?rightCapital ?operational.

DGamma.R6WrongTraceBridgeNegative:36:78--36:89
 32 |     (canonicalTrace (canonicalSchedule leftCapital)) otherTrace) ->
 33 |   ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
 34 |     leftTrace rightTrace sameInputs (canonicalTrace (canonicalSchedule leftCapital))
 35 |     otherTrace otherOccurrences (canonicalSchedule rightCapital)
 36 | wrongTraceBridge convergence otherTrace otherOccurrences = convergenceBridge convergence
                                                                                   ^^^^^^^^^^^

exit=1
```
Result: PASS negative. The bridge cannot detach to another operational trace/final.

Classification: **note**.

### Probe 61 — retained wrong operational trace bridge, corrected interface

Command: replace obsolete bridge source-trace argument with full left schedule and rerun expected failure
```
169/169: Building DGamma.R6WrongTraceBridgeNegative (src/DGamma/R6WrongTraceBridgeNegative.idr)
Error: While processing right hand side of wrongTraceBridge. Can't solve constraint between: operational .operationalTargetFinal and otherFinal.

DGamma.R6WrongTraceBridgeNegative:36:60--36:89
 32 |     (canonicalTrace (canonicalSchedule leftCapital)) otherTrace) ->
 33 |   ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
 34 |     leftTrace rightTrace sameInputs (canonicalSchedule leftCapital)
 35 |     otherTrace otherOccurrences (canonicalSchedule rightCapital)
 36 | wrongTraceBridge convergence otherTrace otherOccurrences = convergenceBridge convergence
                                                                 ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

exit=1
```
Result: PASS negative. Probe 60 was interface-drift noise; this corrected probe reaches and rejects exact operational final detachment.

Classification: **note**.

### Probe 62 — retained stale quotient

Command: expected-failure check of `R6StaleQuotientNegative.idr`
```
Mismatch between: firstOp and secondOp.

DGamma.R6StaleQuotientNegative:33:47--33:80
 29 |   (second : PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 30 |     leftTrace rightTrace sameInputs leftCapital rightCapital secondOp) ->
 31 |   RelationalReplayEndpoint name key world error value nameEq keyEq
 32 |     (canonicalFinal (canonicalSchedule leftCapital)) (operationalTargetFinal secondOp)
 33 | staleQuotient firstOp secondOp first second = composedPermutationEndpoint first
                                                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

exit=1
```
Result: PASS negative. Endpoint quotient remains exact-package indexed.

Classification: **note**.

### Probe 63 — retained mixed schedule substitution

Command: expected-failure check of `R6MixedScheduleNegative.idr`
```
Mismatch between: leftCapital and otherLeft.

DGamma.R6MixedScheduleNegative:34:41--34:52
 30 |     (currentNameBijection (endpointRenaming sameInputs))
 31 | mixedLeftSchedule {nameEq} {keyEq} {protocol} {leftTrace} {rightTrace} {sameInputs}
 32 |   leftCapital otherLeft rightCapital convergence =
 33 |     originalEndpointsConvergeSpike nameEq keyEq protocol leftTrace rightTrace
 34 |       sameInputs otherLeft rightCapital convergence
                                              ^^^^^^^^^^^

exit=1
```
Result: PASS negative. O21 cannot mix an unrelated enriched left schedule.

Classification: **note**.

### Probe 64 — retained wrong occurrence-relation bridge

Command: expected-failure check of `R6WrongOccurrenceBridgeNegative.idr`
```
and:
    CanonicalSchedule name key world error value protocol nameEq keyEq leftTrace
Mismatch between: Transitions initial canonicalLeftFinal and CanonicalSchedule name key world error value protocol nameEq keyEq leftTrace.

DGamma.R6WrongOccurrenceBridgeNegative:28:37--28:43
 24 |     value source replayed) ->
 25 |   {rightSchedule : CanonicalSchedule name key world error value protocol nameEq
 26 |     keyEq rightTrace} ->
 27 |   ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
 28 |     leftTrace rightTrace sameInputs source replayed first rightSchedule ->
                                          ^^^^^^

exit=1
```
Result: Negative stopped elsewhere; inspect.

Classification: **major**.

### Probe 65 — wrong occurrence relation, corrected interface

Command: expected-failure check of `R7WrongOccurrenceBridgeNegative.idr`
```
Mismatch between: first and second.

DGamma.R7WrongOccurrenceBridgeNegative:32:54--32:60
 28 |   ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
 29 |     leftTrace rightTrace sameInputs leftSchedule replayed first rightSchedule ->
 30 |   ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
 31 |     leftTrace rightTrace sameInputs leftSchedule replayed second rightSchedule
 32 | detachBridgeOccurrenceRelation first second bridge = bridge
                                                           ^^^^^^

exit=1
```
Result: PASS negative. Probe 64 was interface-drift noise; exact occurrence correspondence cannot detach.

Classification: **note**.

### Probe 66 — retained wrong-generation scanner substitution

Command: expected-failure check of `R6ScannerWrongGenerationNegative.idr`
```
Mismatch between: 12 and 0.

DGamma.R6ScannerWrongGenerationNegative:14:29--14:33
 10 | 0 conflateSameRawNameBirths :
 11 |   Elem DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth6
 12 |     [ DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18
 13 |     , DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth6 ]
 14 | conflateSameRawNameBirths = Here
                                  ^^^^

exit=1
```
Result: PASS negative. Same raw name cannot erase the birth ordinal.

Classification: **note**.

### Probe 67 — retained first/two scanner orderings

Command: positive check of `R6ScannerRetainedFixturesPositive.idr`
```
168/168: Building DGamma.R6ScannerRetainedFixturesPositive (src/DGamma/R6ScannerRetainedFixturesPositive.idr)
exit=0
```
Result: PASS. The first two cross-side orderings expose exact full final indexes and exact deleted-list equalities.

Classification: **note**.

### Probe 68 — retained third scanner ordering

Command: positive check of `R6ScannerThirdOrdering.idr`
```
168/168: Building DGamma.R6ScannerThirdOrdering (src/DGamma/R6ScannerThirdOrdering.idr)
exit=0
```
Result: PASS. L6,R9,R14,L18 reaches the same exact full indexes/deleted lists.

Classification: **note**.

### Probe 69 — retained one/moved-intermediate static variants

Command: positive check of `R6FourFiberStatic.idr`
```
169/169: Building DGamma.R6FourFiberStatic (src/DGamma/R6FourFiberStatic.idr)
exit=0
```
Result: PASS. One/moved-intermediate and licensing-parent exclusion static artifacts remain valid, with no reachable O19/O20 claim.

Classification: **note**.

### Probe 70 — retained two-intermediate static variant

Command: positive check of `R6TwoIntermediateStatic.idr`
```
169/169: Building DGamma.R6TwoIntermediateStatic (src/DGamma/R6TwoIntermediateStatic.idr)
exit=0
```
Result: PASS. Two unsupported withdrawn intermediates remain a valid static/interface fixture.

Classification: **note**.

### Probe 71 — retained two-step occurrence fold

Command: positive check of `R6OccurrenceFoldPositive.idr`
```
32/32: Building DGamma.R6OccurrenceFoldPositive (src/DGamma/R6OccurrenceFoldPositive.idr)
exit=0
```
Result: PASS. Action/tag/generated-generation occurrence correspondences still compose through two steps.

Classification: **note**.

### Probe 72 — retained recursive operational occurrence fold

Command: positive check of `R6OperationalOccurrenceFoldPositive.idr`
```
169/169: Building DGamma.R6OperationalOccurrenceFoldPositive (src/DGamma/R6OperationalOccurrenceFoldPositive.idr)
exit=0
```
Result: PASS. Recursive actor permutations expose the exact step/rest occurrence composition.

Classification: **note**.

### Probe 73 — retained outer schedules

Command: positive check of `R6OuterSchedulesPositive.idr`
```
169/169: Building DGamma.R6OuterSchedulesPositive (src/DGamma/R6OuterSchedulesPositive.idr)
exit=0
```
Result: PASS. The immutable result retains the exact supplied original canonical schedules.

Classification: **note**.

### Probe 74 — reverse O1–O23 reconciliation against actual hole bodies

Command: map every identifier from Probe 53 back to the declarations and actual output types in the five spike modules.

Result:

- O1: five holes — two same-external algebra, two replay-endpoint algebra, one modulo-vestigial composition.
- O2: two — generic replay independence and deletion specialization.
- O3/O4/O5: one/two/one local-diamond holes.
- O6: adjacent suffix plus independently callable whole-block producer.
- O7/O8/O9/O10/O11: one independently callable hole each (scan/select/enrich/core/accounting); `chooseClosingStepSpike` and `deleteAllClosingEpisodesSpike` are complete wrappers.
- O12/O14/O15/O16/O17/O18: one each; O13 is record projections only.
- O19: matching plus independently callable sealed selector.
- O20: convergence/bridge aggregation.
- O21: two accepted scanner inductions plus replayed endpoint composition.
- O22 complete outer wrapper; O23 record/probe-only.

The counts sum to 30. No second O-number is hidden inside one deletion hole after the split. Multi-field outputs still exist where the table row itself is a coherent record theorem (notably O6, O17, O20), but no additional table obligation was found collapsed into them.

Classification: **note**. This reconciliation does not cure the semantic strength defects in Probes 27 and 50.

### Probe 75 — escape-hatch and release-reachability scan

Command: scan `src/**/*.idr` for named holes/escapes/partial/postulates; scan `src`+`dgamma.ipkg` for research reachability; scan research for non-hole escapes
```
production_forbidden:
<none>
release_reachability:
<none>
research_nonhole_escapes:
<none>
```
Result: PASS. Production is hole/escape-free; research is unreachable; research contains only deliberate named holes, no other escape hatch.

Classification: **note**.

### Probe 76 — exact external release build

Command: seed byte-identical production TTC cache, then `idris2 --build dgamma.ipkg` in exact archived release tree
```
194/207: Building DGamma.CP4ProgressStep (src/DGamma/CP4ProgressStep.idr)
195/207: Building DGamma.CP4ProgressNumeric (src/DGamma/CP4ProgressNumeric.idr)
196/207: Building DGamma.CP4ProgressPrecedence (src/DGamma/CP4ProgressPrecedence.idr)
197/207: Building DGamma.CP4ProgressFinite (src/DGamma/CP4ProgressFinite.idr)
198/207: Building DGamma.CP4ProgressReliance (src/DGamma/CP4ProgressReliance.idr)
199/207: Building DGamma.CP4ProgressNoDeadlock (src/DGamma/CP4ProgressNoDeadlock.idr)
200/207: Building DGamma.CP4ProgressUnloadingShape (src/DGamma/CP4ProgressUnloadingShape.idr)
201/207: Building DGamma.CP4ProgressUnloadingActive (src/DGamma/CP4ProgressUnloadingActive.idr)
202/207: Building DGamma.CP4ProgressUnloadingActiveStep (src/DGamma/CP4ProgressUnloadingActiveStep.idr)
203/207: Building DGamma.CP4ProgressUnloadingReloading (src/DGamma/CP4ProgressUnloadingReloading.idr)
204/207: Building DGamma.CP4ProgressUnloadingClassify (src/DGamma/CP4ProgressUnloadingClassify.idr)
205/207: Building DGamma.CP4ProgressUnloadingDescent (src/DGamma/CP4ProgressUnloadingDescent.idr)
206/207: Building DGamma.CP4ProgressNoDeadlockFinal (src/DGamma/CP4ProgressNoDeadlockFinal.idr)
207/207: Building DGamma.CP4ProgressProof (src/DGamma/CP4ProgressProof.idr)
exit=0
```
Result: PASS. Exact release package reaches 207/207; research and external probes are outside the package graph.

Classification: **note**.

### Probe 77 — bridge exact source and generation projection

Command: positive check of `R7BridgeSourceAndGenerationPositive.idr`
```
168/168: Building DGamma.R7BridgeSourceAndGenerationPositive (src/DGamma/R7BridgeSourceAndGenerationPositive.idr)
exit=0
```
Result: PASS. Consumers project both the exact replay-selected left source and the new accepted-forward original-generation equation.

Classification: **note**. The projected equation remains map-relative as shown by Probe 27.

### Probe 78 — earlier positive-probe artifact lookup

Command: find retained O/A and operational-threading probe sources across prior external trees
```
/tmp/thm73-review3-probes/src/DGamma/R3OADiamondApplicationProbe.idr
/tmp/thm73-review4-probes/spikes/src/DGamma/R4OADiamondApplication.idr
/tmp/thm73-review5-probes/spikes/src/DGamma/R5OperationalThreadingPositive.idr
```
Result: Inventory only; no matching retained path was found under the glob.

Classification: **note**.

Correction to Probe 78: three matching retained sources were found (round-3 O/A, round-4 O/A, round-5 operational threading). The “no matching path” sentence was erroneous. The round-4 O/A and round-5 threading probes are run next.

### Probe 79 — retained source-sensitive O/A application

Command: positive check of round-4 `R4OADiamondApplication.idr`
```
32/32: Building DGamma.R4OADiamondApplication (src/DGamma/R4OADiamondApplication.idr)
exit=0
```
Result: PASS. The source-sensitive O-then-A theorem remains externally consumable.

Classification: **note**.

### Probe 80 — current operational recursion threading

Command: positive check of `R7OperationalThreadingPositive.idr`
```
169/169: Building DGamma.R7OperationalThreadingPositive (src/DGamma/R7OperationalThreadingPositive.idr)
exit=0
```
Result: PASS. One strengthened whole-block step threads its exact target trace, blocks, and full premises into the recursive terminator.

Classification: **note**.

### Probe 81 — synthetic map reaches enriched one-trace capital

Command: extend Probe 27 with `replaceIndependentCanonicalMap`, rerun
```
168/168: Building DGamma.R7CanonicalMapPermutationPositive (src/DGamma/R7CanonicalMapPermutationPositive.idr)
exit=0
```
Result: ATTACK PASSES. `IndependentCanonicalSchedule` also accepts the cloned schedule map while reusing every other field definitionally, so O19/O20 universality does not restrict the malicious map to the intended producer.

Classification: **blocker**.

### Probe 82 — additional historical positive inventory

Command: find prior vestigial/convergence/scanner-consumer probes
```
/tmp/thm73-review3-probes/src/DGamma/CP3VestigialChecks.idr
/tmp/thm73-review3-probes/src/DGamma/R3MappedVestigialVariantProbe.idr
/tmp/thm73-review3-probes/src/DGamma/R3VestigialSimultaneousPackageProbe.idr
/tmp/thm73-review4-probes/release/src/DGamma/CP3VestigialChecks.idr
/tmp/thm73-review4-probes/spikes/src/DGamma/CP3VestigialChecks.idr
/tmp/thm73-review4-probes/spikes/src/DGamma/R4ConvergenceCouplingPositive.idr
/tmp/thm73-review4-probes/spikes/src/DGamma/R4IntermediateVestigialCountermodel.idr
/tmp/thm73-review4-probes/spikes/src/DGamma/R4MappedVestigialVariant.idr
/tmp/thm73-review4-probes/spikes/src/DGamma/R4ScannerProducerConsumers.idr
/tmp/thm73-review4-probes/spikes/src/DGamma/R4VestigialSimultaneous.idr
/tmp/thm73-review5-probes/release/src/DGamma/CP3VestigialChecks.idr
/tmp/thm73-review5-probes/spikes/src/DGamma/CP3VestigialChecks.idr
/tmp/thm73-review5-probes/spikes/src/DGamma/R5IndexedVestigialPipeline.idr
/tmp/thm73-review6-probes/release/src/DGamma/CP3VestigialChecks.idr
/tmp/thm73-review6-probes/spikes/src/DGamma/CP3VestigialChecks.idr
```
Result: Prior one-trace and mapped vestigial plus convergence/scanner consumers are available; the full current pipeline and static variants already cover their downstream indices, but the two direct vestigial positives are rerun for regression completeness.

Classification: **note**.

### Probe 83 — retained one-trace vestigial simultaneous package

Command: positive check of `R4VestigialSimultaneous.idr`
```
167/167: Building DGamma.R4VestigialSimultaneous (src/DGamma/R4VestigialSimultaneous.idr)
exit=0
```
Result: PASS. An accepted original-present/reduced-absent retired clean child remains compatible with simultaneous schedule/replay/bundle assembly.

Classification: **note**.

### Probe 84 — retained accepted scanner-capital consumers

Command: positive check of `R4ScannerProducerConsumers.idr`
```
168/168: Building DGamma.R4ScannerProducerConsumers (src/DGamma/R4ScannerProducerConsumers.idr)
exit=0
```
Result: PASS. Exact accepted correspondence and both withdrawal-to-deleted-list projections still require no external scanner premise.

Classification: **note**.

### Probe 85 — duplicate label pair versus duplicate node

Command: expected-failure check of `R7DuplicateLabelNegative.idr`
```
4/4: Building DGamma.R7DuplicateLabelNegative (src/DGamma/R7DuplicateLabelNegative.idr)
Error: While processing right hand side of duplicateLabelUnique. let 0 present = Here in ($resolved3183) Here is not a valid impossible case.

DGamma.R7DuplicateLabelNegative:11:34--11:49
 07 | 
 08 | 0 duplicateLabelUnique : UniqueKeys [(the Nat 0, the Nat 0), (the Nat 0, the Nat 0)]
 09 | duplicateLabelUnique =
 10 |   UniqueCons
 11 |     (\present => case present of Here impossible)
                                       ^^^^^^^^^^^^^^^

exit=1
```
Result: PASS negative for the narrow property: `UniqueKeys` rejects a literally duplicated pair label. Combined with Probe 50, however, it does not reject two occurrence-duplicate nodes carrying different labels, because action/tag-only labeling can assign either repeated source position to the same node.

Classification: **note**, with Probe 50 remaining a blocker.

### Probe 86 — final repository state before report closure

Command: `git status --short --branch; git diff --cached --name-only; git diff --name-only; git rev-parse HEAD; pgrep -fl [i]dris2`
```
## cp5-thm73-scoping...origin/cp5-thm73-scoping [ahead 40]
?? paper/
?? review-cp5-plan-round7.md
staged:
tracked-worktree:
head=139237a1dd714b9cf55b3f4c10d19cee79484e59
active-idris:
```
Result: PASS. HEAD remains exact target; no staged files, no tracked worktree change, and no Idris process. Only pre-existing untracked `paper/` plus this permitted report are present.

Classification: **note**.

### Probe 87 — exact source locations for final findings

Command: line-number grep of bridge, canonical map, whole-block label/count, and enriched schedule declarations
```
research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr:125:record ReplayedCanonicalEndpointBridge
research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr:161:  0 replayedGeneratedBirthMatched :
research/DGamma/CP5ConfluenceCrossTraceSpike.idr:132:data TraceActionTagAt :
research/DGamma/CP5ConfluenceCrossTraceSpike.idr:167:data DerivationCrossesBlockPositions :
research/DGamma/CP5ConfluenceCrossTraceSpike.idr:217:record WholeBlockSwapDerivation
research/DGamma/CP5ConfluenceCrossTraceSpike.idr:261:  0 blockCrossingPositionsUnique : UniqueKeys crossedSourcePositions
research/DGamma/CP5ConfluenceCrossTraceSpike.idr:262:  0 blockCrossingNodeCountExact :
research/DGamma/CP5ConfluenceCanonicalSortSpike.idr:241:record IndependentCanonicalSchedule
src/DGamma/CP3.idr:3109:record CanonicalRegistrationCorrespondence
src/DGamma/CP3.idr:3116:  canonicalToOriginal :
```
Result: PASS. Exact declaration anchors captured for consolidated findings.

Classification: **note**.

## Claimed-fix disposition

| # | Revision-7 claim | Checked disposition |
|---:|---|---|
| 1 | Bridge equation uses both schedules and accepted original generations | **Partly fixed, still unsound at the universal interface.** The old arbitrary-right-occurrence constructor fails exactly at the new equation (Probe 23), and the advertised direction/projections elaborate (Probes 24/77). But both `CanonicalSchedule` and `IndependentCanonicalSchedule` allow their `canonicalToOriginal` tree to be replaced while retaining every other field (Probes 27/81). The equation is therefore authentic only relative to caller-controlled maps. An exactly-two repeated-birth occurrence family admits a real nontrivial ordinal swap (Probe 29). |
| 2 | Whole-block evidence forces the true nonempty Cartesian crossing | **Nonempty/count/bounds pass; occurrence identity does not.** The old zero-node constructor fails (Probe 30); 1×1, 2×1, and 2×2 record assembly passes with exact node counts (Probes 39/47/49); literal duplicate pair labels fail (Probe 85). However, `TraceActionTagAt` stores only action and tag. The identical concrete finite node can be labeled at positions 0 and 1 when repeated steps share action/tag (Probe 50). Thus label uniqueness is not node/source-occurrence uniqueness. |
| 3 | O7–O11 split into independent callable gates and complete wrappers | **Addressed.** All five boundaries elaborate externally from upstream outputs only (Probe 52); both wrappers are complete source bodies; reverse hole mapping passes (Probes 53/74). |
| 4 | Prior negatives/positives and scanner fixtures retained | **Addressed at tested boundaries.** Old/outer pollution, safety detachment, generated-child, wrong trace, stale quotient, mixed schedule, wrong occurrence, wrong generation, all three scanner orders, O/A, occurrence folds, vestigial/static cases, operational threading, outer schedules, and full pipeline were rerun. Two obsolete round-6 bridge probes first failed on signature drift and were corrected before classification (Probes 60–65). |
| 5 | Exactly 30 holes; exact raw 82–142; concrete gates | **Arithmetic/count addressed, estimate authorization not.** Exact split and sum pass (Probes 53–54). The bridge-authenticity and source-occurrence-label redesigns add work not represented by the current phase grades. |

## End-to-end pipeline attack

1. Both sides compose through split deletion, closing-free sorting/accounting, and `IndependentCanonicalSchedule`.
2. O19 membership matching and sealed operational selection feed O20; old public-certificate pollution remains closed.
3. The strengthened whole-block record prevents a zero-node actor step and admits 1×1, 2×1, and 2×2 Cartesian *label sets*.
4. O20 feeds the new schedule-indexed bridge; O21 and the exact outer constructor compose with no external scanner/bridge premise.
5. The full wrapper elaborates to immutable `ConfluenceResult` (Probe 51).
6. This wrapper remains type-correct only because the two affected hard producers are holes. The current types do not force (a) canonical maps to be the maps constructed by deletion/sorting replay, or (b) each Cartesian label to identify the actual selected-block source occurrence crossed by its node. Probes 27/50 demonstrate those missing constraints directly.

## Numbered findings

1. **blocker — the accepted-generation bridge equation is relative to forgeable canonical maps** (`src/DGamma/CP3.idr:3109–3150`; `research/DGamma/CP5ConfluenceCanonicalSortSpike.idr:241ff`; `research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr:125–173`). The immutable `CanonicalRegistrationCorrespondence` gives a generation-level accounting bijection, but no field ties `canonicalToOriginal` to the deletion/sorting `ActionRegistrationReplayCorrespondence`. `IndependentCanonicalSchedule` likewise carries effect replay correspondence and a deleted classifier, not equality between the tree map and an occurrence-replay origin. `R7CanonicalMapPermutationPositive.idr` typechecks three complete constructions: compose a no-withdrawal canonical tree with an occurrence-generation automorphism, install any alternate valid tree in a schedule without changing another field, and clone the enriched capital while reusing every other proof. The revised bridge then accepts equations through that synthetic tree. `R7TwoOccurrencePermutationPositive.idr` checks the nontrivial core: exactly two distinct same-action births admit an involutive ordinal swap. Therefore a wrong canonical-right birth can be made to satisfy the nominal “original-generation” equation by permuting the left (or right) canonical map. Round-6 Probe 24 is closed only for a fixed honest map; authenticity is not represented by the universal input type.

2. **blocker — Cartesian labels do not identify source transition occurrences** (`research/DGamma/CP5ConfluenceCrossTraceSpike.idr:132–265`). `TraceActionTagAt` proves only that a source block position has the same `Action` and `RuleTag` as the current derivation node. Repeated L-Iter steps can share both. `R7WholeBlockDuplicateLabelAttack.idr` constructs, for the exact same one-node `FiniteAdjacentSwapDerivation`, valid `DerivationCrossesBlockPositions` values labeling that node at source position 0 and at source position 1 whenever both positions have its action/tag. `UniqueKeys` and node count constrain only the chosen pair labels; they do not prove the node-to-original-occurrence map is injective or even correct. Literal duplicate labels are rejected, but a duplicate/degenerate node can be assigned another indistinguishable unused position. The witness must use occurrence origins/ordinals through the composed operational correspondence, not action/tag equality alone.

3. **major — the 82–142 arithmetic is exact but the estimate is not authorization-ready** (`THM73-PLAN.md`, phases B/G). The phase rows really sum to 82–142 and all three gates are concrete. Nevertheless, Finding 1 adds an authenticated canonical-registration occurrence companion across deletion, sorting, enriched schedule assembly, bridge, and O21; Finding 2 adds prefix-fold occurrence identity to every whole-block node and its Cartesian proof. Those are interface redesigns in the two dominant phases, not implementation details already covered by the named outputs. Re-estimate after corrected types and positive/negative probes; a temporary envelope of roughly **90–160** is more credible than retaining 82–142 silently.

## Positive results / non-findings

- Immutable `CP3.idr` remains blob `2c697e532e83989de8591fa6a4378747c6a501c0`; `git diff 34b21c9..139237a -- src dgamma.ipkg` is empty.
- All five research spikes elaborate serially; exact external release build passes 207/207.
- Exact hole split is 6/4/10/8/2 = 30; production and reachable package source contain no named holes or escape hatches.
- O7 scan, O8 selection, O9 enrichment, O10 core, and O11 accounting are independently callable; compatibility wrappers contain no holes.
- Sealing still rejects old pure/outer pollution, safety detachment, generated-child licensing, wrong trace, stale quotient, mixed schedule, and occurrence-relation detachment.
- The old alternate-right-occurrence bridge attack fails only at the new generation equation when schedule maps are held fixed.
- One real node is sufficient for 1×1; two and four labeled nodes are sufficient for 2×1 and 2×2. No count overshoot was found.
- All three concrete scanner orderings expose exact full-index and deleted-list equalities; wrong birth ordinal substitution fails.
- The external full producer/consumer wrapper requires no extra premise and returns the immutable target result type.

## Residual risks

- All 30 hard research bodies remain holes by design; interface elaboration does not establish theorem truth.
- `selectOperationalCanonicalPermutationSpike` remains an unproved universal safe-selector existence theorem for schedules differing through withdrawn intermediates.
- The first actual non-singleton whole-block producer may require stronger intermediate occurrence-origin capital once Finding 2 is repaired.
- O/A and O/O applicability and the accepted scanner inductions remain high mathematical gates.
- Static one/moved/two-intermediate models are honestly not concrete reachable O19/O20 executions.
- Literal status includes pre-existing untracked `paper/` and this mandated report; tracked paths and the git index are clean.

## Estimate assessment

- **Arithmetic:** PASS, exactly 82–142, no overlap subtraction.
- **Gates:** PASS as concrete text (general Cartesian producer, split deletion pipeline, accepted scanner proof).
- **Grades:** FAIL for authorization after the probes. Phase B must include occurrence-authenticated node labeling; phase G (and likely O16/O18) must include canonical-map authenticity. Do not authorize 82–142 unchanged. Re-estimate after the repaired 2×2 producer and synthetic-map negative pass; use approximately 90–160 only as a temporary planning envelope.

## Exact changes required for round 8

1. **Authenticate each canonical map without changing production `CP3`.** Add a research-only enriched companion tying, for every canonical generated occurrence, `canonicalToOriginal (canonicalRegistrationTree schedule)` to the exact source occurrence selected by a deletion+sorting `ActionRegistrationReplayCorrespondence` (prefer exact occurrence equality; at minimum exact original generation plus an injective occurrence-origin law). Construct it in the one-trace producer and carry it in `IndependentCanonicalSchedule`.
2. **Make the bridge consume authenticated enriched capitals, not arbitrary public schedules alone.** Its accepted-forward equation must use the authenticated source/right original occurrences. The complete enriched-clone in Probe 81 and the no-withdrawal permutation in Probe 27 must fail before the bridge equation can be supplied. Retain the fixed-map round-6 wrong-birth negative and actual-direction positive.
3. **Replace action/tag-only Cartesian labels with occurrence-authenticated labels.** Each finite node must expose its located occurrence in the current trace, map it through the composed prefix `ActionRegistrationReplayCorrespondence` to the original source trace, and prove that origin is the exact transition occurrence/ordinal at the selected block position. Repeated identical L-Iter action/tag pairs must remain distinguishable.
4. **Add a real duplicate/shifted-node negative.** Probe 50's same-node position-0/position-1 relabeling must fail. Retain literal duplicate-label rejection and positive 1×1, 2×1, 2×2 producers; the corrected 2×2 producer must receive no premise unavailable from the actual intermediate replay fold.
5. **Update hole mapping and estimates honestly.** If authentication and occurrence-label producers add holes, revise the exact count/reverse O1–O23 map. Re-estimate phases B/F/G from corrected elaborated interfaces rather than carrying 82–142 forward.
6. **Retain all current closure/hygiene tests.** Re-run the complete negative/scanner/static/full-pipeline suite, all five spike checks, immutable blob/source diff, research isolation, 207/207 release build, and no-staged/tracked-change checks.

## Final verdict

**REJECT.** Revision 7 genuinely fixes the deletion producer split, zero-node terminator, fixed-map wrong-birth equation, hole arithmetic, and retained regressions. It is still not ready for the proof grind: caller-valid canonical occurrence maps can be permuted and reused throughout the enriched schedule/bridge pipeline, and Cartesian labels identify only action/tag rather than the actual selected-block source occurrence. Both are interface-strength defects demonstrated by checked positive attack modules.

**Final verdict: REJECT**
