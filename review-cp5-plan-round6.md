# Theorem 73 scoping plan — adversarial review, round 6

Reviewed branch `cp5-thm73-scoping` at requested commit `b220287` under the round-6 protocol. Production sources were treated as read-only; all type-checking probes were created under `/tmp/thm73-review6-probes/`.

## Probe log

### Probe 1 — requested revision, branch, and release-source delta
`git rev-parse --abbrev-ref HEAD; git rev-parse HEAD; git diff --exit-code 34b21c9..b220287 -- src dgamma.ipkg`
branch=cp5-thm73-scoping
HEAD=b2202876410568ea49fb2d393d1216666aba12ad
release delta: empty (exit 0)

**Result:** revision/branch recorded; release-source delta classification: **note**.

### Probe 2 — immutable CP3 blob and initial worktree hygiene
`git hash-object src/DGamma/CP3.idr; git status --short`
CP3 blob=2c697e532e83989de8591fa6a4378747c6a501c0
?? paper/
?? review-cp5-plan-round6.md
**Result:** immutable target blob matches: **note/pass**.

### Probe 3 — prior rejection front and revision-6 plan reconstructed
`read review-cp5-plan-round1.md .. round5.md and THM73-PLAN.md in full`
Round 5 requires sealing arbitrary certificate pollution, a separately scoped current-state one-step producer, action/registration occurrence composition into the bridge, honest four-fiber labels, exact scanner fixtures, exact 75–130 arithmetic, and full closure probes. Revision 6 claims exactly those changes and 27 research holes.

**Result:** checklist reconstructed from prior reports rather than trusting revision-6 prose. **Classification: note.**

### Probe 4 — revision-6 change surface
`git diff --stat/name-status be29a18..b220287; git log --oneline be29a18..b220287`
 THM73-PLAN.md                                      | 415 +++++++++++--------
 research/DGamma/CP5ConfluenceCrossTraceSpike.idr   | 446 +++++++++++++++------
 research/DGamma/CP5ConfluenceLocalDiamondSpike.idr | 180 +++++++++
 .../CP5ConfluenceRenamingCompositionSpike.idr      | 300 +++++++++++---
 review-cp5-plan-round5.md                          | 369 +++++++++++++++++
 5 files changed, 1376 insertions(+), 334 deletions(-)
M	THM73-PLAN.md
M	research/DGamma/CP5ConfluenceCrossTraceSpike.idr
M	research/DGamma/CP5ConfluenceLocalDiamondSpike.idr
M	research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
A	review-cp5-plan-round5.md
b220287 Revise Theorem 73 plan after round 5
7e71132 Export exact CP5 scanner fixture indices
32493a4 Index CP5 scanner events by exact generations
72a3f71 Seal CP5 actor permutations with operational evidence
c99e540 Index CP5 endpoint bridge by action occurrences
39ffe01 Classify CP5 finite adjacent swap derivations
b9bc7a0 Retain CP5 action occurrence replay capital
28b0b12 Record CP5 plan adversarial review round 5

**Result:** recorded actual revision surface. **Classification: note.**

### Probe 5 — actual research-interface diff captured
`git diff --unified=100 be29a18..b220287 -- research/DGamma/CP5Confluence*Spike.idr`
diff lines=    2019
**Result:** exact interface diff captured outside the repository for declaration-level review. **Classification: note.**

### Probe 6 — immutable external release/spike trees
`git archive b220287 -> /tmp/thm73-review6-probes; copy exact release src + five spikes`
release Idris files=207; spike-tree Idris files=212
release CP3 blob=2c697e532e83989de8591fa6a4378747c6a501c0; spike CP3 blob=2c697e532e83989de8591fa6a4378747c6a501c0
active Idris before checks: none
**Result:** exact external tree established; CP3 matches immutable blob. **Classification: note/pass.**

### Probe 7 — revision-6 declaration inventory
`line-level inspection of changed local-diamond, cross-trace, and renaming/scanner declarations`
Observed actual types: `MappedCanonicalSupportOrders` has only two erased membership maps; `CertifiedOperationalCanonicalPermutation` existentially stores certificate/target trace/blocks/bundle plus `OperationalActorPermutation`; each recursive actor step contains current-state `AdjacentActorSwapSafety` and a safety-indexed `OperationalAdjacentBlockSwap`; every block step contains a `FiniteAdjacentSwapDerivation`; O20 consumes the sealed operational value, not matching alone. Action/registration correspondence has target→source action occurrence, tag equality, generated occurrence origin, and a replay-generation bijection equation. Scanner fixtures and exact equalities are real complete declarations.
**Result:** advertised surface exists; producer inhabitability/coupling remains to be attacked. **Classification: note.**

### Probe 8 — local-diamond/occurrence spike elaboration
`idris2 --source-dir src --check src/DGamma/CP5ConfluenceLocalDiamondSpike.idr`
exit=0
24/31: Building DGamma.CP4DeletionChildlessInvariant (src/DGamma/CP4DeletionChildlessInvariant.idr)
25/31: Building DGamma.CP4DeletionPlanComplete (src/DGamma/CP4DeletionPlanComplete.idr)
26/31: Building DGamma.CP4DeletionRetainedAction (src/DGamma/CP4DeletionRetainedAction.idr)
27/31: Building DGamma.CP4RuntimeBindings (src/DGamma/CP4RuntimeBindings.idr)
28/31: Building DGamma.CP4DeletionNoEpisodeReplay (src/DGamma/CP4DeletionNoEpisodeReplay.idr)
29/31: Building DGamma.CP4DeletionRelationalBoundary (src/DGamma/CP4DeletionRelationalBoundary.idr)
30/31: Building DGamma.CP4Support (src/DGamma/CP4Support.idr)
31/31: Building DGamma.CP5ConfluenceLocalDiamondSpike (src/DGamma/CP5ConfluenceLocalDiamondSpike.idr)
**Result:** spike elaborates serially, including occurrence composition and finite derivation folds. **Classification: note/pass.**

### Probe 9 — deletion-chain spike elaboration
`idris2 --source-dir src --check src/DGamma/CP5ConfluenceDeletionChainSpike.idr`
exit=137
 87/165: Building DGamma.CP4DeletionRelationalSuffixFold (src/DGamma/CP4DeletionRelationalSuffixFold.idr)
 88/165: Building DGamma.CP4TerminalRecovery (src/DGamma/CP4TerminalRecovery.idr)
 89/165: Building DGamma.CP4DeletionSelectedCloseEffect (src/DGamma/CP4DeletionSelectedCloseEffect.idr)
 90/165: Building DGamma.CP4DeletionSelectedForeignLifecycleCore (src/DGamma/CP4DeletionSelectedForeignLifecycleCore.idr)
 91/165: Building DGamma.CP4DeletionSelectedForeignLifecycleReplayCore (src/DGamma/CP4DeletionSelectedForeignLifecycleReplayCore.idr)
 92/165: Building DGamma.CP4DeletionSelectedForeignLifecycleUnload (src/DGamma/CP4DeletionSelectedForeignLifecycleUnload.idr)
 93/165: Building DGamma.CP4DeletionSelectedCloseBoundary (src/DGamma/CP4DeletionSelectedCloseBoundary.idr)
 94/165: Building DGamma.CP4DeletionSelectedEffectForeign (src/DGamma/CP4DeletionSelectedEffectForeign.idr)/opt/homebrew/bin/idris2: line 15: 45343 Killed: 9               "$DIR/idris2_app/idris2.so" "$@"
**Result:** elaboration failed. **Classification: blocker.**

### Probe 10 — killed deletion check cleanup and classification correction
`pgrep idris2; count TTC; inspect deletion log`
active=none
TTC count=109
 35 | 0 definedRelatedPost :
 36 |   PartialRelated state relation (Just left) (Just right) -> relation left right

 86/165: Building DGamma.CP4DeletionSuffixFold (src/DGamma/CP4DeletionSuffixFold.idr)
 87/165: Building DGamma.CP4DeletionRelationalSuffixFold (src/DGamma/CP4DeletionRelationalSuffixFold.idr)
 88/165: Building DGamma.CP4TerminalRecovery (src/DGamma/CP4TerminalRecovery.idr)
 89/165: Building DGamma.CP4DeletionSelectedCloseEffect (src/DGamma/CP4DeletionSelectedCloseEffect.idr)
 90/165: Building DGamma.CP4DeletionSelectedForeignLifecycleCore (src/DGamma/CP4DeletionSelectedForeignLifecycleCore.idr)
 91/165: Building DGamma.CP4DeletionSelectedForeignLifecycleReplayCore (src/DGamma/CP4DeletionSelectedForeignLifecycleReplayCore.idr)
 92/165: Building DGamma.CP4DeletionSelectedForeignLifecycleUnload (src/DGamma/CP4DeletionSelectedForeignLifecycleUnload.idr)
 93/165: Building DGamma.CP4DeletionSelectedCloseBoundary (src/DGamma/CP4DeletionSelectedCloseBoundary.idr)
 94/165: Building DGamma.CP4DeletionSelectedEffectForeign (src/DGamma/CP4DeletionSelectedEffectForeign.idr)/opt/homebrew/bin/idris2: line 15: 45343 Killed: 9               "$DIR/idris2_app/idris2.so" "$@"
**Result:** Probe 9 ended by signal 9/exit 137 after warnings only, so its automatic blocker label is superseded: infrastructure/resource failure, inconclusive. No process survived; retry serially with the retained exact-source cache. **Classification: note.**

### Probe 11 — deletion-chain spike elaboration retry
`idris2 --source-dir src --check src/DGamma/CP5ConfluenceDeletionChainSpike.idr` (retained exact-source cache)
exit=0
157/165: Building DGamma.CP4DeletionSelectedEpisodeAnchors (src/DGamma/CP4DeletionSelectedEpisodeAnchors.idr)
158/165: Building DGamma.CP4DeletionSelectedStart (src/DGamma/CP4DeletionSelectedStart.idr)
159/165: Building DGamma.CP4DeletionSelectedEpisodeFold (src/DGamma/CP4DeletionSelectedEpisodeFold.idr)
160/165: Building DGamma.CP4DeletionWithdrawalCurrent (src/DGamma/CP4DeletionWithdrawalCurrent.idr)
161/165: Building DGamma.CP4DeletionRetirementPersistence (src/DGamma/CP4DeletionRetirementPersistence.idr)
162/165: Building DGamma.CP4DeletionWithdrawalJoin (src/DGamma/CP4DeletionWithdrawalJoin.idr)
163/165: Building DGamma.CP4DeletionTheorem (src/DGamma/CP4DeletionTheorem.idr)
165/165: Building DGamma.CP5ConfluenceDeletionChainSpike (src/DGamma/CP5ConfluenceDeletionChainSpike.idr)
**Result:** passed 165-module closure; Probe 9 is conclusively non-defect. **Classification: note/pass.**

### Probe 12 — canonical-sort/enriched-schedule spike elaboration
`idris2 --source-dir src --check src/DGamma/CP5ConfluenceCanonicalSortSpike.idr`
exit=0
166/166: Building DGamma.CP5ConfluenceCanonicalSortSpike (src/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
**Result:** passed; simultaneous enriched schedule boundary remains valid. **Classification: note/pass.**

### Probe 13 — renaming/bridge/scanner spike elaboration
`idris2 --source-dir src --check src/DGamma/CP5ConfluenceRenamingCompositionSpike.idr`
exit=0
167/167: Building DGamma.CP5ConfluenceRenamingCompositionSpike (src/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
**Result:** passed, including concrete fixture `Refl` equalities and occurrence-indexed bridge. **Classification: note/pass.**

### Probe 14 — sealed cross-trace/O19/O20 spike elaboration
`idris2 --source-dir src --check src/DGamma/CP5ConfluenceCrossTraceSpike.idr`
exit=0
DGamma.CP5ConfluenceCrossTraceSpike:531:3--539:41
 531 | 0 permutationOccurrenceCorrespondence :
 532 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 533 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 534 |       rightCapital matching} ->
 535 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 536 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->

**Result:** passed; sealing and complete downstream wrappers are API/index-valid. **Classification: note/pass.**

### Probe 15 — round-5 pure certificate pollution at the sealed O20 type
`idris2 --source-dir src --check src/DGamma/R6OldPollutionNegative.idr` (expected failure)
exit=1
169/169: Building DGamma.R6OldPollutionNegative (src/DGamma/R6OldPollutionNegative.idr)
Error: While processing right hand side of oldPollutionReachesO20. When unifying:
    CertifiedActorPermutation name (supportOrder (canonicalSchedule leftCapital)) (map (renameBackward (currentNameBijection (endpointRenaming sameInputs))) (supportOrder (canonicalSchedule rightCapital)))
and:
    CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital ?matching
Mismatch between: CertifiedActorPermutation name (supportOrder (canonicalSchedule leftCapital)) (map (renameBackward (currentNameBijection (endpointRenaming sameInputs))) (supportOrder (canonicalSchedule rightCapital))) and CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital ?matching.

DGamma.R6OldPollutionNegative:42:54--42:62
 38 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational)
 39 | oldPollutionReachesO20 {nameEq} {keyEq} {protocol} {leftTrace} {rightTrace}
 40 |   {sameInputs} {leftCapital} {rightCapital} matching polluted =
 41 |     (polluted ** canonicalSchedulesConvergeSpike nameEq keyEq protocol leftTrace
 42 |       rightTrace sameInputs leftCapital rightCapital polluted)
                                                           ^^^^^^^^

**Result:** rejected at pure `CertifiedActorPermutation` versus sealed `CertifiedOperationalCanonicalPermutation`, before O20. **Classification: note/pass negative.**

### Probe 16 — polluted inner permutation wrapped in a fresh outer sealed package
`idris2 --source-dir src --check src/DGamma/R6OuterPollutionNegative.idr` (expected failure)
exit=1
169/169: Building DGamma.R6OuterPollutionNegative (src/DGamma/R6OuterPollutionNegative.idr)
Error: While processing right hand side of wrapPollutedOuter. Can't solve constraint between: base .selectedActorPermutation and ActorPermutationStep forward (ActorPermutationStep backward (selectedActorPermutation base)).

DGamma.R6OuterPollutionNegative:47:6--47:38
 43 |     (operationalTargetFinal base)
 44 |     (operationalTargetTrace base)
 45 |     (operationalTargetBlocks base)
 46 |     (operationalTargetPremises base)
 47 |     (selectedPermutationRealized base)
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

**Result:** old realization cannot be reindexed to the polluted outer certificate. **Classification: note/pass negative.**

### Probe 17 — detach per-step safety from its current intermediate state
`idris2 --source-dir src --check src/DGamma/R6SafetyDetachmentNegative.idr` (expected failure)
exit=1
169/169: Building DGamma.R6SafetyDetachmentNegative (src/DGamma/R6SafetyDetachmentNegative.idr)
Error: While processing right hand side of detachSafetyFromCurrentState. When unifying:
    AdjacentActorSwapSafety name key world error value protocol nameEq keyEq orderSwap firstTrace firstBlocks firstPremises
and:
    AdjacentActorSwapSafety name key world error value protocol nameEq keyEq orderSwap secondTrace secondBlocks secondPremises
Mismatch between: firstPremises and secondPremises.

DGamma.R6SafetyDetachmentNegative:33:39--33:45
 29 |   AdjacentActorSwapSafety name key world error value protocol nameEq keyEq
 30 |     orderSwap firstTrace firstBlocks firstPremises ->
 31 |   AdjacentActorSwapSafety name key world error value protocol nameEq keyEq
 32 |     orderSwap secondTrace secondBlocks secondPremises
 33 | detachSafetyFromCurrentState safety = safety
                                            ^^^^^^

**Result:** safety remains indexed by the exact current trace/blocks/bundle and cannot be detached. **Classification: note/pass negative.**

### Probe 18 — parent/child generated licensing rejection before O20
`idris2 --source-dir src --check src/DGamma/R6GeneratedChildSafetyPositive.idr`
exit=0
169/169: Building DGamma.R6GeneratedChildSafetyPositive (src/DGamma/R6GeneratedChildSafetyPositive.idr)
**Result:** exact headed `OInsert child (ChildOf parent)` contradicts `NoGeneratedChild child` without invoking O20. **Classification: note/pass.**

### Probe 19 — zero-node finite derivation inhabits a nontrivial block-step record conditionally
`idris2 --source-dir src --check src/DGamma/R6ZeroDerivationOperationalStep.idr`
exit=0
169/169: Building DGamma.R6ZeroDerivationOperationalStep (src/DGamma/R6ZeroDerivationOperationalStep.idr)
**Result:** passed. `OperationalAdjacentBlockSwap` does not require a nonempty finite derivation or tie its derivation to the selected actor blocks/order crossing; `FiniteAdjacentSwapDone` suffices whenever a target-order decomposition of the unchanged trace is supplied. This weakens the claim that every nontrivial block step contains concrete orientation-classified `AdjacentSwapResult`s. **Classification: major.**

### Probe 20 — external two-step action/registration correspondence fold
`idris2 --source-dir src --check src/DGamma/R6OccurrenceFoldPositive.idr`
exit=0
32/32: Building DGamma.R6OccurrenceFoldPositive (src/DGamma/R6OccurrenceFoldPositive.idr)
**Result:** action and generated origins compose definitionally through two steps; the composed replay-generation ordinal equation remains externally consumable. **Classification: note/pass.**

### Probe 21 — bridge exact canonical-source occurrence projection
`idris2 --source-dir src --check src/DGamma/R6BridgeSourcePositive.idr`
exit=1
DGamma.R6BridgeSourcePositive:39:5--39:6
 35 |   (sourceOccurrence : LocatedGeneratedRegistration child parent component source **
 36 |     sourceOccurrence = replayGeneratedRegistrationOrigin occurrences occurrence)
 37 | bridgeExposesExactReplaySource bridge occurrence =
 38 |   case replayedGeneratedBirthMatched bridge occurrence of
 39 |     (sourceOccurrence ** (exact, rightOccurrence ** unit)) =>
          ^

**Result:** failed. **Classification: major.**

### Probe 22 — bridge source projection retry after dependent-pair syntax fix
`idris2 --source-dir src --check src/DGamma/R6BridgeSourcePositive.idr`
exit=0
168/168: Building DGamma.R6BridgeSourcePositive (src/DGamma/R6BridgeSourcePositive.idr)
**Result:** passed. Probe 21 was only probe pattern syntax; exact source occurrence is externally projected. **Classification: note/pass.**

### Probe 23 — bridge right-occurrence/ordinal pollution
`idris2 --source-dir src --check src/DGamma/R6BridgeRightOccurrencePollution.idr`
exit=1
and:
    (n : name) -> (k : key) -> lookupBinding key ?value ?keyEq k (effectTables name key ?value world (projectEffectState ?error world key ?value name ?nameEq ?replayedLeftFinal) n) = lookupBinding key ?value ?keyEq k (effectTables name key ?value world (projectEffectState ?error world key ?value name ?nameEq (canonicalFinal ?rightSchedule)) (renameForward (replayBridgeBijection bridge) n))
Undefined name DGamma.Coeffects.lookupBinding. 

DGamma.R6BridgeRightOccurrencePollution:48:6--48:31
 44 |   MkReplayedCanonicalEndpointBridge
 45 |     (replayBridgeBijection bridge)
 46 |     (replayBridgeBijectionFixed bridge)
 47 |     (replayBridgeAmbient bridge)
 48 |     (replayBridgeTables bridge)
           ^^^^^^^^^^^^^^^^^^^^^^^^^

**Result:** pollution rejected. **Classification: note/pass negative.**

### Probe 24 — bridge right-occurrence pollution retry after direct coeffects import
`idris2 --source-dir src --check src/DGamma/R6BridgeRightOccurrencePollution.idr`
exit=0
168/168: Building DGamma.R6BridgeRightOccurrencePollution (src/DGamma/R6BridgeRightOccurrencePollution.idr)
**Result:** passed. Probe 23 failed only on a direct-import scope issue. The bridge permits arbitrary replacement of the right occurrence with any same child/parent/component birth, provides no generation/ordinal coherence to the accepted left↔right scanner bijection, and the exact O21 hole consumes it. **Classification: blocker.**

### Probe 25 — third scanner ordering L6,R9,R14,L18
`idris2 --source-dir src --check src/DGamma/R6ScannerThirdOrdering.idr`
exit=1
DGamma.R6ScannerThirdOrdering:74:33--74:37
 70 |   , indexedDeletedGenerations
 71 |       (thirdRight DGamma.R6ScannerThirdOrdering.thirdFinal) =
 72 |       [rightBirth14, rightBirth9]
 73 |   )
 74 | thirdDeletedListsExact = (Refl, Refl)
                                      ^^^^

**Result:** third ordering breaks exact fixture result. **Classification: major.**

### Probe 26 — third scanner ordering retry after direct DecEq import/qualification
`idris2 --source-dir src --check src/DGamma/R6ScannerThirdOrdering.idr`
exit=0
168/168: Building DGamma.R6ScannerThirdOrdering (src/DGamma/R6ScannerThirdOrdering.idr)
**Result:** passed. Probe 25 failed only on probe scope/auto-implicit names; full final index and exact deleted lists hold for L6,R9,R14,L18. **Classification: note/pass.**

### Probe 27 — retained scanner fixtures external equality consumers
`idris2 --source-dir src --check src/DGamma/R6ScannerRetainedFixturesPositive.idr`
exit=1
If Builtin.MkPair: DGamma.CP5ConfluenceRenamingCompositionSpike.concreteReorderedDeletedListsExact is not accessible in this context.

DGamma.R6ScannerRetainedFixturesPositive:39:37--39:71
 35 |      indexedDeletedGenerations (concreteRightIndex concreteReorderedFinalIndexes) =
 36 |         [rightBirth14, rightBirth9])
 37 |   )
 38 | consumeBothExactDeletedLists =
 39 |   (concreteTargetDeletedListsExact, concreteReorderedDeletedListsExact)
                                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

**Result:** consumer failed; inspect. **Classification: major.**

### Probe 28 — retained scanner equality consumers retry
`idris2 --source-dir src --check src/DGamma/R6ScannerRetainedFixturesPositive.idr`
exit=0
168/168: Building DGamma.R6ScannerRetainedFixturesPositive (src/DGamma/R6ScannerRetainedFixturesPositive.idr)
**Result:** passed after direct CP3 import and qualification. Both fixture families expose equality, not membership. **Classification: note/pass.**

### Probe 29 — wrong-generation scanner substitution
`idris2 --source-dir src --check src/DGamma/R6ScannerWrongGenerationNegative.idr` (expected failure)
exit=1
Error: While processing right hand side of conflateSameRawNameBirths. When unifying:
    Elem leftBirth18 [leftBirth18, leftBirth6]
and:
    Elem leftBirth6 [leftBirth18, leftBirth6]
Mismatch between: 12 and 0.

DGamma.R6ScannerWrongGenerationNegative:14:29--14:33
 10 | 0 conflateSameRawNameBirths :
 11 |   Elem DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth6
 12 |     [ DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18
 13 |     , DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth6 ]
 14 | conflateSameRawNameBirths = Here
                                  ^^^^

**Result:** exact birth ordinal prevents same-raw-name conflation. **Classification: note/pass negative.**

### Probe 30 — full-pipeline wrapper prepared at revision-6 boundaries
`adapt round-5 external wrapper to matching -> sealed selector -> O20`
**Result:** external wrapper created under `/tmp`, with no repository source edit. **Classification: note.**

### Probe 31 — complete published-boundary pipeline through sealed O19/O20/O21
`idris2 --source-dir src --check src/DGamma/R6FullPipeline.idr`
exit=0
169/169: Building DGamma.R6FullPipeline (src/DGamma/R6FullPipeline.idr)
**Result:** deletion → reduction → sorting → enriched schedules → membership match → sealed safe selector → O20 → O21 → immutable `ConfluenceResult` elaborates from exactly upstream premises. **Classification: note/pass.**

### Probe 32 — wrong operational bridge trace detachment
`idris2 --source-dir src --check src/DGamma/R6WrongTraceBridgeNegative.idr` (expected failure)
exit=1
169/169: Building DGamma.R6WrongTraceBridgeNegative (src/DGamma/R6WrongTraceBridgeNegative.idr)
Error: While processing right hand side of wrongTraceBridge. Can't solve constraint between: operational .operationalTargetFinal and otherFinal.

DGamma.R6WrongTraceBridgeNegative:36:60--36:89
 32 |     (canonicalTrace (canonicalSchedule leftCapital)) otherTrace) ->
 33 |   ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
 34 |     leftTrace rightTrace sameInputs (canonicalTrace (canonicalSchedule leftCapital))
 35 |     otherTrace otherOccurrences (canonicalSchedule rightCapital)
 36 | wrongTraceBridge convergence otherTrace otherOccurrences = convergenceBridge convergence
                                                                 ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

**Result:** inconclusive/unintended. **Classification: major.**

### Probe 33 — stale quotient from another sealed operational package
`idris2 --source-dir src --check src/DGamma/R6StaleQuotientNegative.idr` (expected failure)
exit=1
169/169: Building DGamma.R6StaleQuotientNegative (src/DGamma/R6StaleQuotientNegative.idr)
Error: While processing right hand side of staleQuotient. When unifying:
    firstOp .operationalTargetFinal
and:
    secondOp .operationalTargetFinal
Mismatch between: firstOp and secondOp.

DGamma.R6StaleQuotientNegative:33:47--33:80
 29 |   (second : PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 30 |     leftTrace rightTrace sameInputs leftCapital rightCapital secondOp) ->
 31 |   RelationalReplayEndpoint name key world error value nameEq keyEq
 32 |     (canonicalFinal (canonicalSchedule leftCapital)) (operationalTargetFinal secondOp)
 33 | staleQuotient firstOp secondOp first second = composedPermutationEndpoint first
                                                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

**Result:** endpoint quotient remains package-value indexed and cannot go stale. **Classification: note/pass negative.**

### Probe 34 — mixed canonical schedule substitution into O21
`idris2 --source-dir src --check src/DGamma/R6MixedScheduleNegative.idr` (expected failure)
exit=1
169/169: Building DGamma.R6MixedScheduleNegative (src/DGamma/R6MixedScheduleNegative.idr)
Error: While processing right hand side of mixedLeftSchedule. When unifying:
    CanonicalConvergenceResult name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital operational
and:
    CanonicalConvergenceResult name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs otherLeft rightCapital operational
Mismatch between: leftCapital and otherLeft.

DGamma.R6MixedScheduleNegative:34:41--34:52
 30 |     (currentNameBijection (endpointRenaming sameInputs))
 31 | mixedLeftSchedule {nameEq} {keyEq} {protocol} {leftTrace} {rightTrace} {sameInputs}
 32 |   leftCapital otherLeft rightCapital convergence =
 33 |     originalEndpointsConvergeSpike nameEq keyEq protocol leftTrace rightTrace
 34 |       sameInputs otherLeft rightCapital convergence
                                              ^^^^^^^^^^^

**Result:** O21 cannot mix another enriched left schedule with the convergence package. **Classification: note/pass negative.**

### Probe 35 — wrong-trace diagnostic classification correction
`inspect /tmp/.../wrong-trace.log`
The diagnostic rejects `operational.operationalTargetFinal` versus `otherFinal`; this is the intended dependent trace/final detachment failure. Probe 32’s grep expected the trace spelling and was too narrow.
**Result:** wrong-trace negative passes. **Classification: note/pass negative.**

### Probe 36 — round-5 static intermediate-vestigial mutations copied to exact revision 6
`copy/rename R5 four-fiber and two-intermediate external models under /tmp`
**Result:** prepared static mutation regressions only; no reachable/O19/O20 execution claim. **Classification: note.**

### Probe 37 — one/moved-intermediate four-fiber static model
`idris2 --source-dir src --check src/DGamma/R6FourFiberStatic.idr`
exit=1
DGamma.R6FourFiberStatic:448:19--448:45
 444 | 0 rightLicensingEndpointCannotBeWellFormed :
 445 |   registryWellFormed @{the (DecEq N) %search} @{the (DecEq K) %search}
 446 |     DGamma.R5FourFiberPositive.rightLicensingState = True -> Void
 447 | rightLicensingEndpointCannotBeWellFormed wellFormed =
 448 |   let childless = wellFormedAbsentHasNoChild (the (DecEq N) %search)
                         ^^^^^^^^^^^^^^^^^^^^^^^^^^

**Result:** static regression failed. **Classification: major.**

### Probe 38 — static mutation probe module-qualification correction
`replace old external module qualifiers after renaming`
**Result:** Probe 37 was a probe-copy namespace failure, not a revision defect; corrected both static modules for retry. **Classification: note.**

### Probe 39 — four-fiber static model retry
`idris2 --source-dir src --check src/DGamma/R6FourFiberStatic.idr`
exit=0
169/169: Building DGamma.R6FourFiberStatic (src/DGamma/R6FourFiberStatic.idr)
**Result:** passed after qualifier correction. **Classification: note/pass.**

### Probe 40 — two unsupported intermediaries static mutation
`idris2 --source-dir src --check src/DGamma/R6TwoIntermediateStatic.idr`
exit=0
169/169: Building DGamma.R6TwoIntermediateStatic (src/DGamma/R6TwoIntermediateStatic.idr)
**Result:** exact multi-intermediate path/absence/pure-target static regression remains accepted. **Classification: note/pass.**

### Probe 41 — safe-selector existence on withdrawn-intermediate schedules
`grep retained artifacts for concrete IndependentCanonicalSchedule/CertifiedOperationalCanonicalPermutation fixtures; compare static models to selector input`
relevant textual hits=6
The checked one/moved/two-intermediate artifacts instantiate endpoint/path states and pure actor targets only. The branch contains no concrete reachable trace, `IndependentCanonicalSchedule`, or operational package for that model. Conversely the static model alone cannot refute the sealed type: its omitted intermediate induces a support path/order difference, but `AdjacentActorSwapSafety` checks direct generated-child licensing while actual local-diamond existence is stored only in the finite derivation. I could neither inhabit nor refute `CertifiedOperationalCanonicalPermutation` for an accepted two-schedule withdrawn-intermediate instance without assuming the very O19/O20 holes under review.
**Result:** the selector’s universal existence remains a genuine explicitly named XL mathematical gate, not a closed producer regression. This is a high residual risk, but revision 6 describes it honestly rather than asserting it proved. **Classification: major residual risk/note, not a checked counterexample.**

### Probe 42 — public ConfluenceResult retains the original valid schedule values
`idris2 --source-dir src --check src/DGamma/R6OuterSchedulesPositive.idr`
exit=0
169/169: Building DGamma.R6OuterSchedulesPositive (src/DGamma/R6OuterSchedulesPositive.idr)
**Result:** both `leftCanonical` and `rightCanonical` reduce definitionally to the exact supplied original schedules. **Classification: note/pass.**

### Probe 43 — occurrence correspondence through recursive operational actor fold
`idris2 --source-dir src --check src/DGamma/R6OperationalOccurrenceFoldPositive.idr`
exit=0
169/169: Building DGamma.R6OperationalOccurrenceFoldPositive (src/DGamma/R6OperationalOccurrenceFoldPositive.idr)
**Result:** each recursive actor step exposes exact finite-step origin composed with the rest fold. **Classification: note/pass.**

### Probe 44 — bridge occurrence-relation detachment
`idris2 --source-dir src --check src/DGamma/R6WrongOccurrenceBridgeNegative.idr` (expected failure)
exit=1
Error: While processing right hand side of detachBridgeOccurrenceRelation. When unifying:
    ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs source replayed first rightSchedule
and:
    ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs source replayed second rightSchedule
Mismatch between: first and second.

DGamma.R6WrongOccurrenceBridgeNegative:31:54--31:60
 27 |   ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
 28 |     leftTrace rightTrace sameInputs source replayed first rightSchedule ->
 29 |   ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
 30 |     leftTrace rightTrace sameInputs source replayed second rightSchedule
 31 | detachBridgeOccurrenceRelation first second bridge = bridge
                                                           ^^^^^^

**Result:** bridge remains value-indexed by the exact fold-produced occurrence correspondence. **Classification: note/pass negative.**

### Probe 45 — exact named research-hole inventory
`regex-scan ?identifier across the five CP5 research spikes`
CP5ConfluenceCanonicalSortSpike.idr 6
  closingFreeTraceShapeSpike_rhs
  supportOrderingSpike_rhs
  sortClosingFreeTraceSpike_rhs
  canonicalSupportTransportSpike_rhs
  deletionSortingOrchestrationAccountingSpike_rhs
  independentCanonicalScheduleSpike_rhs
CP5ConfluenceCrossTraceSpike.idr 4
  operationalAdjacentBlockSwapSpike_rhs
  canonicalSupportOrdersMatchSpike_rhs
  selectOperationalCanonicalPermutationSpike_rhs
  canonicalSchedulesConvergeSpike_rhs
CP5ConfluenceDeletionChainSpike.idr 7
  deletedClassificationForcesLeftScannerDiscardSpike_rhs
  deletedClassificationForcesRightScannerDiscardSpike_rhs
  sameExternalOrchestrationReflexiveSpike_rhs
  sameExternalOrchestrationTransitiveSpike_rhs
  traceIndependentAfterDeletionReplaySpike_rhs
  chooseClosingStepSpike_rhs
  deleteAllClosingEpisodesSpike_rhs
CP5ConfluenceLocalDiamondSpike.idr 8
  traceIndependentAfterRelationalReplaySpike_rhs
  relationalReplayEndpointReflexiveSpike_rhs
  relationalReplayEndpointTransitiveSpike_rhs
  activationActivationDiamondSpike_rhs
  activationOrchestrationDiamondSpike_rhs
  orchestrationActivationDiamondSpike_rhs
  orchestrationOrchestrationDiamondSpike_rhs
  adjacentSwapSuffixSpike_rhs
CP5ConfluenceRenamingCompositionSpike.idr 2
  composeModuloVestigialEndpointSpike_rhs
  replayedCanonicalToOriginalEndpointSpike_rhs
TOTAL 27
**Result:** exactly 27 unique named holes: canonical 6, cross-trace 4, deletion 7, local 8, renaming 2, matching the claim. **Classification: note/pass.**

### Probe 46 — estimate arithmetic and concrete re-estimation gates
`parse eight phase rows and gate text in THM73-PLAN.md`
[('A', 4, 8), ('B', 12, 21), ('C', 8, 15), ('D', 8, 15), ('E', 7, 13), ('F', 9, 16), ('G', 25, 37), ('H', 2, 5)]
sum 75 130
gate-block-swap True
gate-scanner True
**Result:** raw rows sum exactly 75–130 with no subtraction; gates name the first complete safety-indexed whole-block producer and first accepted-correspondence same-name scanner proof. **Classification: note/pass arithmetic.**

### Probe 47 — hole-to-obligation reconciliation
`map each of the 27 identifiers from Probe 45 to Section 6 obligations`
- O1: same-external reflexive/transitive, replay endpoint reflexive/transitive, generic modulo-vestigial composition.
- O2: generic replay independence and deletion specialization.
- O3/O4/O5: A/A, A/O+O/A, and O/O holes respectively.
- O6: adjacent suffix replay plus separately named whole-block producer.
- O8: closing-step selector; O10/O11: delete-all/history assembly.
- O12/O14/O15/O16/O17: closing-free shape, support ordering, support bridge, orchestration accounting, sorting.
- O11/O18 boundary: `independentCanonicalScheduleSpike_rhs` supplies the cumulative classifier to the already complete O18 constructor; it is not another schedule-constructor theorem.
- O19: membership matching and separately named sealed selector.
- O20: canonical convergence/occurrence bridge.
- O21: two accepted scanner discard inductions plus replayed endpoint composition.
O7/O9/O13/O18/O22/O23 are represented by executable records/wrappers or work inside the larger typed deletion producer rather than additional top-level holes. No count is silently lost, but Probe 19 shows O6’s named whole-block hole output does not encode the advertised nonempty Cartesian-crossing property.
**Result:** count/table reconciliation succeeds; obligation-strength caveat recorded under O6. **Classification: major caveat.**

### Probe 48 — reverse obligation-to-hole reconciliation exposes hidden scopes
`inspect ClosingStepChoice/DeletionChainStep producer declarations and grep for standalone O7/O9 producers`
research/DGamma/CP5ConfluenceDeletionChainSpike.idr:116:0 deletedClassificationForcesLeftScannerDiscardSpike :
research/DGamma/CP5ConfluenceDeletionChainSpike.idr:138:0 deletedClassificationForcesRightScannerDiscardSpike :
There is one `chooseClosingStepSpike` hole returning `ClosingStepChoice`; its `HasClosingStep` branch simultaneously requires both the O8 maximal candidate and a full O9 `DeletionChainStep`. No standalone executable O7 closed/open scanner/uniqueness producer or O9 enriched one-step D72 producer is stated. Thus the forward hole→obligation map in Probe 47 succeeds, but the required reverse “no obligation hidden inside another hole” condition fails: O7, O8, and O9 are collapsed into one hole. O10/O11 are likewise both inside `deleteAllClosingEpisodesSpike`, though the record at least exposes their outputs.
**Result:** claimed 27 count is exact, but the obligation table is not one-to-one or independently gateable at O7/O9 as advertised. **Classification: major.**

### Probe 49 — exact external release package build
`idris2 --build dgamma.ipkg` in exact b220287 archive (byte-identical production TTC cache seeded)
exit=0
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
**Result:** release package passes 207/207; research and external probes are not package modules. **Classification: note/pass.**

### Probe 50 — escape/reachability/immutability and final repository hygiene
`scan production/research; git diff/index/status; CP3 blob`
production forbidden hits: 0
production research-reachability hits: 0
research non-hole escape hits: 0
tracked diff paths: none
staged paths: none
CP3 blob=2c697e532e83989de8591fa6a4378747c6a501c0
## cp5-thm73-scoping...origin/cp5-thm73-scoping [ahead 33]
?? paper/
?? review-cp5-plan-round6.md
**Result:** production/release hygiene passes; no staged/tracked changes. Untracked `paper/` and mandated reports remain outside the index. **Classification: note/pass.**

### Probe 51 — exact source locations for consolidated findings
`nl -ba relevant research declarations`
   430	    AdjacentSwapOrientationEvidence left right
   431	
   432	||| A finite whole-block replay is not an assertion about its endpoint.  It is
   433	||| an explicit list of source-sensitive adjacent transpositions, each carrying
   434	||| the concrete A/A, A/O, O/A, or O/O `LocalRelationalDiamond` and the complete
   435	||| `AdjacentSwapResult` returned by suffix replay.
   436	public export
   437	data FiniteAdjacentSwapDerivation :
   438	  (name, key, world, error : Type) -> (value : key -> Type) ->
   439	  (protocol : RegistrationProtocol key value world error) ->
   440	  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
   441	  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
   442	  Transitions initial sourceFinal -> Transitions initial targetFinal -> Type where
   443	  FiniteAdjacentSwapDone :
   444	    FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq
   445	      trace trace
   446	  FiniteAdjacentSwapStep :
   447	    {initial, pairFirst, pairMiddle, pairFinal, originalFinal, targetFinal :
   448	      SystemState name key value world error} ->
   449	    (original : Transitions initial originalFinal) ->
   450	    (prefixTrace : Transitions initial pairFirst) ->
   451	    (left : Transition pairFirst pairMiddle) ->
   452	    (right : Transition pairMiddle pairFinal) ->
   453	    (suffix : Transitions pairFinal originalFinal) ->
   454	    (orientation : AdjacentSwapOrientationEvidence left right) ->
   455	    (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
   456	      left right) ->
   457	    (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
   458	      original prefixTrace left right suffix diamond) ->
   459	    (target : Transitions initial targetFinal) ->
   460	    (rest : FiniteAdjacentSwapDerivation name key world error value protocol
   461	      nameEq keyEq (swappedTrace result) target) ->
   462	    FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq
   463	      original target
   464	
   465	public export
   130	||| its concrete `AdjacentSwapResult`, including action/registration occurrence
   131	||| correspondence.  Endpoint assertions alone cannot construct this record.
   132	public export
   133	record OperationalAdjacentBlockSwap
   134	  (name, key, world, error : Type) (value : key -> Type)
   135	  (protocol : RegistrationProtocol key value world error)
   136	  (nameEq : DecEq name) (keyEq : DecEq key)
   137	  {sourceOrder, targetOrder : List name}
   138	  (orderSwap : AdjacentActorOrderSwap name sourceOrder targetOrder)
   139	  {initial, sourceFinal : SystemState name key value world error}
   140	  (sourceTrace : Transitions initial sourceFinal)
   141	  (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
   142	    sourceOrder sourceTrace)
   143	  (sourcePremises : ReplayInvariantBundle name key world error value protocol
   144	    nameEq keyEq sourceTrace)
   145	  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq
   146	    keyEq orderSwap sourceTrace sourceBlocks sourcePremises) where
   147	  constructor MkOperationalAdjacentBlockSwap
   148	  blockSwapFinal : SystemState name key value world error
   149	  blockSwapTrace : Transitions initial blockSwapFinal
   150	  blockSwapFiniteDerivation : FiniteAdjacentSwapDerivation name key world error
   151	    value protocol nameEq keyEq sourceTrace blockSwapTrace
   152	  blockSwapBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
   153	    targetOrder blockSwapTrace
   154	  blockSwapEndpoint : RelationalReplayEndpoint name key world error value nameEq
   155	    keyEq sourceFinal blockSwapFinal
   156	  blockSwapPremises : ReplayInvariantBundle name key world error value protocol
   157	    nameEq keyEq blockSwapTrace
   158	  blockSwapSameExternalInputs : SameExternalOrchestration nameEq sourceTrace
   159	    blockSwapTrace
   160	
   161	public export
   162	0 blockSwapReplayCorrespondence :
   163	  (step : OperationalAdjacentBlockSwap name key world error value protocol nameEq
   164	    keyEq orderSwap sourceTrace sourceBlocks sourcePremises safety) ->
   165	  RelationalReplayCorrespondence name key world error value sourceTrace
   166	    (blockSwapTrace step)
   167	blockSwapReplayCorrespondence step =
   168	  finiteDerivationReplayCorrespondence (blockSwapFiniteDerivation step)
   169	
   170	public export
   171	0 blockSwapOccurrenceCorrespondence :
   172	  (step : OperationalAdjacentBlockSwap name key world error value protocol nameEq
   173	    keyEq orderSwap sourceTrace sourceBlocks sourcePremises safety) ->
   174	  ActionRegistrationReplayCorrespondence name key world error value sourceTrace
   175	    (blockSwapTrace step)
   176	blockSwapOccurrenceCorrespondence step =
   177	  finiteDerivationOccurrenceCorrespondence (blockSwapFiniteDerivation step)
   178	
   179	||| Exact one-step operational producer.  Its proof must enumerate the finite
   180	||| Cartesian crossing of the two located blocks, derive early applicability and
   181	||| orientation-specific premises from the current bundle/safety, invoke the
   182	||| four local diamonds, and splice every `AdjacentSwapResult`.
   183	public export
   184	0 operationalAdjacentBlockSwapSpike :
   185	  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
   186	  (protocol : RegistrationProtocol key value world error) ->
   187	  {sourceOrder, targetOrder : List name} ->
   188	  (orderSwap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
   189	  {initial, sourceFinal : SystemState name key value world error} ->
   190	  (sourceTrace : Transitions initial sourceFinal) ->
   191	  (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
   192	    sourceOrder sourceTrace) ->
   193	  (sourcePremises : ReplayInvariantBundle name key world error value protocol
   194	    nameEq keyEq sourceTrace) ->
   195	  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq
   196	    keyEq orderSwap sourceTrace sourceBlocks sourcePremises) ->
   197	  OperationalAdjacentBlockSwap name key world error value protocol nameEq keyEq
   198	    orderSwap sourceTrace sourceBlocks sourcePremises safety
   199	operationalAdjacentBlockSwapSpike = ?operationalAdjacentBlockSwapSpike_rhs
   200	
   201	||| Every selected list step is now indexed by exact operational safety and its
   202	||| realized block replay.  A caller cannot prepend a pure swap/inverse loop
   203	||| without also constructing both intermediate safety proofs and finite local
   204	||| diamond derivations.
   205	public export
   145	    worldState (canonicalFinal rightSchedule)
   146	  0 replayBridgeTables : (n : name) -> (k : key) ->
   147	    lookupBinding {key = key} {value = value} k
   148	      (effectTables (projectEffectState @{nameEq} replayedLeftFinal) n) =
   149	    lookupBinding {key = key} {value = value} k
   150	      (effectTables (projectEffectState @{nameEq}
   151	        (canonicalFinal rightSchedule))
   152	        (renameForward replayBridgeBijection n))
   153	  0 replayBridgeControls : (n : name) ->
   154	    MaybeFiberRelatedBy replayBridgeBijection
   155	      (lookupFiber @{nameEq} {key = key} {value = value} {world = world}
   156	        {error = error} n (registry replayedLeftFinal))
   157	      (lookupFiber @{nameEq} {key = key} {value = value} {world = world}
   158	        {error = error} (renameForward replayBridgeBijection n)
   159	        (registry (canonicalFinal rightSchedule)))
   160	  0 replayedGeneratedBirthMatched :
   161	    {child, parent : name} ->
   162	    {component : Component key value world error} ->
   163	    (replayedOccurrence : LocatedGeneratedRegistration child parent component
   164	      replayedLeftTrace) ->
   165	    (sourceOccurrence : LocatedGeneratedRegistration child parent component
   166	      sourceCanonicalTrace **
   167	      (sourceOccurrence = replayGeneratedRegistrationOrigin replayedOccurrences
   168	        replayedOccurrence,
   169	       (rightOccurrence : LocatedGeneratedRegistration
   170	         (renameForward replayBridgeBijection child)
   171	         (renameForward replayBridgeBijection parent) component
   172	         (canonicalTrace rightSchedule) ** Unit)))
   173	
   174	||| Typed link from each one-trace withdrawal to the accepted two-trace
   175	||| registration scanner.  The trace correspondence is exposed at its exact
   176	||| index, and every canonical endpoint withdrawal is a member of the scanner's
   177	||| left/right deleted-generation list with its original closed-parent
   178	||| classification still available.
   195	    nameEq keyEq (survivingTrace deletionResult)
   196	  0 deletionStrictlyShorter :
   197	    LTE (S (traceLength (survivingTrace deletionResult))) (traceLength trace)
   198	
   199	||| Executable/constructive selection boundary for the finite trace.
   200	public export
   201	data ClosingStepChoice :
   202	  (name : Type) -> (key : Type) -> (world : Type) -> (error : Type) ->
   203	  (value : key -> Type) ->
   204	  (protocol : RegistrationProtocol key value world error) ->
   205	  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
   206	  {initial, finalState : SystemState name key value world error} ->
   207	  (trace : Transitions initial finalState) ->
   208	  (premises : CanonicalizationPremises name key world error value protocol
   209	    nameEq keyEq trace) -> Type where
   210	  ClosingFree : NoClosingEpisodes name key world error value nameEq keyEq trace ->
   211	    ClosingStepChoice name key world error value protocol nameEq keyEq trace
   212	      premises
   213	  HasClosingStep :
   214	    (candidate : DeletableClosingEpisode name key world error value nameEq keyEq
   215	      trace) ->
   216	    DeletionChainStep name key world error value protocol nameEq keyEq trace
   217	      premises candidate ->
   218	    ClosingStepChoice name key world error value protocol nameEq keyEq trace
   219	      premises
   220	
   221	public export
   222	classifiedGeneration :
   223	  (entry : (generation : RegistrationGeneration name **
   224	    DeletedGenerationClassification name key world error value nameEq original
   225	      generation)) -> RegistrationGeneration name
   320	traceIndependentAfterDeletionReplaySpike =
   321	  ?traceIndependentAfterDeletionReplaySpike_rhs
   322	
   323	||| Finite maximal selection plus construction of the enriched internal step.
   324	public export
   325	0 chooseClosingStepSpike :
   326	  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
   327	  (protocol : RegistrationProtocol key value world error) ->
   328	  {initial, finalState : SystemState name key value world error} ->
   329	  (trace : Transitions initial finalState) ->
   330	  (premises : CanonicalizationPremises name key world error value protocol
   331	    nameEq keyEq trace) ->
   332	  ClosingStepChoice name key world error value protocol nameEq keyEq trace
   333	    premises
   334	chooseClosingStepSpike = ?chooseClosingStepSpike_rhs
   335	
   336	||| Well-founded recursion on `traceLength`, composing same-external-input,
   337	||| generated-registration, replay-independence, and exact endpoint metadata.
   338	public export
   339	0 deleteAllClosingEpisodesSpike :
   340	  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
   341	  (protocol : RegistrationProtocol key value world error) ->
   342	  {initial, finalState : SystemState name key value world error} ->
   343	  (trace : Transitions initial finalState) ->
   344	  CanonicalizationPremises name key world error value protocol nameEq keyEq trace ->
   345	  ClosingFreeReduction name key world error value protocol nameEq keyEq trace
   346	deleteAllClosingEpisodesSpike = ?deleteAllClosingEpisodesSpike_rhs
**Result:** exact declaration lines captured for final findings. **Classification: note.**

## Consolidated findings

1. **blocker — the occurrence-indexed bridge still permits wrong right-birth selection** (`research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr:125–172`). `ActionRegistrationReplayCorrespondence` correctly maps a replayed birth to an exact source-canonical occurrence and relates its replay ordinal. The bridge exposes that exact source occurrence. But the returned right occurrence is constrained only by renamed child, renamed parent, and component; there is no equation connecting its original generation to the source occurrence via `generatedGenerationBijection sameInputs`. Probe 24 reconstructs the bridge with any alternate same-action right occurrence while preserving the exact source origin, all endpoint fields, and the occurrence-relation index, then feeds it to the exact O21 hole. This matters precisely under same-raw-name/multiple-birth reuse: the right occurrence can be another birth. The bridge must state accepted left-original-generation → right-original-generation equality, not only action identity.

2. **major — a nontrivial `OperationalAdjacentBlockSwap` does not type-require any concrete adjacent swap node** (`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:437–463`; `research/DGamma/CP5ConfluenceCrossTraceSpike.idr:133–159`). Probe 19 constructs the record with `FiniteAdjacentSwapDone`, consuming no orientation and no `AdjacentSwapResult`, whenever the caller supplies a target-order decomposition of the unchanged trace. Such dual decompositions should be impossible for genuine unique blocks, but that impossibility/nonemptiness is not in the step interface. More generally the finite derivation is indexed only by source/target traces, not by the selected actor pair or the Cartesian crossing of `sourceBlocks`. Therefore the separately scoped O6 hole does not enforce the plan's advertised finite whole-block derivation.

3. **major — exact hole count, but O7/O9 are hidden inside another hole** (`research/DGamma/CP5ConfluenceDeletionChainSpike.idr:201–218,325–355`). The count is exactly 27, but `chooseClosingStepSpike` simultaneously hides the executable closing-episode scan/uniqueness work (O7), maximal candidate choice (O8), and complete enriched `DeletionChainStep` construction (O9). There is no separately stated O7 scanner producer or O9 one-step producer. This violates the requested reverse obligation reconciliation and prevents the advertised gates from being independently elaborated/re-estimated. O10/O11 are likewise combined in `deleteAllClosingEpisodesSpike`, though their output record is at least explicit.

4. **note/positive — sealing itself resists the round-5 attacks.** Public mapped support orders contain membership only. A pure polluted certificate cannot reach O20 (Probe 15), a legitimate sealed realization cannot be wrapped under a polluted outer certificate (Probe 16), safety cannot detach from the current trace/blocks/bundle (Probe 17), and the exact generated-child boundary is rejected before O20 (Probe 18). The remaining safe-selector existence problem is real, not illusory.

5. **note/positive — recursive occurrence and consumer coupling mostly work.** Generic two-step and recursive operational-fold correspondence probes pass (Probes 20 and 43); the bridge is indexed by the exact fold-produced relation and cannot be detached (Probe 44); wrong trace, stale quotient, and mixed schedule substitutions fail (Probes 32–35). The defect is specifically the missing accepted-generation equation for the chosen right occurrence, not loss of the source occurrence or fold index.

6. **note/positive — scanner fixtures withstand the requested attacks.** Both retained orderings expose full final-index and exact deleted-list equalities (Probe 28), the third order L6/R9/R14/L18 computes the same exact results (Probe 26), and wrong generation substitution fails on the ordinal (Probe 29). Scanner events retain constructor kind and exact generation.

7. **note/positive — four-fiber labeling is honest.** Plan and code explicitly disclaim reachable O19/O20 execution. One/moved/two-intermediate static mutations pass (Probes 39–40). No remaining end-to-end operational overclaim was found.

## Residual risks

- `selectOperationalCanonicalPermutationSpike` remains an unproved universal existence theorem. The retained withdrawn-intermediate models do not instantiate `IndependentCanonicalSchedule`; I could neither inhabit nor refute the sealed type for a concrete accepted two-schedule model without assuming O19/O20. This is honestly labeled an XL gate but remains the highest mathematical risk.
- The one-step producer still must establish every early-applicability, licensing, O/O freshness, and suffix replay premise at actual intermediate states. Strengthening its output as required below may expose another weak→strong failure.
- O21's accepted scanner inductions remain holes. The executable index fixture validates updates, not an actual full `RegistrationTraceCorrespondence` proof for those concrete events.
- All 27 research theorem bodies remain holes by design; elaboration does not establish theorem truth.
- The literal worktree includes pre-existing untracked `paper/` and this mandated report; tracked paths and the index are clean.

## Estimate assessment

The arithmetic is now correct: the eight raw bands sum exactly to **75–130**, with no overlap subtraction. Both re-estimation gates are concrete and appropriately placed. The range is directionally plausible for the currently named work, but it is **not an authorization estimate while the bridge and whole-block interfaces require revision**. Recompute the phase B/G rows after the corrected types elaborate; do not silently retain 75–130 if the accepted-generation bridge or block-crossing witness adds obligations.

## Exact changes required for round 7

1. **Couple bridge matches by accepted generation, not action alone.** Make `ReplayedCanonicalEndpointBridge` consume the left canonical schedule (or its `CanonicalRegistrationCorrespondence`) and require, for the exposed source/right occurrences, an equation of the form: the accepted `generatedGenerationBijection sameInputs` maps the source occurrence's exact original generation to the right occurrence's exact original generation. Add a duplicate same-child/same-parent/same-component alternate-birth negative; Probe 24 must fail.
2. **Index the whole-block derivation by the actor swap and located blocks.** A nontrivial `OperationalAdjacentBlockSwap` must carry a nonempty derivation proving the concrete Cartesian crossing of the selected left/right blocks. `FiniteAdjacentSwapDone` may terminate the recursive finite fold, but it must not inhabit a nontrivial actor-step output. The zero-node producer in Probe 19 must fail without relying on an unstated uniqueness contradiction.
3. **Split O7/O8/O9 producer boundaries.** State an executable closing/open occurrence scanner/uniqueness theorem, a separate maximal selector, and a separate enriched one-step D72 producer returning `DeletionChainStep`; make `chooseClosingStepSpike` a complete wrapper over them. Prefer similarly separating delete recursion (O10) from cumulative accounting (O11), or document and type a concrete intermediate gate.
4. **Retain the successful sealing/coupling negatives.** Re-run old pollution, outer pollution, current-state safety detachment, generated-child rejection, wrong trace, stale quotient, mixed schedule, and wrong occurrence-relation tests.
5. **Retain scanner and static tests.** Keep both branch fixtures, the third-order exact-list test, wrong-generation negative, honest static labels, and one/moved/two-intermediate variants.
6. **Reconcile holes in both directions and re-estimate.** Every table obligation must have its own independently testable producer or be explicitly marked as a complete wrapper/record-only obligation; report the new exact hole count and raw phase sum.
7. **Repeat release hygiene.** Preserve immutable CP3, empty production diff, research unreachability, 207/207 external build, and no staged/tracked changes.

## Final verdict

**REJECT.** Revision 6 genuinely closes the public pure-certificate pollution hole and substantially improves current-state safety, recursive occurrence threading, scanner fixtures, and documentation honesty. It is still not ready for proof shifts: the occurrence bridge can select the wrong same-action right birth without accepted-generation equality; the claimed concrete whole-block derivation can be zero-node and is not indexed by the chosen blocks; and O7/O9 remain hidden inside one deletion-selector hole.

**Final verdict: REJECT**

### Probe 52 — post-report final repository state
`git status --short --branch; git diff --cached --name-only; git diff --name-only; pgrep idris2`
## cp5-thm73-scoping...origin/cp5-thm73-scoping [ahead 33]
?? paper/
?? review-cp5-plan-round6.md
staged=none
tracked=none
active Idris=none
**Result:** no staged files, no tracked worktree changes, and no Idris process remains. **Classification: note/pass.**

**Final verdict: REJECT**
