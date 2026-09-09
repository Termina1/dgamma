module DGamma.CP5O20NativeInsertEnvironmentSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionGenerationScan
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5O20StampedHistoryFoldSpike
import DGamma.CP5O20StampedOrdinalNecessitySpike
import DGamma.CP5O20CanonicalOrdinalAttachmentSpike
import DGamma.CP5O20PhysicalInsertPositionSpike
import DGamma.CP5O20PhysicalInsertStageSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Every native scan's final ordinal is its starting ordinal plus the
||| physical trace count, including the original edges absent after filtering.
export
0 o20NativeScanCount :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  {ordinal, finalOrdinal : Nat} -> {live, finalLive : GenerationEnvironment name} ->
  GenerationTraceScan nameEq ordinal live trace finalOrdinal finalLive ->
  (finalOrdinal = ordinal + transitionCount trace)
o20NativeScanCount {ordinal} GenerationTraceScanEnd = sym (plusZeroRightNeutral ordinal)
o20NativeScanCount {ordinal} (GenerationTraceScanStep step rest later) =
  trans (o20NativeScanCount later) (plusSuccRightSucc ordinal (transitionCount rest))

||| Scan the actual finite preceding trace from the empty origin. The live
||| environment is COMPUTED, not a caller parameter; its ordinal is the same
||| physical count used by LocatedGeneratedRegistration.
export
0 o20NativePrefixScan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  GenerationTraceScan nameEq Z [] trace (transitionCount trace)
    (o20ScannedFinalLive nameEq Z [] trace)
o20NativePrefixScan {name} {key} {world} {error} {value} nameEq trace =
  replace {p = \live => GenerationTraceScan nameEq Z [] trace (transitionCount trace) live}
    (o20GenerationScanFinalLiveExact (generationScan (scanGenerations nameEq Z [] trace)))
    (replace {p = \ordinal => GenerationTraceScan nameEq Z [] trace ordinal
      (scanFinalLive (scanGenerations nameEq Z [] trace))}
      (o20NativeScanCount (generationScan (scanGenerations nameEq Z [] trace)))
      (generationScan (scanGenerations nameEq Z [] trace)))

||| A18-style physical attachment with NO live-environment parameters.
||| Both source tables are the deterministic scans of the attached births'
||| actual preceding traces. This record does NOT postulate an all-name cut.
public export
record O20PrefixScannedInsertAttachment
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {leftFirst, leftFinal, rightFirst, rightFinal, leftNowFirst, leftNowFinal, rightNowFirst, rightNowFinal : SystemState name key value world error}
  {left : Transitions leftFirst leftFinal} {right : Transitions rightFirst rightFinal}
  {leftNow : Transitions leftNowFirst leftNowFinal} {rightNow : Transitions rightNowFirst rightNowFinal}
  (leftReplay : ActionRegistrationReplayCorrespondence name key world error value left leftNow)
  (rightReplay : ActionRegistrationReplayCorrespondence name key world error value right rightNow)
  (mapping : RegistrationGenerationBijection name) (renaming : NameBijection name)
  (child, parent : name) (component : Component key value world error)
  (leftBirth : LocatedGeneratedRegistration child parent component leftNow) where
  constructor MkO20PrefixScannedInsertAttachment
  0 nativeInsertPositions : O20PhysicalInsertOriginPositions name key world error value leftReplay rightReplay mapping renaming
    child parent component leftBirth
  0 nativeLeftBirthScan : GenerationTraceScan nameEq Z [] (beforeRegistration leftBirth)
    (registrationOrdinal leftBirth) (o20ScannedFinalLive nameEq Z [] (beforeRegistration leftBirth))
  0 nativeRightBirthScan : GenerationTraceScan nameEq Z []
    (beforeRegistration (attachedRightBirth (physicalBirths nativeInsertPositions)))
    (registrationOrdinal (attachedRightBirth (physicalBirths nativeInsertPositions)))
    (o20ScannedFinalLive nameEq Z [] (beforeRegistration (attachedRightBirth (physicalBirths nativeInsertPositions))))
  0 nativeInsertStage : O20StampedStage name key world error value nameEq keyEq
    (o20ReplayOrdinalBijection (replayGenerationRenaming leftReplay) mapping (replayGenerationRenaming rightReplay)) renaming
    (registrationOrdinal leftBirth) (registrationOrdinal (attachedRightBirth (physicalBirths nativeInsertPositions)))
    (o20ScannedFinalLive nameEq Z [] (beforeRegistration leftBirth))
    (o20ScannedFinalLive nameEq Z [] (beforeRegistration (attachedRightBirth (physicalBirths nativeInsertPositions))))
    (putCurrentGeneration @{nameEq} child (registrationGeneration leftBirth)
      (o20ScannedFinalLive nameEq Z [] (beforeRegistration leftBirth)))
    (putCurrentGeneration @{nameEq} (renameForward renaming child)
      (registrationGeneration (attachedRightBirth (physicalBirths nativeInsertPositions)))
      (o20ScannedFinalLive nameEq Z [] (beforeRegistration (attachedRightBirth (physicalBirths nativeInsertPositions)))))
    (registrationBefore leftBirth) (registrationBefore (attachedRightBirth (physicalBirths nativeInsertPositions)))
    (registrationAfter leftBirth) (registrationAfter (attachedRightBirth (physicalBirths nativeInsertPositions)))

||| Construct both prefix-scanned environments, certificates and the stage
||| from the SAME attached physical births. No environment choice is exposed.
export
0 o20PrefixScannedInsertFromOrigins :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal, leftNowFirst, leftNowFinal, rightNowFirst, rightNowFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
  {leftNow : Transitions leftNowFirst leftNowFinal} -> {rightNow : Transitions rightNowFirst rightNowFinal} ->
  (leftReplay : ActionRegistrationReplayCorrespondence name key world error value left leftNow) ->
  (rightReplay : ActionRegistrationReplayCorrespondence name key world error value right rightNow) ->
  (mapping : RegistrationGenerationBijection name) -> (renaming : NameBijection name) ->
  AlignedTransitions name key world error value nameEq keyEq leftNow ->
  AlignedTransitions name key world error value nameEq keyEq rightNow ->
  (child, parent : name) -> (component : Component key value world error) ->
  (leftBirth : LocatedGeneratedRegistration child parent component leftNow) ->
  (positions : O20PhysicalInsertOriginPositions name key world error value leftReplay rightReplay mapping renaming
    child parent component leftBirth) ->
  O20PrefixScannedInsertAttachment name key world error value nameEq keyEq leftReplay rightReplay mapping renaming
    child parent component leftBirth
o20PrefixScannedInsertFromOrigins nameEq keyEq leftReplay rightReplay mapping renaming
  leftAligned rightAligned child parent component leftBirth positions =
    MkO20PrefixScannedInsertAttachment positions
      (o20NativePrefixScan nameEq (beforeRegistration leftBirth))
      (o20NativePrefixScan nameEq (beforeRegistration (attachedRightBirth (physicalBirths positions))))
      (o20AttachedGeneratedInsertStage nameEq keyEq leftReplay rightReplay mapping renaming
        leftAligned rightAligned child parent component leftBirth (physicalBirths positions))

||| Accepted A18 telescope with the arbitrary live-environment PARAMETERS
||| REMOVED. Both real source-cut environments and their scans are produced
||| at the attached births, using the unchanged conjugated physical map.
||| This does not yet produce the all-name predecessor relation.
export
0 o20PermutedCanonicalPrefixScannedInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace} ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace} ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  {operational : CertifiedOperationalCanonicalPermutation name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital matching} ->
  (execution : PermutedCanonicalExecution name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital operational) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  (0 generatedMatched : GeneratedOrchestrationMatched name key world error value nameEq
    leftTrace rightTrace (generatedGenerationBijection sameInputs)) ->
  (child, parent : name) -> (component : Component key value world error) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} child leftFinal = True) ->
  (birth : LocatedGeneratedRegistration child parent component (operationalTargetTrace operational)) ->
  O20PrefixScannedInsertAttachment name key world error value nameEq keyEq
    (composeActionRegistrationReplayCorrespondence (canonicalOccurrenceCorrespondence leftCapital)
      (permutationOccurrenceCorrespondence execution))
    (canonicalOccurrenceCorrespondence rightCapital) (generatedGenerationBijection sameInputs)
    (expectedBridgeBijection sameInputs) child parent component birth
o20PermutedCanonicalPrefixScannedInsert {name} {key} {world} {error} {value} {protocol} {nameEq} {keyEq}
  {initial} {leftFinal} {rightFinal} {leftTrace} {rightTrace} {sameInputs} {leftCapital} {rightCapital} {matching} {operational}
  execution leftUnique rightUnique generatedMatched child parent component supported birth =
    o20PrefixScannedInsertFromOrigins nameEq keyEq
      (composeActionRegistrationReplayCorrespondence (canonicalOccurrenceCorrespondence leftCapital)
        (permutationOccurrenceCorrespondence execution))
      (canonicalOccurrenceCorrespondence rightCapital) (generatedGenerationBijection sameInputs)
      (expectedBridgeBijection sameInputs)
      (replayAligned (operationalTargetPremises operational)) (replayAligned (canonicalReplayPremises rightCapital))
      child parent component birth
      (o20PermutedCanonicalInsertOrigins {name} {key} {world} {error} {value} {protocol} {nameEq} {keyEq}
        {initial} {leftFinal} {rightFinal} {leftTrace} {rightTrace} {sameInputs} {leftCapital} {rightCapital} {matching} {operational}
        execution leftUnique rightUnique generatedMatched child parent component supported birth)

||| Conditional ALL-NAME successor at the native scanned coordinates. Only
||| the actual predecessor cut is a premise; the stage derives its successor.
||| The accepted-input predecessor producer remains OPEN, not assumed closed.
export
0 o20PrefixScannedInsertCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal, leftNowFirst, leftNowFinal, rightNowFirst, rightNowFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
  {leftNow : Transitions leftNowFirst leftNowFinal} -> {rightNow : Transitions rightNowFirst rightNowFinal} ->
  (leftReplay : ActionRegistrationReplayCorrespondence name key world error value left leftNow) ->
  (rightReplay : ActionRegistrationReplayCorrespondence name key world error value right rightNow) ->
  (mapping : RegistrationGenerationBijection name) -> (renaming : NameBijection name) ->
  (child, parent : name) -> (component : Component key value world error) ->
  (leftBirth : LocatedGeneratedRegistration child parent component leftNow) ->
  (attached : O20PrefixScannedInsertAttachment name key world error value nameEq keyEq leftReplay rightReplay mapping renaming
    child parent component leftBirth) ->
  O20StampedCut name key world error value nameEq
    (o20ReplayOrdinalBijection (replayGenerationRenaming leftReplay) mapping (replayGenerationRenaming rightReplay)) renaming
    (o20ScannedFinalLive nameEq Z [] (beforeRegistration leftBirth))
    (o20ScannedFinalLive nameEq Z [] (beforeRegistration (attachedRightBirth (physicalBirths (nativeInsertPositions attached)))))
    (registrationBefore leftBirth) (registrationBefore (attachedRightBirth (physicalBirths (nativeInsertPositions attached)))) ->
  O20StampedCut name key world error value nameEq
    (o20ReplayOrdinalBijection (replayGenerationRenaming leftReplay) mapping (replayGenerationRenaming rightReplay)) renaming
    (putCurrentGeneration @{nameEq} child (registrationGeneration leftBirth) (o20ScannedFinalLive nameEq Z [] (beforeRegistration leftBirth)))
    (putCurrentGeneration @{nameEq} (renameForward renaming child) (registrationGeneration (attachedRightBirth (physicalBirths (nativeInsertPositions attached)))) (o20ScannedFinalLive nameEq Z [] (beforeRegistration (attachedRightBirth (physicalBirths (nativeInsertPositions attached))))))
    (registrationAfter leftBirth) (registrationAfter (attachedRightBirth (physicalBirths (nativeInsertPositions attached))))
o20PrefixScannedInsertCut nameEq keyEq leftReplay rightReplay mapping renaming child parent component leftBirth attached predecessor =
  o20StampedStageCut (nativeInsertStage attached) predecessor
