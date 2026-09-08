module DGamma.CP5O20SupportedBridgeAssemblySpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5O20SupportedBirthBridgeSpike
import DGamma.CP5O20EpisodeSynchronizationSpike
import DGamma.CP5O20AllNameSynchronizationSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| A11 constructor boundary: the FOURTH scoped clause is now entirely
||| producer-owned by the accepted supported-birth theorem. Only the earlier
||| all-name cut invariant remains input; no opposite birth/matching oracle.
||| This does NOT extract arbitrary canonical paired execution or close O20.
export
0 o20SupportedBridgeFromOwnedCut :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal, replayedFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq left) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq right) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  GeneratedOrchestrationMatched name key world error value nameEq left right (generatedGenerationBijection sameInputs) ->
  (replayed : Transitions initial replayedFinal) ->
  (occurrences : ActionRegistrationReplayCorrespondence name key world error value
    (canonicalTrace (canonicalSchedule leftCapital)) replayed) ->
  O20AllNameCut name key world error value nameEq (expectedBridgeBijection sameInputs)
    replayedFinal (canonicalFinal (canonicalSchedule rightCapital)) ->
  ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
    left right sameInputs leftCapital replayed occurrences rightCapital
o20SupportedBridgeFromOwnedCut name key world error value nameEq keyEq protocol {replayedFinal}
  left right sameInputs leftCapital rightCapital leftUnique rightUnique matched replayed occurrences paired =
    MkReplayedCanonicalEndpointBridge
      (synchronizedAmbient (allNameEffects paired))
      (\selected, wanted => synchronizationLookupBindings key value keyEq wanted
        (effectTables (projectEffectState @{nameEq} replayedFinal) selected)
        (effectTables (projectEffectState @{nameEq} (canonicalFinal (canonicalSchedule rightCapital)))
          (renameForward (expectedBridgeBijection sameInputs) selected))
        (synchronizedTables (allNameEffects paired) selected))
      (allNameControls paired)
      (\birth, supported => supportedReplayedBirthBridge name key world error value nameEq keyEq protocol
        left right sameInputs leftCapital rightCapital leftUnique rightUnique matched replayed occurrences
        _ _ _ supported birth)
