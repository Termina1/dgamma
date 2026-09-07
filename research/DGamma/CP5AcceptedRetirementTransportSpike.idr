module DGamma.CP5AcceptedRetirementTransportSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5GeneratedRetirementTransportSpike
import DGamma.CP5RootOrchestrationTransportSpike
import DGamma.CP5RetirementHistorySpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| Root and generated cases both use ACTUAL retirement source authentication.
||| The accepted live-root law fixes root names; A9 correlates generated stamps.
0 acceptedRetirementBackwardByParent :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  GeneratedOrchestrationMatched name key world error value nameEq left right (generatedGenerationBijection sameInputs) ->
  AlignedTransitions name key world error value nameEq keyEq right -> (bindings (registry initial) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (selected : name) -> (leftGeneration, rightGeneration : RegistrationGeneration name) ->
  CurrentGenerationBirth name key world error value left selected leftGeneration ->
  CurrentGenerationBirth name key world error value right (renameForward (currentNameBijection (endpointRenaming sameInputs)) selected) rightGeneration ->
  (generationForward (generatedGenerationBijection sameInputs) leftGeneration = rightGeneration) ->
  (rightFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq}
    (renameForward (currentNameBijection (endpointRenaming sameInputs)) selected) (registry rightFinal) = Just rightFiber) ->
  LocatedActionOccurrence (ORetire (renameForward (currentNameBijection (endpointRenaming sameInputs)) selected)) right ->
  (observedParent : Parent name) -> (fiberParent rightFiber = observedParent) -> LocatedActionOccurrence (ORetire selected) left
acceptedRetirementBackwardByParent name key world error value nameEq keyEq left right sameInputs matched aligned empty unique selected
  leftGeneration rightGeneration leftBirth rightBirth generationMapped rightFiber rightFound occurrence Root parentExact =
    replace {p = \action => LocatedActionOccurrence action left}
      (cong ORetire (trans (sym (rightLiveRootFixed (endpointRenaming sameInputs)
        (renameForward (currentNameBijection (endpointRenaming sameInputs)) selected) rightFiber rightFound parentExact))
        (renameLeftInverse (currentNameBijection (endpointRenaming sameInputs)) selected)))
      (rootActionLocated name key world error value nameEq left (ORetire (renameForward (currentNameBijection (endpointRenaming sameInputs)) selected))
        (rootActionBackward name key world error value nameEq left right (sameExternalInputs sameInputs)
          (ORetire (renameForward (currentNameBijection (endpointRenaming sameInputs)) selected))
          (rootEndpointRetirementPacket name key world error value nameEq keyEq right aligned empty unique
            (renameForward (currentNameBijection (endpointRenaming sameInputs)) selected) rightFiber rightFound parentExact occurrence)))
acceptedRetirementBackwardByParent name key world error value nameEq keyEq left right sameInputs matched aligned empty unique selected
  leftGeneration rightGeneration leftBirth rightBirth generationMapped rightFiber rightFound occurrence (ChildOf parent) parentExact =
    case generatedEndpointRetirementPacket name key world error value nameEq keyEq right aligned empty unique
      (renameForward (currentNameBijection (endpointRenaming sameInputs)) selected) parent rightFiber rightFound parentExact occurrence of
      (packet ** (actorExact, kind)) => generatedRetirementBackwardAtBirths name key world error value nameEq keyEq left right
        (generatedGenerationBijection sameInputs) matched unique selected (renameForward (currentNameBijection (endpointRenaming sameInputs)) selected)
        leftGeneration rightGeneration leftBirth rightBirth generationMapped packet actorExact kind

0 acceptedRetirementForwardByParent :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  GeneratedOrchestrationMatched name key world error value nameEq left right (generatedGenerationBijection sameInputs) ->
  AlignedTransitions name key world error value nameEq keyEq left -> (bindings (registry initial) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  (selected : name) -> (leftGeneration, rightGeneration : RegistrationGeneration name) ->
  CurrentGenerationBirth name key world error value left (renameBackward (currentNameBijection (endpointRenaming sameInputs)) selected) leftGeneration ->
  CurrentGenerationBirth name key world error value right selected rightGeneration ->
  (generationBackward (generatedGenerationBijection sameInputs) rightGeneration = leftGeneration) ->
  (leftFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq}
    (renameBackward (currentNameBijection (endpointRenaming sameInputs)) selected) (registry leftFinal) = Just leftFiber) ->
  LocatedActionOccurrence (ORetire (renameBackward (currentNameBijection (endpointRenaming sameInputs)) selected)) left ->
  (observedParent : Parent name) -> (fiberParent leftFiber = observedParent) -> LocatedActionOccurrence (ORetire selected) right
acceptedRetirementForwardByParent name key world error value nameEq keyEq left right sameInputs matched aligned empty unique selected
  leftGeneration rightGeneration leftBirth rightBirth generationMapped leftFiber leftFound occurrence Root parentExact =
    replace {p = \action => LocatedActionOccurrence action right}
      (cong ORetire (trans (sym (leftLiveRootFixed (endpointRenaming sameInputs)
        (renameBackward (currentNameBijection (endpointRenaming sameInputs)) selected) leftFiber leftFound parentExact))
        (renameRightInverse (currentNameBijection (endpointRenaming sameInputs)) selected)))
      (rootActionLocated name key world error value nameEq right (ORetire (renameBackward (currentNameBijection (endpointRenaming sameInputs)) selected))
        (rootActionForward name key world error value nameEq left right (sameExternalInputs sameInputs)
          (ORetire (renameBackward (currentNameBijection (endpointRenaming sameInputs)) selected))
          (rootEndpointRetirementPacket name key world error value nameEq keyEq left aligned empty unique
            (renameBackward (currentNameBijection (endpointRenaming sameInputs)) selected) leftFiber leftFound parentExact occurrence)))
acceptedRetirementForwardByParent name key world error value nameEq keyEq left right sameInputs matched aligned empty unique selected
  leftGeneration rightGeneration leftBirth rightBirth generationMapped leftFiber leftFound occurrence (ChildOf parent) parentExact =
    case generatedEndpointRetirementPacket name key world error value nameEq keyEq left aligned empty unique
      (renameBackward (currentNameBijection (endpointRenaming sameInputs)) selected) parent leftFiber leftFound parentExact occurrence of
      (packet ** (actorExact, kind)) => generatedRetirementForwardAtBirths name key world error value nameEq keyEq left right
        (generatedGenerationBijection sameInputs) matched unique (renameBackward (currentNameBijection (endpointRenaming sameInputs)) selected) selected
        leftGeneration rightGeneration leftBirth rightBirth generationMapped packet actorExact kind

export
0 acceptedSupportedForwardRejectsTargetRetired :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  GeneratedOrchestrationMatched name key world error value nameEq left right (generatedGenerationBijection sameInputs) ->
  AlignedTransitions name key world error value nameEq keyEq left -> AlignedTransitions name key world error value nameEq keyEq right ->
  (bindings (registry initial) = []) -> UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right -> (selected : name) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected leftFinal = True) ->
  (rightFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq}
    (renameForward (currentNameBijection (endpointRenaming sameInputs)) selected) (registry rightFinal) = Just rightFiber) ->
  (retired rightFiber = True) -> Void
acceptedSupportedForwardRejectsTargetRetired name key world error value nameEq keyEq {leftFinal} left right sameInputs matched
  leftAligned rightAligned empty leftUnique rightUnique selected supported rightFiber rightFound rightRetired =
    case computedSupportPresent name key world error value nameEq keyEq leftFinal selected supported of
      (leftFiber ** leftFound) => case acceptedSupportedForwardDomain name key world error value nameEq keyEq left right sameInputs leftAligned rightAligned empty selected supported of
        (leftGeneration ** rightGeneration ** _ ** (leftCurrent, rightCurrent, generationMapped, _)) =>
          nonretiredEndpointRejectsRetirement name key world error value nameEq keyEq left leftAligned empty leftUnique selected leftFiber leftFound
            (computedSupportNotRetired name key world error value nameEq keyEq leftFinal selected leftFiber leftFound supported)
            (acceptedRetirementBackwardByParent name key world error value nameEq keyEq left right sameInputs matched rightAligned empty rightUnique selected
              leftGeneration rightGeneration
              (acceptedLeftCurrentBirth name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs)
                selected leftGeneration leftCurrent)
              (acceptedRightCurrentBirth name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs)
                (renameForward (currentNameBijection (endpointRenaming sameInputs)) selected) rightGeneration rightCurrent)
              generationMapped rightFiber rightFound
              (retiredEndpointHasRetirement name key world error value nameEq keyEq right rightAligned empty
                (renameForward (currentNameBijection (endpointRenaming sameInputs)) selected) rightFiber rightFound rightRetired) (fiberParent rightFiber) Refl)

export
0 acceptedSupportedBackwardRejectsTargetRetired :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  GeneratedOrchestrationMatched name key world error value nameEq left right (generatedGenerationBijection sameInputs) ->
  AlignedTransitions name key world error value nameEq keyEq left -> AlignedTransitions name key world error value nameEq keyEq right ->
  (bindings (registry initial) = []) -> UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right -> (selected : name) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected rightFinal = True) ->
  (leftFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq}
    (renameBackward (currentNameBijection (endpointRenaming sameInputs)) selected) (registry leftFinal) = Just leftFiber) ->
  (retired leftFiber = True) -> Void
acceptedSupportedBackwardRejectsTargetRetired name key world error value nameEq keyEq {rightFinal} left right sameInputs matched
  leftAligned rightAligned empty leftUnique rightUnique selected supported leftFiber leftFound leftRetired =
    case computedSupportPresent name key world error value nameEq keyEq rightFinal selected supported of
      (rightFiber ** rightFound) => case acceptedSupportedBackwardDomain name key world error value nameEq keyEq left right sameInputs leftAligned rightAligned empty selected supported of
        (rightGeneration ** leftGeneration ** _ ** (rightCurrent, leftCurrent, generationMapped, _)) =>
          nonretiredEndpointRejectsRetirement name key world error value nameEq keyEq right rightAligned empty rightUnique selected rightFiber rightFound
            (computedSupportNotRetired name key world error value nameEq keyEq rightFinal selected rightFiber rightFound supported)
            (acceptedRetirementForwardByParent name key world error value nameEq keyEq left right sameInputs matched leftAligned empty leftUnique selected
              leftGeneration rightGeneration
              (acceptedLeftCurrentBirth name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs)
                (renameBackward (currentNameBijection (endpointRenaming sameInputs)) selected) leftGeneration leftCurrent)
              (acceptedRightCurrentBirth name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs)
                selected rightGeneration rightCurrent)
              generationMapped leftFiber leftFound
              (retiredEndpointHasRetirement name key world error value nameEq keyEq left leftAligned empty
                (renameBackward (currentNameBijection (endpointRenaming sameInputs)) selected) leftFiber leftFound leftRetired) (fiberParent leftFiber) Refl)
