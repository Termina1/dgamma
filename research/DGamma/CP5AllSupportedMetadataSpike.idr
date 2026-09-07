module DGamma.CP5AllSupportedMetadataSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5MatchedBirthMetadataSpike
import DGamma.CP5RootBirthCoverageSpike
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

public export
supportMapParent : (name : Type) -> (name -> name) -> Parent name -> Parent name
supportMapParent name renaming Root = Root
supportMapParent name renaming (ChildOf parent) = ChildOf (renaming parent)

0 allSupportedMetadataForwardByParent :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  AlignedTransitions name key world error value nameEq keyEq left -> AlignedTransitions name key world error value nameEq keyEq right ->
  RegistrationDiscipline protocol nameEq left -> (bindings (registry initial) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left -> UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (selected : name) -> (sourceFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} selected (registry leftFinal) = Just sourceFiber) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected leftFinal = True) ->
  (observedParent : Parent name) -> (fiberParent sourceFiber = observedParent) ->
  (targetFiber : Fiber name key value world error **
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq}
      (renameForward (currentNameBijection (endpointRenaming sameInputs)) selected) (registry rightFinal) = Just targetFiber,
     fiberComponent targetFiber = fiberComponent sourceFiber,
     fiberParent targetFiber = supportMapParent name (renameForward (currentNameBijection (endpointRenaming sameInputs))) (fiberParent sourceFiber)))
allSupportedMetadataForwardByParent name key world error value nameEq keyEq protocol left right sameInputs leftAligned rightAligned discipline empty leftUnique rightUnique
  selected sourceFiber sourceFound supported Root parentExact =
    case acceptedSupportedRootMetadataForward name key world error value nameEq keyEq left right sameInputs leftAligned rightAligned empty rightUnique
      selected sourceFiber sourceFound parentExact supported of
      (targetFiber ** (targetFound, metadata)) => (targetFiber ** (targetFound, cong snd metadata,
        trans (cong fst metadata) (cong (supportMapParent name (renameForward (currentNameBijection (endpointRenaming sameInputs)))) (sym parentExact))))
allSupportedMetadataForwardByParent name key world error value nameEq keyEq protocol {leftFinal} {rightFinal} left right sameInputs leftAligned rightAligned discipline empty leftUnique rightUnique
  selected sourceFiber sourceFound supported (ChildOf parent) parentExact =
    case acceptedSupportedGeneratedLeftCoverage name key world error value nameEq keyEq protocol left right
      (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs) leftAligned discipline empty leftUnique selected sourceFiber sourceFound parent parentExact supported of
      (event ** (member, actorExact)) => case acceptedSupportedGeneratedCoherenceForward name key world error value nameEq keyEq left right sameInputs
        leftAligned rightAligned empty leftUnique rightUnique event member sourceFiber
        (replace {p = \actor => (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} actor (registry leftFinal) = Just sourceFiber)} (sym actorExact) sourceFound)
        (replace {p = \actor => (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} actor leftFinal = True)} (sym actorExact) supported) of
        (targetEvent ** targetFiber ** metadata ** (_, _, targetFound, _, _, parentName)) =>
          (targetFiber **
            (replace {p = \actor => (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq}
              (renameForward (currentNameBijection (endpointRenaming sameInputs)) actor) (registry rightFinal) = Just targetFiber)} actorExact targetFound,
             sym (endpointComponentsMatch metadata),
             trans (rightEndpointBirthParent metadata) (trans (cong ChildOf (sym parentName))
               (cong (supportMapParent name (renameForward (currentNameBijection (endpointRenaming sameInputs)))) (sym (leftEndpointBirthParent metadata))))))

||| Every supported original name, not merely a supplied retained event.
export
0 acceptedAllSupportedMetadataForward :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  AlignedTransitions name key world error value nameEq keyEq left -> AlignedTransitions name key world error value nameEq keyEq right ->
  RegistrationDiscipline protocol nameEq left -> (bindings (registry initial) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left -> UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (selected : name) -> (sourceFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} selected (registry leftFinal) = Just sourceFiber) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected leftFinal = True) ->
  (targetFiber : Fiber name key value world error **
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq}
      (renameForward (currentNameBijection (endpointRenaming sameInputs)) selected) (registry rightFinal) = Just targetFiber,
     fiberComponent targetFiber = fiberComponent sourceFiber,
     fiberParent targetFiber = supportMapParent name (renameForward (currentNameBijection (endpointRenaming sameInputs))) (fiberParent sourceFiber)))
acceptedAllSupportedMetadataForward name key world error value nameEq keyEq protocol left right sameInputs leftAligned rightAligned discipline empty leftUnique rightUnique
  selected sourceFiber sourceFound supported =
    allSupportedMetadataForwardByParent name key world error value nameEq keyEq protocol left right sameInputs leftAligned rightAligned discipline empty leftUnique rightUnique
      selected sourceFiber sourceFound supported (fiberParent sourceFiber) Refl

0 allSupportedMetadataBackwardByParent :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  AlignedTransitions name key world error value nameEq keyEq left -> AlignedTransitions name key world error value nameEq keyEq right ->
  RegistrationDiscipline protocol nameEq right -> (bindings (registry initial) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left -> UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (selected : name) -> (sourceFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} selected (registry rightFinal) = Just sourceFiber) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected rightFinal = True) ->
  (observedParent : Parent name) -> (fiberParent sourceFiber = observedParent) ->
  (targetFiber : Fiber name key value world error **
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq}
      (renameBackward (currentNameBijection (endpointRenaming sameInputs)) selected) (registry leftFinal) = Just targetFiber,
     fiberComponent targetFiber = fiberComponent sourceFiber,
     fiberParent targetFiber = supportMapParent name (renameBackward (currentNameBijection (endpointRenaming sameInputs))) (fiberParent sourceFiber)))
allSupportedMetadataBackwardByParent name key world error value nameEq keyEq protocol left right sameInputs leftAligned rightAligned discipline empty leftUnique rightUnique
  selected sourceFiber sourceFound supported Root parentExact =
    case acceptedSupportedRootMetadataBackward name key world error value nameEq keyEq left right sameInputs leftAligned rightAligned empty leftUnique
      selected sourceFiber sourceFound parentExact supported of
      (targetFiber ** (targetFound, metadata)) => (targetFiber ** (targetFound, cong snd metadata,
        trans (cong fst metadata) (cong (supportMapParent name (renameBackward (currentNameBijection (endpointRenaming sameInputs)))) (sym parentExact))))
allSupportedMetadataBackwardByParent name key world error value nameEq keyEq protocol {leftFinal} {rightFinal} left right sameInputs leftAligned rightAligned discipline empty leftUnique rightUnique
  selected sourceFiber sourceFound supported (ChildOf parent) parentExact =
    case acceptedSupportedGeneratedRightCoverage name key world error value nameEq keyEq protocol left right
      (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs) rightAligned discipline empty rightUnique selected sourceFiber sourceFound parent parentExact supported of
      (event ** (member, actorExact)) => case acceptedSupportedGeneratedCoherenceBackward name key world error value nameEq keyEq left right sameInputs
        leftAligned rightAligned empty leftUnique rightUnique event member sourceFiber
        (replace {p = \actor => (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} actor (registry rightFinal) = Just sourceFiber)} (sym actorExact) sourceFound)
        (replace {p = \actor => (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} actor rightFinal = True)} (sym actorExact) supported) of
        (targetEvent ** targetFiber ** metadata ** (_, _, targetFound, _, _, parentName)) =>
          (targetFiber **
            (replace {p = \actor => (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq}
              (renameBackward (currentNameBijection (endpointRenaming sameInputs)) actor) (registry leftFinal) = Just targetFiber)} actorExact targetFound,
             endpointComponentsMatch metadata,
             trans (leftEndpointBirthParent metadata) (trans (cong ChildOf (sym parentName))
               (cong (supportMapParent name (renameBackward (currentNameBijection (endpointRenaming sameInputs)))) (sym (rightEndpointBirthParent metadata))))))
