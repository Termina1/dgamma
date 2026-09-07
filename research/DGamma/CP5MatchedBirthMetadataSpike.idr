module DGamma.CP5MatchedBirthMetadataSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Decidable.Equality
import Data.List.Elem

%default total
%unbound_implicits off

||| The accepted left scanner authenticates the endpoint's EXACT static fields.
export
0 acceptedLeftEndpointMetadataBirth :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (renaming : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq renaming left right) ->
  AlignedTransitions name key world error value nameEq keyEq left ->
  (bindings (registry leftFirst) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} selected (leftFinalGenerations registrations) = Just generation) ->
  (observed : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry leftFinal) = Just observed) ->
  (birth : LocatedActionOccurrence (OInsert selected (fiberParent observed) (fiberComponent observed)) left **
    generation = MkRegistrationGeneration selected (locatedActionOrdinal birth))
acceptedLeftEndpointMetadataBirth name key world error value nameEq keyEq left right renaming registrations aligned empty unique selected generation current observed found =
  currentBirthAtPrefixMetadata name key world error value nameEq keyEq left left NoTransitions
    (currentBirthTraceAppendEmpty name key world error value left) aligned empty unique selected generation
    (acceptedLeftCurrentBirth name key world error value nameEq left right renaming registrations selected generation current) observed found


||| The symmetric accepted right scanner authenticates exact static fields.
export
0 acceptedRightEndpointMetadataBirth :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (renaming : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq renaming left right) ->
  AlignedTransitions name key world error value nameEq keyEq right ->
  (bindings (registry rightFirst) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} selected (rightFinalGenerations registrations) = Just generation) ->
  (observed : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry rightFinal) = Just observed) ->
  (birth : LocatedActionOccurrence (OInsert selected (fiberParent observed) (fiberComponent observed)) right **
    generation = MkRegistrationGeneration selected (locatedActionOrdinal birth))
acceptedRightEndpointMetadataBirth name key world error value nameEq keyEq left right renaming registrations aligned empty unique selected generation current observed found =
  currentBirthAtPrefixMetadata name key world error value nameEq keyEq right right NoTransitions
    (currentBirthTraceAppendEmpty name key world error value right) aligned empty unique selected generation
    (acceptedRightCurrentBirth name key world error value nameEq left right renaming registrations selected generation current) observed found


||| Forward actual endpoint metadata under an AUTHENTICATED matching member.
||| The opposite fiber comes from accepted current-domain transport, not a caller.
||| No opposite support truth or retired equality is asserted.
export
0 supportedMatchingMetadataForward :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  AlignedTransitions name key world error value nameEq keyEq left ->
  AlignedTransitions name key world error value nameEq keyEq right ->
  bindings (registry initial) = [] ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (matching : AuthenticatedRegistrationMatching name key world error value (generatedGenerationBijection sameInputs) left right) ->
  (leftEvent : RegistrationEvent name key world error value) -> Elem leftEvent (leftScannedEvents matching) ->
  (leftFiber : Fiber name key value world error) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} (eventChild leftEvent) (registry leftFinal) = Just leftFiber ->
  isSupported {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} @{keyEq} (eventChild leftEvent) leftFinal = True ->
  (rightEvent : RegistrationEvent name key world error value ** rightFiber : Fiber name key value world error **
    (Elem rightEvent (rightScannedEvents matching),
     eventChild rightEvent = (renameForward (currentNameBijection (endpointRenaming sameInputs)) (eventChild leftEvent)),
     lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
       @{nameEq} (renameForward (currentNameBijection (endpointRenaming sameInputs)) (eventChild leftEvent)) (registry rightFinal) = Just rightFiber,
     MatchedEndpointStaticMetadata name key world error value (generatedGenerationBijection sameInputs) leftEvent rightEvent leftFiber rightFiber))
supportedMatchingMetadataForward name key world error value nameEq keyEq left right sameInputs
  leftAligned rightAligned empty leftUnique rightUnique matching leftEvent leftMember leftFiber leftFound supported =
    case acceptedSupportedForwardDomain name key world error value nameEq keyEq left right sameInputs
      leftAligned rightAligned empty (eventChild leftEvent) supported of
      (leftGeneration ** rightGeneration ** rightFiber ** (leftCurrent, rightCurrent, mapped, rightFound)) =>
        case matchedEventForward matching leftEvent leftMember of
          (rightEvent ** (rightMember, matched)) =>
            (rightEvent ** rightFiber ** (rightMember,
              (matchedScannedCurrentName name key world error value right (generatedGenerationBijection sameInputs) leftEvent rightEvent matched
                    (rightScannedBirths matching rightEvent rightMember) leftGeneration rightGeneration
                    (currentBirthMatchesScannedEvent name key world error value nameEq keyEq left leftUnique leftEvent
                      (leftScannedBirths matching leftEvent leftMember) leftGeneration (acceptedLeftCurrentBirth name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs) (eventChild leftEvent) leftGeneration leftCurrent))
                    mapped (renameForward (currentNameBijection (endpointRenaming sameInputs)) (eventChild leftEvent)) (acceptedRightCurrentBirth name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs) (renameForward (currentNameBijection (endpointRenaming sameInputs)) (eventChild leftEvent)) rightGeneration rightCurrent)),
              rightFound,
              matchedBirthEndpointMetadataRenamed name key world error value nameEq keyEq left right
                leftAligned rightAligned empty empty leftUnique rightUnique (generatedGenerationBijection sameInputs) leftEvent rightEvent
                (leftScannedBirths matching leftEvent leftMember) (rightScannedBirths matching rightEvent rightMember)
                matched leftFiber rightFiber (eventChild leftEvent) (renameForward (currentNameBijection (endpointRenaming sameInputs)) (eventChild leftEvent)) Refl
                (matchedScannedCurrentName name key world error value right (generatedGenerationBijection sameInputs) leftEvent rightEvent matched
                    (rightScannedBirths matching rightEvent rightMember) leftGeneration rightGeneration
                    (currentBirthMatchesScannedEvent name key world error value nameEq keyEq left leftUnique leftEvent
                      (leftScannedBirths matching leftEvent leftMember) leftGeneration (acceptedLeftCurrentBirth name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs) (eventChild leftEvent) leftGeneration leftCurrent))
                    mapped (renameForward (currentNameBijection (endpointRenaming sameInputs)) (eventChild leftEvent)) (acceptedRightCurrentBirth name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs) (renameForward (currentNameBijection (endpointRenaming sameInputs)) (eventChild leftEvent)) rightGeneration rightCurrent))
                leftFound rightFound))

||| Symmetric actual endpoint metadata; backward domain transport does not
||| silently assert the opposite endpoint is supported.
export
0 supportedMatchingMetadataBackward :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  AlignedTransitions name key world error value nameEq keyEq left ->
  AlignedTransitions name key world error value nameEq keyEq right ->
  bindings (registry initial) = [] ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (matching : AuthenticatedRegistrationMatching name key world error value (generatedGenerationBijection sameInputs) left right) ->
  (rightEvent : RegistrationEvent name key world error value) -> Elem rightEvent (rightScannedEvents matching) ->
  (rightFiber : Fiber name key value world error) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} (eventChild rightEvent) (registry rightFinal) = Just rightFiber ->
  isSupported {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} @{keyEq} (eventChild rightEvent) rightFinal = True ->
  (leftEvent : RegistrationEvent name key world error value ** leftFiber : Fiber name key value world error **
    (Elem leftEvent (leftScannedEvents matching),
     eventChild leftEvent = (renameBackward (currentNameBijection (endpointRenaming sameInputs)) (eventChild rightEvent)),
     lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
       @{nameEq} (renameBackward (currentNameBijection (endpointRenaming sameInputs)) (eventChild rightEvent)) (registry leftFinal) = Just leftFiber,
     MatchedEndpointStaticMetadata name key world error value (generatedGenerationBijection sameInputs) leftEvent rightEvent leftFiber rightFiber))
supportedMatchingMetadataBackward name key world error value nameEq keyEq left right sameInputs
  leftAligned rightAligned empty leftUnique rightUnique matching rightEvent rightMember rightFiber rightFound supported =
    case acceptedSupportedBackwardDomain name key world error value nameEq keyEq left right sameInputs
      leftAligned rightAligned empty (eventChild rightEvent) supported of
      (rightGeneration ** leftGeneration ** leftFiber ** (rightCurrent, leftCurrent, mapped, leftFound)) =>
        case matchedEventBackward matching rightEvent rightMember of
          (leftEvent ** (leftMember, matched)) =>
            (leftEvent ** leftFiber ** (leftMember,
              (matchedScannedCurrentNameBackward name key world error value left (generatedGenerationBijection sameInputs) leftEvent rightEvent matched
                    (leftScannedBirths matching leftEvent leftMember) leftGeneration rightGeneration
                    (currentBirthMatchesScannedEvent name key world error value nameEq keyEq right rightUnique rightEvent
                      (rightScannedBirths matching rightEvent rightMember) rightGeneration (acceptedRightCurrentBirth name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs) (eventChild rightEvent) rightGeneration rightCurrent))
                    mapped (renameBackward (currentNameBijection (endpointRenaming sameInputs)) (eventChild rightEvent)) (acceptedLeftCurrentBirth name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs) (renameBackward (currentNameBijection (endpointRenaming sameInputs)) (eventChild rightEvent)) leftGeneration leftCurrent)),
              leftFound,
              matchedBirthEndpointMetadataRenamed name key world error value nameEq keyEq left right
                leftAligned rightAligned empty empty leftUnique rightUnique (generatedGenerationBijection sameInputs) leftEvent rightEvent
                (leftScannedBirths matching leftEvent leftMember) (rightScannedBirths matching rightEvent rightMember)
                matched leftFiber rightFiber (renameBackward (currentNameBijection (endpointRenaming sameInputs)) (eventChild rightEvent)) (eventChild rightEvent)
                (matchedScannedCurrentNameBackward name key world error value left (generatedGenerationBijection sameInputs) leftEvent rightEvent matched
                    (leftScannedBirths matching leftEvent leftMember) leftGeneration rightGeneration
                    (currentBirthMatchesScannedEvent name key world error value nameEq keyEq right rightUnique rightEvent
                      (rightScannedBirths matching rightEvent rightMember) rightGeneration (acceptedRightCurrentBirth name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs) (eventChild rightEvent) rightGeneration rightCurrent))
                    mapped (renameBackward (currentNameBijection (endpointRenaming sameInputs)) (eventChild rightEvent)) (acceptedLeftCurrentBirth name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs) (renameBackward (currentNameBijection (endpointRenaming sameInputs)) (eventChild rightEvent)) leftGeneration leftCurrent))
                Refl leftFound rightFound))

||| Fully sealed forward boundary: matching and births come from sameInputs itself.
||| The explicit remaining coverage premise is membership of this retained event.
export
0 acceptedSupportedGeneratedMetadataForward :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  AlignedTransitions name key world error value nameEq keyEq left ->
  AlignedTransitions name key world error value nameEq keyEq right ->
  bindings (registry initial) = [] ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (leftEvent : RegistrationEvent name key world error value) -> Elem leftEvent (leftScannedEvents (acceptedAuthenticatedRegistrationMatching name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs))) ->
  (leftFiber : Fiber name key value world error) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} (eventChild leftEvent) (registry leftFinal) = Just leftFiber ->
  isSupported {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} @{keyEq} (eventChild leftEvent) leftFinal = True ->
  (rightEvent : RegistrationEvent name key world error value ** rightFiber : Fiber name key value world error **
    (Elem rightEvent (rightScannedEvents (acceptedAuthenticatedRegistrationMatching name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs))),
     eventChild rightEvent = (renameForward (currentNameBijection (endpointRenaming sameInputs)) (eventChild leftEvent)),
     lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
       @{nameEq} (renameForward (currentNameBijection (endpointRenaming sameInputs)) (eventChild leftEvent)) (registry rightFinal) = Just rightFiber,
     MatchedEndpointStaticMetadata name key world error value (generatedGenerationBijection sameInputs) leftEvent rightEvent leftFiber rightFiber))
acceptedSupportedGeneratedMetadataForward name key world error value nameEq keyEq left right sameInputs
  leftAligned rightAligned empty leftUnique rightUnique leftEvent leftMember leftFiber leftFound supported =
    supportedMatchingMetadataForward name key world error value nameEq keyEq left right sameInputs
      leftAligned rightAligned empty leftUnique rightUnique (acceptedAuthenticatedRegistrationMatching name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs))
      leftEvent leftMember leftFiber leftFound supported

||| Fully sealed backward boundary, retaining the honest event-coverage premise.
export
0 acceptedSupportedGeneratedMetadataBackward :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  AlignedTransitions name key world error value nameEq keyEq left ->
  AlignedTransitions name key world error value nameEq keyEq right ->
  bindings (registry initial) = [] ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (rightEvent : RegistrationEvent name key world error value) -> Elem rightEvent (rightScannedEvents (acceptedAuthenticatedRegistrationMatching name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs))) ->
  (rightFiber : Fiber name key value world error) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} (eventChild rightEvent) (registry rightFinal) = Just rightFiber ->
  isSupported {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} @{keyEq} (eventChild rightEvent) rightFinal = True ->
  (leftEvent : RegistrationEvent name key world error value ** leftFiber : Fiber name key value world error **
    (Elem leftEvent (leftScannedEvents (acceptedAuthenticatedRegistrationMatching name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs))),
     eventChild leftEvent = (renameBackward (currentNameBijection (endpointRenaming sameInputs)) (eventChild rightEvent)),
     lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
       @{nameEq} (renameBackward (currentNameBijection (endpointRenaming sameInputs)) (eventChild rightEvent)) (registry leftFinal) = Just leftFiber,
     MatchedEndpointStaticMetadata name key world error value (generatedGenerationBijection sameInputs) leftEvent rightEvent leftFiber rightFiber))
acceptedSupportedGeneratedMetadataBackward name key world error value nameEq keyEq left right sameInputs
  leftAligned rightAligned empty leftUnique rightUnique rightEvent rightMember rightFiber rightFound supported =
    supportedMatchingMetadataBackward name key world error value nameEq keyEq left right sameInputs
      leftAligned rightAligned empty leftUnique rightUnique (acceptedAuthenticatedRegistrationMatching name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs))
      rightEvent rightMember rightFiber rightFound supported

||| BOTH matched parent generations are actual ORIGINAL insertion births.
||| These are historical activation stamps, not an endpoint-currentness claim.
export
0 acceptedMatchedParentBirths :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (renaming : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq renaming left right) ->
  (leftEvent, rightEvent : RegistrationEvent name key world error value) ->
  Elem leftEvent (leftScannedEvents (acceptedAuthenticatedRegistrationMatching name key world error value nameEq left right renaming registrations)) ->
  Elem rightEvent (rightScannedEvents (acceptedAuthenticatedRegistrationMatching name key world error value nameEq left right renaming registrations)) ->
  (matched : RegistrationEventMatch renaming leftEvent rightEvent) ->
  (CurrentGenerationBirth name key world error value left (eventParent leftEvent)
      (activationParentGeneration (leftMatchedActivation matched)),
   CurrentGenerationBirth name key world error value right (eventParent rightEvent)
      (activationParentGeneration (rightMatchedActivation matched)))
acceptedMatchedParentBirths name key world error value nameEq left right renaming registrations leftEvent rightEvent leftMember rightMember matched =
  (acceptedLeftEventParentBirth name key world error value nameEq left right renaming registrations leftEvent leftMember
    (leftMatchedActivation matched) (leftActivationPresent matched),
   acceptedRightEventParentBirth name key world error value nameEq left right renaming registrations rightEvent rightMember
    (rightMatchedActivation matched) (rightActivationPresent matched))

||| Generation names are read back only from the authenticated parent births.
export
0 acceptedMatchedParentNames :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (renaming : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq renaming left right) ->
  (leftEvent, rightEvent : RegistrationEvent name key world error value) ->
  Elem leftEvent (leftScannedEvents (acceptedAuthenticatedRegistrationMatching name key world error value nameEq left right renaming registrations)) ->
  Elem rightEvent (rightScannedEvents (acceptedAuthenticatedRegistrationMatching name key world error value nameEq left right renaming registrations)) ->
  (matched : RegistrationEventMatch renaming leftEvent rightEvent) ->
  (generationName (activationParentGeneration (leftMatchedActivation matched)) = eventParent leftEvent,
   generationName (activationParentGeneration (rightMatchedActivation matched)) = eventParent rightEvent)
acceptedMatchedParentNames name key world error value nameEq left right renaming registrations leftEvent rightEvent leftMember rightMember matched =
  (cong generationName (currentBirthStampExact (fst
    (acceptedMatchedParentBirths name key world error value nameEq left right renaming registrations leftEvent rightEvent leftMember rightMember matched))),
   cong generationName (currentBirthStampExact (snd
    (acceptedMatchedParentBirths name key world error value nameEq left right renaming registrations leftEvent rightEvent leftMember rightMember matched))))

||| Endpoint parent fields are exactly the names of the AUTHENTICATED matched
||| parent generations. Those generations are mapped by endpointEventMatch;
||| their endpoint-currentness/phi coherence is intentionally still separate.
export
0 acceptedEndpointParentGenerations :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (renaming : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq renaming left right) ->
  (leftEvent, rightEvent : RegistrationEvent name key world error value) ->
  Elem leftEvent (leftScannedEvents (acceptedAuthenticatedRegistrationMatching name key world error value nameEq left right renaming registrations)) ->
  Elem rightEvent (rightScannedEvents (acceptedAuthenticatedRegistrationMatching name key world error value nameEq left right renaming registrations)) ->
  (leftFiber, rightFiber : Fiber name key value world error) ->
  (metadata : MatchedEndpointStaticMetadata name key world error value renaming leftEvent rightEvent leftFiber rightFiber) ->
  (fiberParent leftFiber = ChildOf (generationName (activationParentGeneration (leftMatchedActivation (endpointEventMatch metadata)))),
   fiberParent rightFiber = ChildOf (generationName (activationParentGeneration (rightMatchedActivation (endpointEventMatch metadata)))))
acceptedEndpointParentGenerations name key world error value nameEq left right renaming registrations leftEvent rightEvent leftMember rightMember leftFiber rightFiber metadata =
  (trans (leftEndpointBirthParent metadata) (cong ChildOf (sym (fst
    (acceptedMatchedParentNames name key world error value nameEq left right renaming registrations leftEvent rightEvent leftMember rightMember (endpointEventMatch metadata))))),
   trans (rightEndpointBirthParent metadata) (cong ChildOf (sym (snd
    (acceptedMatchedParentNames name key world error value nameEq left right renaming registrations leftEvent rightEvent leftMember rightMember (endpointEventMatch metadata))))))

||| Source parent support plus genuine matched births proves exact parent
||| CURRENT stamps and phi coherence, not opposite support/retirement truth.
export
0 acceptedSupportedParentForward :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  AlignedTransitions name key world error value nameEq keyEq left ->
  AlignedTransitions name key world error value nameEq keyEq right ->
  bindings (registry initial) = [] ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  (leftEvent, rightEvent : RegistrationEvent name key world error value) ->
  Elem leftEvent (leftScannedEvents (acceptedAuthenticatedRegistrationMatching name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs))) -> Elem rightEvent (rightScannedEvents (acceptedAuthenticatedRegistrationMatching name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs))) ->
  (matched : RegistrationEventMatch (generatedGenerationBijection sameInputs) leftEvent rightEvent) ->
  isSupported {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} @{keyEq} (eventParent leftEvent) leftFinal = True ->
  (lookupCurrentGeneration @{nameEq} (eventParent leftEvent) (leftFinalGenerations (generatedRegistrationTree sameInputs)) = Just (activationParentGeneration (leftMatchedActivation matched)),
   lookupCurrentGeneration @{nameEq} (eventParent rightEvent) (rightFinalGenerations (generatedRegistrationTree sameInputs)) = Just (activationParentGeneration (rightMatchedActivation matched)),
   (renameForward (currentNameBijection (endpointRenaming sameInputs)) (eventParent leftEvent)) = eventParent rightEvent)
acceptedSupportedParentForward name key world error value nameEq keyEq left right sameInputs leftAligned rightAligned empty leftUnique
  leftEvent rightEvent leftMember rightMember matched parentSupported =
    case acceptedSupportedForwardDomain name key world error value nameEq keyEq left right sameInputs
      leftAligned rightAligned empty (eventParent leftEvent) parentSupported of
      (leftGeneration ** rightGeneration ** rightParentFiber ** (leftCurrent, rightCurrent, mapped, rightFound)) =>
        parentGenerationCurrentPacket name key world error value nameEq right (generationForward (generatedGenerationBijection sameInputs))
          (leftFinalGenerations (generatedRegistrationTree sameInputs)) (rightFinalGenerations (generatedRegistrationTree sameInputs))
          (eventParent leftEvent) (renameForward (currentNameBijection (endpointRenaming sameInputs)) (eventParent leftEvent)) (eventParent rightEvent)
          leftGeneration rightGeneration (activationParentGeneration (leftMatchedActivation matched)) (activationParentGeneration (rightMatchedActivation matched))
          leftCurrent rightCurrent mapped (matchedParentGeneration matched)
          (authenticatedBirthStampsSame name key world error value nameEq keyEq left leftUnique (eventParent leftEvent)
            leftGeneration (activationParentGeneration (leftMatchedActivation matched)) (acceptedLeftCurrentBirth name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs) (eventParent leftEvent) leftGeneration leftCurrent) (acceptedLeftEventParentBirth name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs) leftEvent leftMember (leftMatchedActivation matched) (leftActivationPresent matched)))
          (acceptedRightCurrentBirth name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs) (renameForward (currentNameBijection (endpointRenaming sameInputs)) (eventParent leftEvent)) rightGeneration rightCurrent) (acceptedRightEventParentBirth name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs) rightEvent rightMember (rightMatchedActivation matched) (rightActivationPresent matched))

||| Symmetric current-parent authentication and inverse-phi coherence.
export
0 acceptedSupportedParentBackward :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  AlignedTransitions name key world error value nameEq keyEq left ->
  AlignedTransitions name key world error value nameEq keyEq right ->
  bindings (registry initial) = [] ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (leftEvent, rightEvent : RegistrationEvent name key world error value) ->
  Elem leftEvent (leftScannedEvents (acceptedAuthenticatedRegistrationMatching name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs))) -> Elem rightEvent (rightScannedEvents (acceptedAuthenticatedRegistrationMatching name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs))) ->
  (matched : RegistrationEventMatch (generatedGenerationBijection sameInputs) leftEvent rightEvent) ->
  isSupported {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} @{keyEq} (eventParent rightEvent) rightFinal = True ->
  (lookupCurrentGeneration @{nameEq} (eventParent rightEvent) (rightFinalGenerations (generatedRegistrationTree sameInputs)) = Just (activationParentGeneration (rightMatchedActivation matched)),
   lookupCurrentGeneration @{nameEq} (eventParent leftEvent) (leftFinalGenerations (generatedRegistrationTree sameInputs)) = Just (activationParentGeneration (leftMatchedActivation matched)),
   (renameBackward (currentNameBijection (endpointRenaming sameInputs)) (eventParent rightEvent)) = eventParent leftEvent)
acceptedSupportedParentBackward name key world error value nameEq keyEq left right sameInputs leftAligned rightAligned empty rightUnique
  leftEvent rightEvent leftMember rightMember matched parentSupported =
    case acceptedSupportedBackwardDomain name key world error value nameEq keyEq left right sameInputs
      leftAligned rightAligned empty (eventParent rightEvent) parentSupported of
      (rightGeneration ** leftGeneration ** leftParentFiber ** (rightCurrent, leftCurrent, mapped, leftFound)) =>
        parentGenerationCurrentPacket name key world error value nameEq left (generationBackward (generatedGenerationBijection sameInputs))
          (rightFinalGenerations (generatedRegistrationTree sameInputs)) (leftFinalGenerations (generatedRegistrationTree sameInputs))
          (eventParent rightEvent) (renameBackward (currentNameBijection (endpointRenaming sameInputs)) (eventParent rightEvent)) (eventParent leftEvent)
          rightGeneration leftGeneration (activationParentGeneration (rightMatchedActivation matched)) (activationParentGeneration (leftMatchedActivation matched))
          rightCurrent leftCurrent mapped
          (trans (cong (generationBackward (generatedGenerationBijection sameInputs)) (sym (matchedParentGeneration matched)))
            (generationLeftInverse (generatedGenerationBijection sameInputs) (activationParentGeneration (leftMatchedActivation matched))))
          (authenticatedBirthStampsSame name key world error value nameEq keyEq right rightUnique (eventParent rightEvent)
            rightGeneration (activationParentGeneration (rightMatchedActivation matched)) (acceptedRightCurrentBirth name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs) (eventParent rightEvent) rightGeneration rightCurrent) (acceptedRightEventParentBirth name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs) rightEvent rightMember (rightMatchedActivation matched) (rightActivationPresent matched)))
          (acceptedLeftCurrentBirth name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs) (renameBackward (currentNameBijection (endpointRenaming sameInputs)) (eventParent rightEvent)) leftGeneration leftCurrent) (acceptedLeftEventParentBirth name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs) leftEvent leftMember (leftMatchedActivation matched) (leftActivationPresent matched))

||| Derive the parent premise from actual supported child metadata, without
||| asking the caller for parent support or any historical/current stamp equation.
export
0 acceptedSupportedChildParentForward :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  AlignedTransitions name key world error value nameEq keyEq left ->
  AlignedTransitions name key world error value nameEq keyEq right ->
  bindings (registry initial) = [] ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  (leftEvent, rightEvent : RegistrationEvent name key world error value) ->
  Elem leftEvent (leftScannedEvents (acceptedAuthenticatedRegistrationMatching name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs))) -> Elem rightEvent (rightScannedEvents (acceptedAuthenticatedRegistrationMatching name key world error value nameEq left right (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs))) ->
  (leftFiber, rightFiber : Fiber name key value world error) ->
  (metadata : MatchedEndpointStaticMetadata name key world error value (generatedGenerationBijection sameInputs) leftEvent rightEvent leftFiber rightFiber) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} (eventChild leftEvent) (registry leftFinal) = Just leftFiber ->
  isSupported {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} @{keyEq} (eventChild leftEvent) leftFinal = True ->
  (lookupCurrentGeneration @{nameEq} (eventParent leftEvent) (leftFinalGenerations (generatedRegistrationTree sameInputs)) = Just (activationParentGeneration (leftMatchedActivation (endpointEventMatch metadata))),
   lookupCurrentGeneration @{nameEq} (eventParent rightEvent) (rightFinalGenerations (generatedRegistrationTree sameInputs)) = Just (activationParentGeneration (rightMatchedActivation (endpointEventMatch metadata))),
   (renameForward (currentNameBijection (endpointRenaming sameInputs)) (eventParent leftEvent)) = eventParent rightEvent)
acceptedSupportedChildParentForward name key world error value nameEq keyEq {leftFinal} left right sameInputs
  leftAligned rightAligned empty leftUnique leftEvent rightEvent leftMember rightMember leftFiber rightFiber metadata leftFound supported =
    acceptedSupportedParentForward name key world error value nameEq keyEq left right sameInputs
      leftAligned rightAligned empty leftUnique leftEvent rightEvent leftMember rightMember (endpointEventMatch metadata)
      (computedSupportParent name key world error value nameEq keyEq leftFinal (eventChild leftEvent) leftFiber leftFound
        (eventParent leftEvent) (leftEndpointBirthParent metadata) supported)
