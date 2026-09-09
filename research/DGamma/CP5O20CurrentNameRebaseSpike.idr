module DGamma.CP5O20CurrentNameRebaseSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignControlCore
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5O20SupportedEndpointCapitalSpike
import DGamma.CP5O20HistoryNameTransportSpike
import DGamma.CP5O20RootOrdinalBoundarySpike
import DGamma.CP5O20ChainCurrentDisappearanceSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Retained-present class: ANY actual canonical fiber, including unsupported
||| present fibers, has a real original fiber and full same-name controls.
||| Actual presence excludes the endpoint's withdrawn-name branch; there is
||| no support restriction, supplied original presence or tail control premise.
export
0 o20CanonicalPresentOriginalControl :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (original : Transitions initial finalState) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected
    (registry (canonicalFinal (canonicalSchedule capital))) = Just fiber) ->
  ForeignRelatedFiberFound name key world error value nameEq selected
    (registry (canonicalFinal (canonicalSchedule capital))) (registry finalState) fiber
o20CanonicalPresentOriginalControl name key world error value nameEq keyEq protocol {finalState}
  original capital selected fiber present =
    foreignControlLookupFound nameEq selected (registry (canonicalFinal (canonicalSchedule capital)))
      (registry finalState) fiber present
      (fiberControlMaybeSymmetric (endpointControlsOutside (canonicalEndpoint (canonicalSchedule capital)) selected
        (canonicalPresentOutsideWithdrawals name key world error value nameEq keyEq finalState
          (canonicalFinal (canonicalSchedule capital)) (canonicalEndpoint (canonicalSchedule capital)) selected fiber present)))

||| Retained-present name rebase, including unsupported fibers: produce the
||| ORIGINAL current generation and authenticate the supplied current image.
||| The full vestigial alternative now contradicts B5's actual canonical
||| disappearance. No original-current lookup, support or agreement is input.
export
0 o20CanonicalPresentForwardName :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (generationEq : DecEq (RegistrationGeneration name)) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  (current : CurrentEndpointRenaming nameEq keyEq mapping left right registrations) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq left) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected
    (registry (canonicalFinal (canonicalSchedule capital))) = Just fiber) ->
  (generation : RegistrationGeneration name **
    (lookupCurrentGeneration @{nameEq} selected (leftFinalGenerations registrations) = Just generation,
     o20HistoricalTarget mapping generation = renameForward (currentNameBijection current) selected))
o20CanonicalPresentForwardName name key world error value protocol nameEq keyEq generationEq
  left right mapping registrations current capital unique selected fiber present =
    case o20CanonicalPresentOriginalControl name key world error value nameEq keyEq protocol left capital selected fiber present of
      MkForeignRelatedFiberFound originalFiber originalPresent controls =>
        case acceptedLeftEndpointCurrent name key world error value nameEq keyEq left right mapping registrations
          (replayAligned (chainReplayCapital (capitalPremises capital)))
          (replayInitialEmpty (chainReplayCapital (capitalPremises capital))) selected originalFiber originalPresent of
          (generation ** found) =>
            (generation ** (found, o20HistoryNonVestigialEndpoint nameEq keyEq left right mapping registrations current
              selected generation found
              (\packet => absurd (trans (sym present)
                (o20CanonicalVestigialDisappears name key world error value protocol nameEq keyEq generationEq
                  left right mapping registrations capital unique selected packet)))))

||| Symmetric retained-present rebase at the right canonical endpoint.
||| B7 excludes its FULL right vestigial alternative. The accepted left
||| native birth authenticates the backward target name, not a guessed map.
export
0 o20CanonicalPresentBackwardName :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (generationEq : DecEq (RegistrationGeneration name)) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  (current : CurrentEndpointRenaming nameEq keyEq mapping left right registrations) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq right) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected
    (registry (canonicalFinal (canonicalSchedule capital))) = Just fiber) ->
  (generation : RegistrationGeneration name **
    (lookupCurrentGeneration @{nameEq} selected (rightFinalGenerations registrations) = Just generation,
     generationName (generationBackward mapping generation) = renameBackward (currentNameBijection current) selected))
o20CanonicalPresentBackwardName name key world error value protocol nameEq keyEq generationEq
  left right mapping registrations current capital unique selected fiber present =
    case o20CanonicalPresentOriginalControl name key world error value nameEq keyEq protocol right capital selected fiber present of
      MkForeignRelatedFiberFound originalFiber originalPresent controls =>
        case acceptedRightEndpointCurrent name key world error value nameEq keyEq left right mapping registrations
          (replayAligned (chainReplayCapital (capitalPremises capital)))
          (replayInitialEmpty (chainReplayCapital (capitalPremises capital))) selected originalFiber originalPresent of
          (generation ** found) =>
            case rightCurrentGenerationMapped current selected generation found of
              Left packet => absurd (trans (sym present)
                (o20RightCanonicalVestigialDisappears name key world error value protocol nameEq keyEq generationEq
                  left right mapping registrations capital unique selected packet))
              Right (opposite ** (matched, oppositeCurrent)) =>
                (generation ** (found, trans (cong generationName matched)
                  (cong generationName (currentBirthStampExact
                    (acceptedLeftCurrentBirth name key world error value nameEq left right mapping registrations
                      (renameBackward (currentNameBijection current) selected) opposite oppositeCurrent)))))

||| One actual replay's insertion-count law for BOTH parent classes. Root
||| law is explicit; generated law comes from this correspondence's coherent
||| generated origin. No scoped-to-raw bridge or new stored field is used.
export
0 o20ReplayInsertionOrdinals :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {sourceFirst, sourceFinal, targetFirst, targetFinal : SystemState name key value world error} ->
  {source : Transitions sourceFirst sourceFinal} -> {target : Transitions targetFirst targetFinal} ->
  (correspondence : ActionRegistrationReplayCorrespondence name key world error value source target) ->
  O20RootReplayOrdinals name key world error value correspondence ->
  (selected : name) -> (parent : Parent name) -> (component : Component key value world error) ->
  (birth : LocatedActionOccurrence (OInsert selected parent component) target) ->
  (generationForward (replayGenerationRenaming correspondence)
    (MkRegistrationGeneration selected (locatedActionOrdinal (replayActionOrigin correspondence birth))) =
    MkRegistrationGeneration selected (locatedActionOrdinal birth))
o20ReplayInsertionOrdinals correspondence roots selected Root component birth = rootReplayOrdinal roots birth
o20ReplayInsertionOrdinals correspondence roots selected (ChildOf parent) component
  (MkLocatedActionOccurrence before afterState earlier edge later shape decomposition) =
    trans (cong (generationForward (replayGenerationRenaming correspondence))
      (cong (MkRegistrationGeneration selected)
        (sym (cong locatedActionOrdinal
          (replayGeneratedActionOriginCoherent correspondence
            (MkLocatedGeneratedRegistration before afterState earlier edge later shape decomposition))))))
      (replayGeneratedOrdinalPreserved correspondence
        (MkLocatedGeneratedRegistration before afterState earlier edge later shape decomposition))
