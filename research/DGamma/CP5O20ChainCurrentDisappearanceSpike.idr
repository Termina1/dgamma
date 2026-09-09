module DGamma.CP5O20ChainCurrentDisappearanceSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20DiscardedBirthOriginSpike
import DGamma.CP5O20DiscardedSelectionCoverageSpike
import DGamma.CP5O20GlobalActivationHistorySpike
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5UniqueRawNameDeletion
import DGamma.CP5O20DeletionDisappearanceSpike
import DGamma.CP5O20DeletionRetainedBirthSpike
import DGamma.CP5O20WholeClosingJoinSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| At a genuinely present endpoint, the native current stamp is the exact
||| generated birth's stamp. The existing global raw-insertion uniqueness
||| hypothesis compares ONLY insertion counts, not dependent occurrences.
||| This hypothesis is already part of the accepted O20 macro telescope.
export
0 o20UniqueGeneratedCurrent :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (finalOrdinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationTraceScan nameEq Z [] trace finalOrdinal live ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  (bindings (registry initial) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq trace ->
  (child, parent : name) -> (component : Component key value world error) ->
  (birth : LocatedGeneratedRegistration child parent component trace) ->
  (fiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry finalState) = Just fiber) ->
  (lookupCurrentGeneration @{nameEq} child live = Just (registrationGeneration birth))
o20UniqueGeneratedCurrent name key world error value nameEq keyEq trace finalOrdinal live scan aligned empty unique
  child parent component birth fiber present =
    case currentDomainFromEmptyScan name key world error value nameEq keyEq trace finalOrdinal live scan aligned empty child fiber present of
      (generation ** current) =>
        case currentBirthFromGenerationScan name key world error value nameEq trace finalOrdinal live scan child generation current of
          MkCurrentGenerationBirth actualParent actualComponent actualBirth exact =>
            trans current (cong Just (trans exact
              (cong (MkRegistrationGeneration child)
                (uniqueInsertionPosition unique child actualParent (ChildOf parent) actualComponent component
                  actualBirth (generatedRegistrationActionOccurrence birth)))))

||| Selected-class current disappearance at the ACTUAL node. Its own whole
||| source scan plus unique insertion counts identify the selected stamp;
||| the native withdrawal result, not a canonical absence premise, closes it.
export
0 o20SelectedClassifiedPresentAbsent :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol nameEq keyEq trace) ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq trace) ->
  (step : DeletionChainStep name key world error value protocol nameEq keyEq trace premises candidate) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq trace ->
  (generation : RegistrationGeneration name) ->
  (classified : DeletedGenerationClassification name key world error value nameEq trace generation) ->
  Elem generation (selectedRegistrations candidate) ->
  (fiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (generationName generation) (registry finalState) = Just fiber) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (generationName generation)
    (registry (survivingFinal (deletionResult step))) = Nothing)
o20SelectedClassifiedPresentAbsent name key world error value protocol nameEq keyEq
  trace premises candidate step unique generation classified member fiber present =
    o20CurrentWithdrawalAbsent (registeredWithdrawn (deletionResult step) generation member)
      (trans (o20UniqueGeneratedCurrent name key world error value nameEq keyEq trace
        (originalFinalOrdinal (deletionResult step)) (originalFinalLive (deletionResult step))
        (o20DeletionOriginalScan candidate (deletionResult step))
        (replayAligned (chainReplayCapital premises)) (replayInitialEmpty (chainReplayCapital premises)) unique
        (generationName generation) (deletedParent classified) (deletedComponent classified)
        (deletedOccurrence classified) fiber present)
        (cong Just (deletedOccurrenceGeneration classified)))

||| Whole-chain current-coordinate disappearance for EVERY classified birth,
||| under the macro's existing unique-raw-insertion hypothesis. Every node
||| observes its actual original lookup: absent stays absent; selected-present
||| uses B3; retained uses R203's actual birth/close and the node's bijection.
||| The closing-free base rejects the classification. No tail absence is input.
export
0 o20ClassifiedChainAbsent :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (generationEq : DecEq (RegistrationGeneration name)) ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) -> (target : Transitions initial targetFinal) ->
  (premises : CanonicalizationPremises name key world error value protocol nameEq keyEq source) ->
  (derivation : ClosingFreeDeletionDerivation name key world error value protocol nameEq keyEq source target) ->
  NoClosingEpisodes name key world error value nameEq keyEq target ->
  UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  (generation : RegistrationGeneration name) ->
  DeletedGenerationClassification name key world error value nameEq source generation ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (generationName generation) (registry targetFinal) = Nothing)
o20ClassifiedChainAbsent name key world error value protocol nameEq keyEq generationEq _ _ premises
  (ClosingFreeDeletionDone trace) noClosing unique generation classified =
    absurd (o20EveryDeletedGenerationSelected name key world error value protocol nameEq keyEq generationEq
      trace trace premises (ClosingFreeDeletionDone trace) noClosing generation classified)
o20ClassifiedChainAbsent name key world error value protocol nameEq keyEq generationEq
  {initial} {sourceFinal} {targetFinal} _ _ sourcePremises
  (ClosingFreeDeletionStep source premises candidate step target rest) noClosing unique generation classified =
    atObservation (lookupFiber {name} {key} {value} {world} {error} @{nameEq}
      (generationName generation) (registry sourceFinal)) Refl
  where
    0 atObservation : (observed : Maybe (Fiber name key value world error)) ->
      (lookupFiber {name} {key} {value} {world} {error} @{nameEq}
        (generationName generation) (registry sourceFinal) = observed) ->
      (lookupFiber {name} {key} {value} {world} {error} @{nameEq}
        (generationName generation) (registry targetFinal) = Nothing)
    atObservation Nothing exact =
      o20DeletionChainPreservesAbsence nameEq keyEq
        (ClosingFreeDeletionStep source premises candidate step target rest) (generationName generation) exact
    atObservation (Just fiber) exact =
      case isElem @{generationEq} generation (selectedRegistrations candidate) of
        Yes member => o20DeletionChainPreservesAbsence nameEq keyEq rest (generationName generation)
          (o20SelectedClassifiedPresentAbsent name key world error value protocol nameEq keyEq
            source premises candidate step unique generation classified member fiber exact)
        No outside =>
          case o20DeletionRetainedClosingBirth name key world error value protocol nameEq keyEq
            source premises candidate step generation classified outside of
            (birth ** (stamp, closing)) =>
              replace {p = \actor => lookupFiber {name} {key} {value} {world} {error} @{nameEq}
                actor (registry targetFinal) = Nothing} (cong generationName stamp)
                (o20ClassifiedChainAbsent name key world error value protocol nameEq keyEq generationEq
                  (survivingTrace (deletionResult step)) target (nextPremises step) rest noClosing
                  (uniqueInsertionsAfterDeletionDerivation name key world error value nameEq keyEq protocol
                    (ClosingFreeDeletionStep source premises candidate step (survivingTrace (deletionResult step))
                      (ClosingFreeDeletionDone (survivingTrace (deletionResult step)))) unique)
                  (generationForward (deletionProducerGenerationRenaming (deletionProducerCapital step)) generation)
                  (o20RetainedBirthClassified nameEq (survivingTrace (deletionResult step))
                    (deletionProducerGenerationRenaming (deletionProducerCapital step)) generation
                    (MkO20RetainedGenerationBirth (deletedParent classified) (deletedComponent classified) birth stamp) closing))

||| EVERY full accepted present-vestigial packet disappears at its actual
||| independent canonical endpoint, not only generations selected at the head.
||| Deletion follows the supplied real derivation; its own sorting relation
||| preserves the derived absence. No cumulative-list equality is assumed.
export
0 o20CanonicalVestigialDisappears :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (generationEq : DecEq (RegistrationGeneration name)) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq left) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  (selected : name) ->
  (packet : VestigialEndpointGeneration name key world error value nameEq keyEq
    (leftFinalGenerations registrations) (leftDeletedGenerations registrations) selected leftFinal) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected
    (registry (canonicalFinal (canonicalSchedule capital))) = Nothing)
o20CanonicalVestigialDisappears name key world error value protocol nameEq keyEq generationEq
  left right mapping registrations capital unique selected packet =
    o20ReducedAbsenceSurvivesSorting nameEq keyEq left capital selected
      (replace {p = \actor => lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor
        (registry (reducedFinal (capitalReduction capital))) = Nothing}
        (cong generationName (currentBirthStampExact
          (acceptedLeftCurrentBirth name key world error value nameEq left right mapping registrations selected
            (vestigialGeneration packet) (vestigialGenerationCurrent packet))))
        (o20ClassifiedChainAbsent name key world error value protocol nameEq keyEq generationEq
          left (reducedTrace (capitalReduction capital)) (capitalPremises capital)
          (reductionDeletionDerivation (capitalReduction capital)) (reducedClosingFree (capitalReduction capital)) unique
          (vestigialGeneration packet)
          (o20AcceptedDiscardedBirthClassified name key world error value nameEq left right mapping registrations
            (vestigialGeneration packet) (vestigialBirthDiscarded packet))))

||| Reverse discarded-membership coverage for either native activation scan.
||| This consumes the ACTUAL chronology produced in R203, so it covers the
||| right side without exporting/changing a private bilateral symmetry helper.
export
0 o20NativeDiscardedOrigin :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (ordinal : Nat) -> (index : RegistrationIndexState name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> (finalIndex : RegistrationIndexState name) ->
  (events : List (RegistrationEvent name key world error value)) ->
  O20NativeActivationScan nameEq ordinal index trace finalIndex events ->
  (generation : RegistrationGeneration name) -> Elem generation (indexedDeletedGenerations finalIndex) ->
  O20DiscardedTraceOrigin name key world error value ordinal (indexedDeletedGenerations index) generation trace
o20NativeDiscardedOrigin name key world error value nameEq ordinal
  (MkRegistrationIndexState live activations counts discarded) trace finalIndex events scan generation member =
    case scan of
      O20ActivationScanEnd => O20DiscardedBefore member
      O20ActivationScanOrdinary action edge rest shape ordinary later =>
        o20DiscardedOriginPrepend name key world error value ordinal discarded
          (indexedDeletedGenerations (advanceRegistrationIndex @{nameEq} ordinal action
            (MkRegistrationIndexState live activations counts discarded))) generation edge rest
          (o20IndexDiscardedAdvance name key world error value nameEq ordinal action
            (MkRegistrationIndexState live activations counts discarded))
          (o20NativeDiscardedOrigin name key world error value nameEq (S ordinal)
            (advanceRegistrationIndex @{nameEq} ordinal action (MkRegistrationIndexState live activations counts discarded))
            rest finalIndex events later generation member)
      O20ActivationScanDeleted {child} {parent} {component} edge rest shape closing later =>
        o20DiscardedOriginAfterDiscard name key world error value ordinal discarded generation child parent component
          edge rest shape (deletedParentEpisodeCloses closing)
          (o20NativeDiscardedOrigin name key world error value nameEq (S ordinal)
            (advanceDeletedRegistrationIndex @{nameEq} ordinal child parent component (MkRegistrationIndexState live activations counts discarded))
            rest finalIndex events later generation member)
      O20ActivationScanRetained {child} {parent} {component} {events = laterEvents} edge rest shape retained later =>
        o20DiscardedOriginPrepend name key world error value ordinal discarded
          (indexedDeletedGenerations (advanceSurvivingRegistrationIndex @{nameEq} ordinal child parent component
            (MkRegistrationIndexState live activations counts discarded))) generation edge rest
          (o20SurvivingDiscardedObserved name key world error value nameEq ordinal child parent component
            live activations counts discarded (lookupParentActivation @{nameEq} parent activations) Refl)
          (o20NativeDiscardedOrigin name key world error value nameEq (S ordinal)
            (advanceSurvivingRegistrationIndex @{nameEq} ordinal child parent component (MkRegistrationIndexState live activations counts discarded))
            rest finalIndex laterEvents later generation member)

||| Right-side present-vestigial disappearance uses the SECOND accepted
||| ORIGINAL chronology, not an assumed swapped correspondence. Its exact
||| native discarded membership yields the real right deleted classification.
export
0 o20RightCanonicalVestigialDisappears :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (generationEq : DecEq (RegistrationGeneration name)) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq right) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (selected : name) ->
  (packet : VestigialEndpointGeneration name key world error value nameEq keyEq
    (rightFinalGenerations registrations) (rightDeletedGenerations registrations) selected rightFinal) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected
    (registry (canonicalFinal (canonicalSchedule capital))) = Nothing)
o20RightCanonicalVestigialDisappears name key world error value protocol nameEq keyEq generationEq
  left right mapping registrations capital unique selected packet =
    case o20AcceptedActivationHistories nameEq left right mapping registrations of
      (leftEvents ** (rightEvents ** (leftScan, rightScan, leftPositions, rightPositions, leftCounts, rightCounts))) =>
        o20ReducedAbsenceSurvivesSorting nameEq keyEq right capital selected
          (replace {p = \actor => lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor
            (registry (reducedFinal (capitalReduction capital))) = Nothing}
            (cong generationName (currentBirthStampExact
              (acceptedRightCurrentBirth name key world error value nameEq left right mapping registrations selected
                (vestigialGeneration packet) (vestigialGenerationCurrent packet))))
            (o20ClassifiedChainAbsent name key world error value protocol nameEq keyEq generationEq
              right (reducedTrace (capitalReduction capital)) (capitalPremises capital)
              (reductionDeletionDerivation (capitalReduction capital)) (reducedClosingFree (capitalReduction capital)) unique
              (vestigialGeneration packet)
              (o20DiscardedOriginClassified name key world error value nameEq right (vestigialGeneration packet)
                (o20NativeDiscardedOrigin name key world error value nameEq Z emptyRegistrationIndex right
                  (rightFinalIndex registrations) rightEvents rightScan (vestigialGeneration packet)
                  (vestigialBirthDiscarded packet)))))
