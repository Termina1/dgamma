module DGamma.CP5O20ChainCurrentDisappearanceSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
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
