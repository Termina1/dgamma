module DGamma.CP5O20PresentVestigialSelectionSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20DiscardedBirthOriginSpike
import DGamma.CP5O20WholeClosingJoinSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Every FULL present-vestigial packet at the accepted original left endpoint
||| is selected by the ACTUAL closing-free deletion chain. Its own native
||| discarded membership produces the birth classification; R203's recursive
||| retained-close theorem supplies selection, including the closing-free base.
||| No selected-list equality or coverage callback is an input.
export
0 everyPresentVestigialSelected :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (generationEq : DecEq (RegistrationGeneration name)) ->
  {initial, sourceFinal, targetFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) -> (target : Transitions initial targetFinal) ->
  (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping source right) ->
  (premises : CanonicalizationPremises name key world error value protocol nameEq keyEq source) ->
  (derivation : ClosingFreeDeletionDerivation name key world error value protocol nameEq keyEq source target) ->
  NoClosingEpisodes name key world error value nameEq keyEq target ->
  (selected : name) ->
  (packet : VestigialEndpointGeneration name key world error value nameEq keyEq
    (leftFinalGenerations registrations) (leftDeletedGenerations registrations) selected sourceFinal) ->
  Elem (vestigialGeneration packet) (closingFreeDeletionGenerations derivation)
everyPresentVestigialSelected name key world error value protocol nameEq keyEq generationEq
  source target right mapping registrations premises derivation noClosing selected packet =
    o20EveryDeletedGenerationSelected name key world error value protocol nameEq keyEq generationEq
      source target premises derivation noClosing (vestigialGeneration packet)
      (o20AcceptedDiscardedBirthClassified name key world error value nameEq source right mapping registrations
        (vestigialGeneration packet) (vestigialBirthDiscarded packet))
