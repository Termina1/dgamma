module DGamma.CP5O20DeletionRetainedBirthSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| The actual deletion step's occurrence map uses its own operational
||| generation bijection, by the step's stored producer exactness equation.
export
0 o20DeletionStepGenerationRenaming :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol nameEq keyEq trace) ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq trace) ->
  (step : DeletionChainStep name key world error value protocol nameEq keyEq trace premises candidate) ->
  (replayGenerationRenaming (deletionOccurrenceCorrespondence step) =
    deletionProducerGenerationRenaming (deletionProducerCapital step))
o20DeletionStepGenerationRenaming trace premises candidate step =
  cong replayGenerationRenaming (deletionOccurrenceCorrespondenceExact step)
