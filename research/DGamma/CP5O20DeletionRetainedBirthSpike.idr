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

||| A retained birth from the step's own accounting has its exact forward
||| generation coordinate. Both occurrence-origin equations belong to this step.
export
0 o20DeletionRetainedBirthGeneration :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol nameEq keyEq trace) ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq trace) ->
  (step : DeletionChainStep name key world error value protocol nameEq keyEq trace premises candidate) ->
  {child, parent : name} -> {component : Component key value world error} ->
  (birth : LocatedGeneratedRegistration child parent component (survivingTrace (deletionResult step))) ->
  (generation : RegistrationGeneration name) ->
  (registrationGeneration (canonicalToOriginal (deletionRegistrationAccounting step) birth) = generation) ->
  (generationForward (deletionProducerGenerationRenaming (deletionProducerCapital step)) generation =
    registrationGeneration birth)
o20DeletionRetainedBirthGeneration trace premises candidate step birth generation exact =
  trans
    (cong (generationForward (deletionProducerGenerationRenaming (deletionProducerCapital step)))
      (trans (sym exact) (cong registrationGeneration (deletionRegistrationOriginExact step birth))))
    (replace {p = \mapping =>
      (generationForward mapping
        (registrationGeneration (replayGeneratedRegistrationOrigin (deletionOccurrenceCorrespondence step) birth)) =
        registrationGeneration birth)}
      (o20DeletionStepGenerationRenaming trace premises candidate step)
      (replayGeneratedOrdinalPreserved (deletionOccurrenceCorrespondence step) birth))

||| An actual surviving generated Insert and its exact forward source stamp.
||| This packet does not contain, or imply, a later parent Unload.
public export
record O20RetainedGenerationBirth
  (name, key, world, error : Type) (value : key -> Type)
  (mapping : RegistrationGenerationBijection name)
  (generation : RegistrationGeneration name)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) where
  constructor MkO20RetainedGenerationBirth
  0 retainedParent : name
  0 retainedComponent : Component key value world error
  0 retainedBirth : LocatedGeneratedRegistration (generationName generation)
    retainedParent retainedComponent trace
  0 retainedGenerationExact :
    (generationForward mapping generation = registrationGeneration retainedBirth)
