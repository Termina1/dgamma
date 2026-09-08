module DGamma.CP5O19CartesianInsertionSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP3StatementChecks
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19ActivationRowSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5UniqueRawNameInsertions
import Data.Nat
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19OpeningPropagationSpike
import DGamma.CP5O19InsertObservationSpike
import DGamma.CP4DeletionGenerationScan
import DGamma.CP5O19InsertionInsertionRowSpike
import DGamma.CP5O19ActivationInsertionRowSpike
import DGamma.CP5O19ResolvedOpeningRowSpike
import DGamma.CP5O20BeginObservationSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Project the actual source provenance at an occurrence. No replacement
||| component, source parent yield, or pair-discipline premise is invented.
export
0 o19ProvenanceAtOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) ->
  {initial, finalState, before, afterState : SystemState name key value world error} ->
  (source : Transitions initial finalState) -> (step : Transition before afterState) ->
  OccursIn step source -> RegistrationProvenance protocol nameEq source ->
  RegistrationStepProvenance protocol nameEq (transitionAction step) before
o19ProvenanceAtOccurrence protocol nameEq _ _ OccursHere (RegistrationProvenanceStep _ _ head rest) = head
o19ProvenanceAtOccurrence protocol nameEq _ step (OccursLater occurs) (RegistrationProvenanceStep _ rest head remaining) =
  o19ProvenanceAtOccurrence protocol nameEq rest step occurs remaining
