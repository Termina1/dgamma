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

||| An actual insertion is not any parent recovery transition. This makes
||| retirement discipline of the finite O/O pair genuinely vacuous locally,
||| without dropping the original whole-source retirement discipline.
export
0 o19InsertionCannotRecover :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  (step : Transition before afterState) -> (child, owner : name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  (transitionAction step = OInsert child parent component) ->
  ParentRecoveryStep owner step -> Void
o19InsertionCannotRecover step child owner parent component inserted (ParentLeaves action) =
  uninhabited (cong isLifecycleAction (trans (sym inserted) action))
o19InsertionCannotRecover step child owner parent component inserted (ParentDivertsBefore action) =
  uninhabited (cong isLifecycleAction (trans (sym inserted) action))
o19InsertionCannotRecover step child owner parent component inserted (ParentDivertsAfter action tag) =
  uninhabited (cong isLifecycleAction (trans (sym inserted) action))
o19InsertionCannotRecover step child owner parent component inserted (ParentRaises action tag) =
  uninhabited (cong isLifecycleAction (trans (sym inserted) action))

||| Reconstruct finite insertion discipline from ACTUAL pointwise provenance
||| and explicit no-recovery evidence for that short suffix.
export
0 o19InsertionDisciplineFromProvenance :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) ->
  (child : name) -> (parent : Parent name) -> (component : Component key value world error) ->
  (before : SystemState name key value world error) ->
  {afterState, finalState : SystemState name key value world error} ->
  (rest : Transitions afterState finalState) ->
  RegistrationStepProvenance protocol nameEq (OInsert child parent component) before ->
  ((owner : name) -> NoParentRecovery owner rest) ->
  RegistrationStepDiscipline protocol nameEq (OInsert child parent component) before rest
o19InsertionDisciplineFromProvenance protocol nameEq child Root component before rest provenance noRecovery = provenance
o19InsertionDisciplineFromProvenance protocol nameEq child (ChildOf owner) component before rest provenance noRecovery =
  (provenance, ParentDoesNotRecover (noRecovery owner))
