module DGamma.CP5O19ActivationInsertionRowSpike

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
import DGamma.CP5O19ResolvedOpeningRowSpike
import DGamma.CP5O20BeginObservationSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Same simultaneous row boundary for a moved orchestration node.
public export
record O19OrchestrationRow
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, sourceFinal, before, rightBefore, rightAfter : SystemState name key value world error}
  (source : Transitions initial sourceFinal)
  (earlier : Transitions initial before)
  (sourceRight : Transition rightBefore rightAfter)
  (crossings : Nat) where
  constructor MkO19OrchestrationRow
  orchestrationRowCursor : O19ReachedCursor name key world error value protocol nameEq keyEq source
  orchestrationRowMiddle : SystemState name key value world error
  orchestrationRowRight : Transition before orchestrationRowMiddle
  orchestrationRowRest : Transitions orchestrationRowMiddle (cursorFinal orchestrationRowCursor)
  0 orchestrationRowDecomposition : appendTransitions earlier (MoreTransitions orchestrationRowRight orchestrationRowRest) = cursorTrace orchestrationRowCursor
  0 orchestrationRowAction : transitionAction orchestrationRowRight = transitionAction sourceRight
  0 orchestrationRowTag : transitionTag orchestrationRowRight = transitionTag sourceRight
  0 orchestrationRowActor : transitionActor orchestrationRowRight = transitionActor sourceRight
  0 orchestrationRowClass : PaperOrchestrationStep orchestrationRowRight
  0 orchestrationRowNodeCount : finiteAdjacentSwapNodeCount (cursorDerivation orchestrationRowCursor) = crossings


||| Constructor-owned zero row; its count observes only finite Done.
export
0 o19OrchestrationRowZero :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, sourceFinal, before, rightAfter : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) -> (earlier : Transitions initial before) ->
  (right : Transition before rightAfter) -> (later : Transitions rightAfter sourceFinal) ->
  (appendTransitions earlier (MoreTransitions right later) = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  (0 unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  PaperOrchestrationStep right ->
  O19OrchestrationRow name key world error value protocol nameEq keyEq source earlier right 0
o19OrchestrationRowZero {sourceFinal} {rightAfter} nameEq keyEq protocol source earlier
  right later decomposition premises unique activation =
    MkO19OrchestrationRow
      (MkO19ReachedCursor sourceFinal source premises unique FiniteAdjacentSwapDone)
      rightAfter right later decomposition Refl Refl Refl activation Refl

