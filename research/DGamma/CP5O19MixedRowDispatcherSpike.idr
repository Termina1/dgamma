module DGamma.CP5O19MixedRowDispatcherSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19ActivationRowSpike
import DGamma.CP5O19ActivationInsertionRowSpike
import DGamma.CP5O19CartesianInsertionSpike
import DGamma.CP5O19MixedActivationRowSpike
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Unified ACTUAL row output for all four A/A, O/A, A/O, O/O orientations.
||| The same output owns its whole bundle, uniqueness, finite derivation,
||| moved labels, exact decomposition and structurally established row count.
public export
record O19MixedRow
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, sourceFinal, before, rightBefore, rightAfter : SystemState name key value world error}
  (source : Transitions initial sourceFinal)
  (earlier : Transitions initial before)
  (sourceRight : Transition rightBefore rightAfter)
  (crossings : Nat) where
  constructor MkO19MixedRow
  mixedRowCursor : O19ReachedCursor name key world error value protocol nameEq keyEq source
  mixedRowMiddle : SystemState name key value world error
  mixedRowRight : Transition before mixedRowMiddle
  mixedRowRest : Transitions mixedRowMiddle (cursorFinal mixedRowCursor)
  0 mixedRowDecomposition : appendTransitions earlier (MoreTransitions mixedRowRight mixedRowRest) = cursorTrace mixedRowCursor
  0 mixedRowAction : transitionAction mixedRowRight = transitionAction sourceRight
  0 mixedRowTag : transitionTag mixedRowRight = transitionTag sourceRight
  0 mixedRowActor : transitionActor mixedRowRight = transitionActor sourceRight
  0 mixedRowClass : Either (PaperActivationStep mixedRowRight) (PaperOrchestrationStep mixedRowRight)
  0 mixedRowNodeCount : finiteAdjacentSwapNodeCount (cursorDerivation mixedRowCursor) = crossings
