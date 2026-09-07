module DGamma.CP5O19ActivationRowSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19OpeningPropagationSpike
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| One observed row boundary: the moved right activation is now immediately
||| after the exact untouched prefix. The actual reached bundle, uniqueness,
||| derivation and its structural node count belong to this SAME output.
||| This does not yet assert a whole Cartesian plan or installed target blocks.
public export
record O19ActivationRow
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, sourceFinal, before, rightBefore, rightAfter : SystemState name key value world error}
  (source : Transitions initial sourceFinal)
  (earlier : Transitions initial before)
  (sourceRight : Transition rightBefore rightAfter)
  (crossings : Nat) where
  constructor MkO19ActivationRow
  rowCursor : O19ReachedCursor name key world error value protocol nameEq keyEq source
  rowMiddle : SystemState name key value world error
  rowRight : Transition before rowMiddle
  rowRest : Transitions rowMiddle (cursorFinal rowCursor)
  0 rowDecomposition : appendTransitions earlier (MoreTransitions rowRight rowRest) = cursorTrace rowCursor
  0 rowAction : transitionAction rowRight = transitionAction sourceRight
  0 rowTag : transitionTag rowRight = transitionTag sourceRight
  0 rowActor : transitionActor rowRight = transitionActor sourceRight
  0 rowActivation : PaperActivationStep rowRight
  0 rowNodeCount : finiteAdjacentSwapNodeCount (cursorDerivation rowCursor) = crossings
