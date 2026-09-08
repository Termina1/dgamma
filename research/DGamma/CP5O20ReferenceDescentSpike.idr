module DGamma.CP5O20ReferenceDescentSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O20SafeBlockSelectionSpike
import DGamma.CP5O20LinearExtensionSpike
import DGamma.CP5O20OperationalProgressSpike
import DGamma.CP5O20OperationalDescentSpike
import DGamma.CP5O20SupportedReferenceSpike
import DGamma.CP5UniqueRawNameInsertions
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Simultaneous actually stopped operational permutation and fixed supported
||| reference invariant. The stopped order is not claimed equal to the goal.
public export
record O20ReferenceStoppedPermutation
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key) (sourceOrder, goalOrder : List name)
  (reference, goalState : SystemState name key value world error)
  (goalLinearization : LinearizesSupport name key world error value nameEq keyEq goalState goalOrder)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState)
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace)
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) where
  constructor MkO20ReferenceStoppedPermutation
  0 referenceStopped : O20StoppedOperationalPermutation name key world error value protocol nameEq keyEq
    sourceOrder goalOrder goalState goalLinearization trace blocks premises
  0 referenceStoppedOrders : O20SupportedReferenceOrders name key world error value nameEq keyEq
    reference (stoppedOrder referenceStopped) goalOrder
