module DGamma.CP5O20OperationalProgressSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceWorkMeasureSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O19OperationalAssemblySpike
import DGamma.CP5O20SafeBlockSelectionSpike
import DGamma.CP5O20LinearExtensionSpike
import DGamma.CP5O20BlockMeasureSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5UniqueRawNameCanonicalCapital
import Data.List
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| One actual goal-oriented whole-block step with reached uniqueness and
||| exact GLOBAL decrease on the SAME choice. Every witness is erased.
||| This packet does not assert common-state linearization or completeness.
public export
record O20OperationalProgress
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key) (sourceOrder, goalOrder : List name)
  (goalState : SystemState name key value world error)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState)
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace)
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) where
  constructor MkO20OperationalProgress
  0 progressChoice : O20OrientedSafeSwap name key world error value protocol nameEq keyEq
    sourceOrder goalOrder goalState trace blocks premises
  0 progressStep : OperationalAdjacentBlockSwap name key world error value protocol nameEq keyEq
    (chosenOrderSwap (orientedChoice progressChoice)) trace blocks premises (chosenSafety (orientedChoice progressChoice))
  0 progressUnique : UniqueRawNameInsertions name key world error value nameEq keyEq (blockSwapTrace progressStep)
  0 progressDecrease : (rankInversions (map (o20GoalRank nameEq goalOrder) sourceOrder) =
    S (rankInversions (map (o20GoalRank nameEq goalOrder) (chosenTargetOrder (orientedChoice progressChoice)))))
