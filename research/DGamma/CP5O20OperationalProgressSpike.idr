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
||| This packet does not assert supported-reference order preservation or completeness.
public export
record O20OperationalProgress
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key) (sourceOrder, goalOrder : List name)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState)
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace)
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) where
  constructor MkO20OperationalProgress
  0 progressChoice : O20OrientedSafeSwap name key world error value protocol nameEq keyEq
    sourceOrder goalOrder trace blocks premises
  0 progressStep : OperationalAdjacentBlockSwap name key world error value protocol nameEq keyEq
    (chosenOrderSwap (orientedChoice progressChoice)) trace blocks premises (chosenSafety (orientedChoice progressChoice))
  0 progressUnique : UniqueRawNameInsertions name key world error value nameEq keyEq (blockSwapTrace progressStep)
  0 progressDecrease : (rankInversions (map (o20GoalRank nameEq goalOrder) sourceOrder) =
    S (rankInversions (map (o20GoalRank nameEq goalOrder) (chosenTargetOrder (orientedChoice progressChoice)))))

||| Simultaneously PRODUCE the actual O19 step, reached full block/bundle
||| packet, actual reached uniqueness and fixed-goal drop from ONE safe choice.
||| There is no caller-supplied reached trace, replay, or decrease witness.
export
0 o20RealizeOrientedProgress :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, goalOrder : List name} ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) ->
  (choice : O20OrientedSafeSwap name key world error value protocol nameEq keyEq sourceOrder goalOrder trace blocks premises) ->
  (O20OperationalProgress name key world error value protocol nameEq keyEq sourceOrder goalOrder trace blocks premises)
o20RealizeOrientedProgress {name} {key} {world} {error} {value} {goalOrder}
  nameEq keyEq protocol trace blocks premises choice =
    MkO20OperationalProgress choice
      (o19ActualOperationalBlockSwap nameEq keyEq protocol
        (chosenOrderSwap (orientedChoice choice)) trace blocks premises
        (chosenSafety (orientedChoice choice)) (chosenSourceUnique (orientedChoice choice)))
      (blockSwapUniqueInsertions name key world error value protocol nameEq keyEq
        (o19ActualOperationalBlockSwap nameEq keyEq protocol
          (chosenOrderSwap (orientedChoice choice)) trace blocks premises
          (chosenSafety (orientedChoice choice)) (chosenSourceUnique (orientedChoice choice)))
        (chosenSourceUnique (orientedChoice choice)))
      (o20ActorSwapMeasureDrop nameEq goalOrder (chosenOrderSwap (orientedChoice choice))
        (orientedGoalUnique choice) (orientedGoalReverse choice))

||| Finite safe-candidate enumeration now realizes each returned positive
||| as an actual operational step and a strict global decrease. Nothing still
||| means blocked, NOT canonicality or finite-linear-extension completeness.
export
0 o20SelectOperationalProgress :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) -> (sourceOrder, goalOrder : List name) ->
  (UniqueKeys goalOrder) ->
  {initial, finalState : SystemState name key value world error} -> (trace : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) ->
  (0 unique : UniqueRawNameInsertions name key world error value nameEq keyEq trace) ->
  (Maybe (O20OperationalProgress name key world error value protocol nameEq keyEq sourceOrder goalOrder trace blocks premises))
o20SelectOperationalProgress nameEq keyEq protocol sourceOrder goalOrder goalUnique trace blocks premises unique =
  map (\choice => o20RealizeOrientedProgress nameEq keyEq protocol trace blocks premises choice)
    (o20SelectOrientedSafeBlocks nameEq keyEq protocol sourceOrder goalOrder goalUnique trace blocks premises unique)
