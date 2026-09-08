module DGamma.CP5O20OperationalDescentSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceWorkMeasureSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O20SafeBlockSelectionSpike
import DGamma.CP5O20LinearExtensionSpike
import DGamma.CP5O20BlockMeasureSpike
import DGamma.CP5O20OperationalProgressSpike
import DGamma.CP5UniqueRawNameInsertions
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Actual finite operational descent to a checked blocked choice. Each
||| recursive tail is on the SAME produced O19 trace/blocks/full bundle/unique.
||| Blocked is deliberately NOT named canonical: completeness is still owed.
public export
data O20OperationalDescent :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (sourceOrder, goalOrder : List name) ->
  (goalState : SystemState name key value world error) ->
  (goalLinearization : LinearizesSupport name key world error value nameEq keyEq goalState goalOrder) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq trace) -> Type where
  O20DescentBlocked :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {protocol : RegistrationProtocol key value world error} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} -> {sourceOrder, goalOrder : List name} ->
    {goalState : SystemState name key value world error} ->
    {goalLinearization : LinearizesSupport name key world error value nameEq keyEq goalState goalOrder} ->
    {initial, finalState : SystemState name key value world error} -> {trace : Transitions initial finalState} ->
    {blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace} ->
    {premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace} ->
    {unique : UniqueRawNameInsertions name key world error value nameEq keyEq trace} ->
    (0 blocked : (o20SelectOperationalProgress nameEq keyEq protocol sourceOrder goalOrder goalState goalLinearization trace blocks premises unique = Nothing)) ->
    O20OperationalDescent name key world error value protocol nameEq keyEq sourceOrder goalOrder goalState goalLinearization trace blocks premises unique
  O20DescentStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {protocol : RegistrationProtocol key value world error} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} -> {sourceOrder, goalOrder : List name} ->
    {goalState : SystemState name key value world error} ->
    {goalLinearization : LinearizesSupport name key world error value nameEq keyEq goalState goalOrder} ->
    {initial, finalState : SystemState name key value world error} -> {trace : Transitions initial finalState} ->
    {blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace} ->
    {premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace} ->
    {unique : UniqueRawNameInsertions name key world error value nameEq keyEq trace} ->
    (0 progress : O20OperationalProgress name key world error value protocol nameEq keyEq sourceOrder goalOrder goalState trace blocks premises) ->
    (0 rest : O20OperationalDescent name key world error value protocol nameEq keyEq
      (chosenTargetOrder (orientedChoice (progressChoice progress))) goalOrder goalState goalLinearization
      (blockSwapTrace (progressStep progress)) (blockSwapBlocks (progressStep progress)) (blockSwapPremises (progressStep progress)) (progressUnique progress)) ->
    O20OperationalDescent name key world error value protocol nameEq keyEq sourceOrder goalOrder goalState goalLinearization trace blocks premises unique

||| Zero measure excludes any positive progress by its OWN exact drop.
||| The explicit Maybe observation supplies the honest blocked equation.
export
0 o20DescentZeroObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) -> (sourceOrder, goalOrder : List name) ->
  (goalState : SystemState name key value world error) ->
  (goalLinearization : LinearizesSupport name key world error value nameEq keyEq goalState goalOrder) ->
  {initial, finalState : SystemState name key value world error} -> (trace : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq trace) ->
  (rankInversions (map (o20GoalRank nameEq goalOrder) sourceOrder) = Z) ->
  (observed : Maybe (O20OperationalProgress name key world error value protocol nameEq keyEq sourceOrder goalOrder goalState trace blocks premises)) ->
  (o20SelectOperationalProgress nameEq keyEq protocol sourceOrder goalOrder goalState goalLinearization trace blocks premises unique = observed) ->
  (O20OperationalDescent name key world error value protocol nameEq keyEq sourceOrder goalOrder goalState goalLinearization trace blocks premises unique)
o20DescentZeroObserved nameEq keyEq protocol sourceOrder goalOrder goalState goalLinearization trace blocks premises unique measured Nothing observed =
  O20DescentBlocked observed
o20DescentZeroObserved nameEq keyEq protocol sourceOrder goalOrder goalState goalLinearization trace blocks premises unique measured (Just progress) observed =
  absurd (trans (sym measured) (progressDecrease progress))

||| Successor case at an EXPLICIT actual selection. The smaller argument is
||| an internal induction hypothesis, supplied only by the structural loop.
export
0 o20DescentSuccessorObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) -> (sourceOrder, goalOrder : List name) ->
  (goalState : SystemState name key value world error) ->
  (goalLinearization : LinearizesSupport name key world error value nameEq keyEq goalState goalOrder) ->
  {initial, finalState : SystemState name key value world error} -> (trace : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq trace) ->
  (fuel : Nat) ->
  (smaller : (nextOrder : List name) -> {nextFinal : SystemState name key value world error} ->
    (nextTrace : Transitions initial nextFinal) ->
    (nextBlocks : ActorBlockDecomposition name key world error value nameEq keyEq nextOrder nextTrace) ->
    (nextPremises : ReplayInvariantBundle name key world error value protocol nameEq keyEq nextTrace) ->
    (nextUnique : UniqueRawNameInsertions name key world error value nameEq keyEq nextTrace) ->
    (rankInversions (map (o20GoalRank nameEq goalOrder) nextOrder) = fuel) ->
    (O20OperationalDescent name key world error value protocol nameEq keyEq nextOrder goalOrder goalState goalLinearization nextTrace nextBlocks nextPremises nextUnique)) ->
  (rankInversions (map (o20GoalRank nameEq goalOrder) sourceOrder) = S fuel) ->
  (observed : Maybe (O20OperationalProgress name key world error value protocol nameEq keyEq sourceOrder goalOrder goalState trace blocks premises)) ->
  (o20SelectOperationalProgress nameEq keyEq protocol sourceOrder goalOrder goalState goalLinearization trace blocks premises unique = observed) ->
  (O20OperationalDescent name key world error value protocol nameEq keyEq sourceOrder goalOrder goalState goalLinearization trace blocks premises unique)
o20DescentSuccessorObserved nameEq keyEq protocol sourceOrder goalOrder goalState goalLinearization trace blocks premises unique fuel smaller measured Nothing observed =
  O20DescentBlocked observed
o20DescentSuccessorObserved nameEq keyEq protocol sourceOrder goalOrder goalState goalLinearization trace blocks premises unique fuel smaller measured (Just progress) observed =
  O20DescentStep progress
    (smaller (chosenTargetOrder (orientedChoice (progressChoice progress)))
      (blockSwapTrace (progressStep progress)) (blockSwapBlocks (progressStep progress))
      (blockSwapPremises (progressStep progress)) (progressUnique progress)
      (successorEqualityInjective (trans (sym (progressDecrease progress)) measured)))
