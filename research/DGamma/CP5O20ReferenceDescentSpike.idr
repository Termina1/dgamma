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

||| Fold one ACTUAL O19 progress step with its recursively produced result.
||| Build the stopped packet and its reference proof simultaneously; no scalar
||| equation observes a nested computed fold and no new endpoint is guessed.
export
0 o20ReferenceStoppedAfterProgress :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) -> (sourceOrder, goalOrder : List name) ->
  (reference, goalState : SystemState name key value world error) ->
  (goalLinearization : LinearizesSupport name key world error value nameEq keyEq goalState goalOrder) ->
  {initial, finalState : SystemState name key value world error} -> (trace : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) ->
  (progress : O20OperationalProgress name key world error value protocol nameEq keyEq sourceOrder goalOrder goalState trace blocks premises) ->
  (rest : O20ReferenceStoppedPermutation name key world error value protocol nameEq keyEq
    (chosenTargetOrder (orientedChoice (progressChoice progress))) goalOrder reference goalState goalLinearization
    (blockSwapTrace (progressStep progress)) (blockSwapBlocks (progressStep progress)) (blockSwapPremises (progressStep progress))) ->
  O20ReferenceStoppedPermutation name key world error value protocol nameEq keyEq
    sourceOrder goalOrder reference goalState goalLinearization trace blocks premises
o20ReferenceStoppedAfterProgress nameEq keyEq protocol sourceOrder goalOrder reference goalState goalLinearization
  trace blocks premises progress (MkO20ReferenceStoppedPermutation reached reachedReference) =
    MkO20ReferenceStoppedPermutation
      (MkO20StoppedOperationalPermutation (stoppedOrder reached) (stoppedFinal reached) (stoppedTrace reached)
        (stoppedBlocks reached) (stoppedPremises reached) (stoppedUnique reached)
        (ActorPermutationStep (chosenOrderSwap (orientedChoice (progressChoice progress))) (stoppedCertificate reached))
        (OperationalActorStep (chosenOrderSwap (orientedChoice (progressChoice progress))) (stoppedCertificate reached)
          blocks premises (chosenSafety (orientedChoice (progressChoice progress))) (progressStep progress) (stoppedRealized reached))
        (stoppedChoiceAbsent reached))
      reachedReference

||| Structural induction on the real finite operational descent. The reference
||| is transported to the SAME reached order at each step, before recursing on
||| that step's actual trace/blocks/full bundle/uniqueness.
export
0 o20ReferenceDescent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) -> (sourceOrder, goalOrder : List name) ->
  (reference, goalState : SystemState name key value world error) ->
  (goalLinearization : LinearizesSupport name key world error value nameEq keyEq goalState goalOrder) ->
  {initial, finalState : SystemState name key value world error} -> (trace : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq trace) ->
  O20SupportedReferenceOrders name key world error value nameEq keyEq reference sourceOrder goalOrder ->
  O20OperationalDescent name key world error value protocol nameEq keyEq sourceOrder goalOrder goalState goalLinearization trace blocks premises unique ->
  O20ReferenceStoppedPermutation name key world error value protocol nameEq keyEq
    sourceOrder goalOrder reference goalState goalLinearization trace blocks premises
o20ReferenceDescent {finalState} nameEq keyEq protocol sourceOrder goalOrder reference goalState goalLinearization
  trace blocks premises unique capital (O20DescentBlocked blocked) =
    MkO20ReferenceStoppedPermutation
      (MkO20StoppedOperationalPermutation sourceOrder finalState trace blocks premises unique
        ActorPermutationDone (OperationalActorDone blocks premises) blocked) capital
o20ReferenceDescent nameEq keyEq protocol sourceOrder goalOrder reference goalState goalLinearization
  trace blocks premises unique capital (O20DescentStep progress rest) =
    o20ReferenceStoppedAfterProgress nameEq keyEq protocol sourceOrder goalOrder reference goalState goalLinearization
      trace blocks premises progress
      (o20ReferenceDescent nameEq keyEq protocol (chosenTargetOrder (orientedChoice (progressChoice progress))) goalOrder
        reference goalState goalLinearization (blockSwapTrace (progressStep progress))
        (blockSwapBlocks (progressStep progress)) (blockSwapPremises (progressStep progress)) (progressUnique progress)
        (o20SwapSupportedReference (chosenOrderSwap (orientedChoice (progressChoice progress))) capital
          (orientedGoalReverse (progressChoice progress))) rest)
