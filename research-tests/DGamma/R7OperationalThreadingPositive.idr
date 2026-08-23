module DGamma.R7OperationalThreadingPositive

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

public export
oneOperationalStepThreadsExactOutputs :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {before, after : List name} ->
  {orderSwap : AdjacentActorOrderSwap name before after} ->
  {initial, sourceFinal : SystemState name key value world error} ->
  {sourceTrace : Transitions initial sourceFinal} ->
  {sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq before sourceTrace} ->
  {sourcePremises : ReplayInvariantBundle name key world error value protocol nameEq keyEq sourceTrace} ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq
    orderSwap sourceTrace sourceBlocks sourcePremises) ->
  (step : OperationalAdjacentBlockSwap name key world error value protocol nameEq keyEq
    orderSwap sourceTrace sourceBlocks sourcePremises safety) ->
  OperationalActorPermutation name key world error value protocol nameEq keyEq
    (ActorPermutationStep orderSwap ActorPermutationDone)
    sourceTrace sourceBlocks sourcePremises (blockSwapTrace step)
oneOperationalStepThreadsExactOutputs {orderSwap} {sourceBlocks} {sourcePremises}
  safety step =
    OperationalActorStep orderSwap ActorPermutationDone sourceBlocks sourcePremises
      safety step (OperationalActorDone (blockSwapBlocks step) (blockSwapPremises step))
