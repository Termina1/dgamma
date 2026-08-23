module DGamma.R8ZeroDerivationOperationalStepNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

||| Attack the claimed one-step certificate strength.  For any nontrivial actor
||| order swap, the public step record can be built with the zero-node finite
||| derivation if the caller supplies a second decomposition of the unchanged
||| trace at the target order.  No AdjacentSwapResult or orientation is consumed.
public export
0 zeroDerivationOperationalStepStillAccepted :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {sourceOrder, targetOrder : List name} ->
  {orderSwap : AdjacentActorOrderSwap name sourceOrder targetOrder} ->
  {initial, sourceFinal : SystemState name key value world error} ->
  {sourceTrace : Transitions initial sourceFinal} ->
  {sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace} ->
  {sourcePremises : ReplayInvariantBundle name key world error value protocol nameEq
    keyEq sourceTrace} ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq
    orderSwap sourceTrace sourceBlocks sourcePremises) ->
  (targetBlocksOnUnchangedTrace : ActorBlockDecomposition name key world error value
    nameEq keyEq targetOrder sourceTrace) ->
  RelationalReplayEndpoint name key world error value nameEq keyEq sourceFinal
    sourceFinal ->
  SameExternalOrchestration nameEq sourceTrace sourceTrace ->
  OperationalAdjacentBlockSwap name key world error value protocol nameEq keyEq
    orderSwap sourceTrace sourceBlocks sourcePremises safety
zeroDerivationOperationalStepStillAccepted {sourceFinal} {sourceTrace} {sourcePremises}
  safety targetBlocks endpoint sameInputs =
    MkOperationalAdjacentBlockSwap sourceFinal sourceTrace
      FiniteAdjacentSwapDone targetBlocks endpoint sourcePremises sameInputs
