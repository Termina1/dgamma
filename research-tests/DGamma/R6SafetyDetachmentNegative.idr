module DGamma.R6SafetyDetachmentNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

||| Safety from one replay intermediate must not license a step at another trace.
0 detachSafetyFromCurrentState :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {before, after : List name} ->
  {orderSwap : AdjacentActorOrderSwap name before after} ->
  {initial, firstFinal, secondFinal : SystemState name key value world error} ->
  {firstTrace : Transitions initial firstFinal} ->
  {secondTrace : Transitions initial secondFinal} ->
  {firstBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    before firstTrace} ->
  {secondBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    before secondTrace} ->
  {firstPremises : ReplayInvariantBundle name key world error value protocol nameEq
    keyEq firstTrace} ->
  {secondPremises : ReplayInvariantBundle name key world error value protocol nameEq
    keyEq secondTrace} ->
  AdjacentActorSwapSafety name key world error value protocol nameEq keyEq
    orderSwap firstTrace firstBlocks firstPremises ->
  AdjacentActorSwapSafety name key world error value protocol nameEq keyEq
    orderSwap secondTrace secondBlocks secondPremises
detachSafetyFromCurrentState safety = safety
