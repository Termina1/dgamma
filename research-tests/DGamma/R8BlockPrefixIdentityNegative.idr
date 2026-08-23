module DGamma.R8BlockPrefixIdentityNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

||| A caller-selected source-to-source correspondence cannot replace the exact
||| identity root required by WholeBlockSwapDerivation.
public export
0 replaceBlockLabelRootByArbitraryMap :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {sourceInitial, sourceFinal, targetFinal :
    SystemState name key value world error} ->
  {sourceTrace : Transitions sourceInitial sourceFinal} ->
  {targetTrace : Transitions sourceInitial targetFinal} ->
  {leftActor, rightActor : name} ->
  {leftBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
    leftActor sourceTrace} ->
  {rightBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
    rightActor sourceTrace} ->
  {derivation : FiniteAdjacentSwapDerivation name key world error value protocol
    nameEq keyEq sourceTrace targetTrace} ->
  {positions : List (Nat, Nat)} ->
  (alternateRoot : ActionRegistrationReplayCorrespondence name key world error
    value sourceTrace sourceTrace) ->
  DerivationCrossesBlockPositions name key world error value protocol nameEq keyEq
    sourceTrace leftBlock rightBlock alternateRoot derivation positions ->
  DerivationCrossesBlockPositions name key world error value protocol nameEq keyEq
    sourceTrace leftBlock rightBlock
      (identityActionRegistrationReplayCorrespondence sourceTrace)
      derivation positions
replaceBlockLabelRootByArbitraryMap alternateRoot labels = labels
