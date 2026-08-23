module DGamma.R6OperationalOccurrenceFoldPositive

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

||| External recursive-fold consumer: at an actor-step node the generated origin
||| is definitionally the current finite block derivation origin composed with
||| the rest of the operational actor fold.
public export
0 operationalStepGeneratedOriginExact :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {before, middle, after : List name} ->
  {orderSwap : AdjacentActorOrderSwap name before middle} ->
  {restCertificate : CertifiedActorPermutation name middle after} ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {sourceTrace : Transitions initial sourceFinal} ->
  {sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    before sourceTrace} ->
  {sourcePremises : ReplayInvariantBundle name key world error value protocol nameEq
    keyEq sourceTrace} ->
  {targetTrace : Transitions initial targetFinal} ->
  (replay : OperationalActorPermutation name key world error value protocol nameEq
    keyEq (ActorPermutationStep orderSwap restCertificate) sourceTrace
      sourceBlocks sourcePremises targetTrace) ->
  {child, parent : name} -> {component : Component key value world error} ->
  (occurrence : LocatedGeneratedRegistration child parent component targetTrace) ->
  case replay of
    OperationalActorStep _ _ _ _ _ step rest =>
      replayGeneratedRegistrationOrigin
        (operationalPermutationOccurrenceCorrespondence replay) occurrence =
      replayGeneratedRegistrationOrigin (blockSwapOccurrenceCorrespondence step)
        (replayGeneratedRegistrationOrigin
          (operationalPermutationOccurrenceCorrespondence rest) occurrence)
operationalStepGeneratedOriginExact
  (OperationalActorStep orderSwap restCertificate sourceBlocks sourcePremises
    safety step rest) occurrence = Refl
