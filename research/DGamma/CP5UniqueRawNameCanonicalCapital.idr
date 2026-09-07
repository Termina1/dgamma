module DGamma.CP5UniqueRawNameCanonicalCapital

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5UniqueRawNameDeletion
import Decidable.Equality

%default total
%unbound_implicits off

||| Freshness is a separate hypothesis on the ORIGINAL trace, not a capital field.
||| The result is the exact reduction stored by this capital.
export
0 capitalReducedUniqueInsertions :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  (UniqueRawNameInsertions name key world error value nameEq keyEq original) ->
  (UniqueRawNameInsertions name key world error value nameEq keyEq
    (reducedTrace (capitalReduction capital)))
capitalReducedUniqueInsertions name key world error value protocol nameEq keyEq capital =
  uniqueInsertionsAfterReduction name key world error value nameEq keyEq protocol
    (capitalReduction capital)

||| Open the producer-owned schedule equation once. No arbitrary target trace,
||| occurrence map, or freshness field is accepted in place of the sealed chain.
export
0 capitalCanonicalUniqueInsertions :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  (UniqueRawNameInsertions name key world error value nameEq keyEq original) ->
  (UniqueRawNameInsertions name key world error value nameEq keyEq
    (canonicalTrace (canonicalSchedule capital)))
capitalCanonicalUniqueInsertions name key world error value protocol nameEq keyEq
  (MkIndependentCanonicalSchedule premises reduction ordering sorted
    supportTransport accounting _ Refl classified) unique =
      uniqueInsertionsAfterFiniteDerivation name key world error value protocol nameEq keyEq
        (sortingAdjacentDerivation sorted)
        (uniqueInsertionsAfterReduction name key world error value nameEq keyEq protocol reduction unique)

||| A whole block swap retains the injective all-action derivation, not just RAR.
export
0 blockSwapUniqueInsertions :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {sourceOrder, targetOrder : List name} ->
  {orderSwap : AdjacentActorOrderSwap name sourceOrder targetOrder} ->
  {initial, sourceFinal : SystemState name key value world error} ->
  {sourceTrace : Transitions initial sourceFinal} ->
  {sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder sourceTrace} ->
  {sourcePremises : ReplayInvariantBundle name key world error value protocol nameEq keyEq sourceTrace} ->
  {safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq orderSwap sourceTrace sourceBlocks sourcePremises} ->
  (step : OperationalAdjacentBlockSwap name key world error value protocol nameEq keyEq
    orderSwap sourceTrace sourceBlocks sourcePremises safety) ->
  (UniqueRawNameInsertions name key world error value nameEq keyEq sourceTrace) ->
  (UniqueRawNameInsertions name key world error value nameEq keyEq (blockSwapTrace step))
blockSwapUniqueInsertions name key world error value protocol nameEq keyEq step =
  uniqueInsertionsAfterFiniteDerivation name key world error value protocol nameEq keyEq
    (wholeBlockFiniteDerivation (blockSwapWholeDerivation step))
