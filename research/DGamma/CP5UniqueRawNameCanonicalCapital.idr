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
