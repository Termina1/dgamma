module DGamma.R176UnsealedOriginUniqueNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5UniqueRawNameInsertions
import Decidable.Equality

%default total
%unbound_implicits off

||| A bare all-action map is not the sealed injective operational derivation.
0 unsealedOriginCannotTransportUnique :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> {target : Transitions initial targetFinal} ->
  (origin : ActionRegistrationReplayCorrespondence name key world error value source target) ->
  (UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (UniqueRawNameInsertions name key world error value nameEq keyEq target)
unsealedOriginCannotTransportUnique name key world error value protocol nameEq keyEq origin unique =
  uniqueInsertionsAfterFiniteDerivation name key world error value protocol nameEq keyEq origin unique
