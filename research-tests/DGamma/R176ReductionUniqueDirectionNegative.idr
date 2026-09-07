module DGamma.R176ReductionUniqueDirectionNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5UniqueRawNameDeletion
import Decidable.Equality

%default total
%unbound_implicits off

||| Statement-boundary negative only: no concrete reuse-reducing execution is
||| claimed. Actual reduced uniqueness cannot be supplied as original uniqueness.
0 reductionUniqueCannotRunBackward :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} ->
  (reduction : ClosingFreeReduction name key world error value protocol nameEq keyEq original) ->
  (UniqueRawNameInsertions name key world error value nameEq keyEq (reducedTrace reduction)) ->
  (UniqueRawNameInsertions name key world error value nameEq keyEq (reducedTrace reduction))
reductionUniqueCannotRunBackward name key world error value protocol nameEq keyEq reduction reducedUnique =
  uniqueInsertionsAfterReduction name key world error value nameEq keyEq protocol reduction reducedUnique
