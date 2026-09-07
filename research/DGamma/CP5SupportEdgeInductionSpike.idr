module DGamma.CP5SupportEdgeInductionSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4Support
import DGamma.CP4SupportSolution
import DGamma.CP5CurrentGenerationBirthSpike
import Control.WellFounded
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

0 supportNameRanksEqual :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) ->
  (state : SystemState name key value world error) -> (selected : name) -> (leftRank, rightRank : Nat) ->
  NameProtocolRank protocol nameEq state selected leftRank -> NameProtocolRank protocol nameEq state selected rightRank -> leftRank = rightRank
supportNameRanksEqual name key world error value protocol nameEq state selected leftRank rightRank
  (MkNameProtocolRank leftFiber leftFound leftRanked) (MkNameProtocolRank rightFiber rightFound rightRanked) =
    case justInjective (trans (sym leftFound) rightFound) of
      Refl => justInjective (trans (sym leftRanked) rightRanked)

0 supportEdgeInductionAtRank :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) -> RegistryProtocolRanked protocol nameEq state -> RegistryParentRanksIncrease protocol nameEq state ->
  (property : name -> Type) ->
  ((selected : name) -> (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected state = True) ->
    ((lower : name) -> SupportEdge nameEq state lower selected ->
      (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} lower state = True) -> property lower) -> property selected) ->
  (rank : Nat) -> Accessible LT rank -> (selected : name) -> NameProtocolRank protocol nameEq state selected rank ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected state = True) -> property selected
supportEdgeInductionAtRank name key world error value protocol nameEq keyEq state ranked parentOrdered property step rank (Access smaller) selected selectedRanked supported =
  step selected supported (\lower, edge, lowerSupported =>
    case supportEdgeRankIncreases {name = name} {key = key} {value = value} {world = world} {error = error} protocol nameEq state ranked parentOrdered edge of
      MkRankedSupportEdge lowerRank upperRank lowerRanked upperRanked increases =>
        supportEdgeInductionAtRank name key world error value protocol nameEq keyEq state ranked parentOrdered property step lowerRank
          (smaller lowerRank (replace {p = LT lowerRank}
            (supportNameRanksEqual name key world error value protocol nameEq state selected upperRank rank upperRanked selectedRanked) increases))
          lower lowerRanked lowerSupported)
