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
