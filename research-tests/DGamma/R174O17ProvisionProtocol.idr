module DGamma.R174O17ProvisionProtocol

import DGamma.Core
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Section3Example
import DGamma.Unified
import Data.Bool
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| A genuine provider program is the only yielded catalog component.
public export
r174ProvisionCatalog : Nat -> Maybe (Component ToyKey ToyValue ToyRuntime String)
r174ProvisionCatalog Z = Just providerComponent
r174ProvisionCatalog (S tag) = Nothing

||| Admit only dependency-free components. Tag-free programs have rank 1;
||| programs with a yield tag have rank 0, so our installing child outranks its
||| yielding parent. No equality comparison of effect functions is needed.
public export
r174ProvisionRank : Component ToyKey ToyValue ToyRuntime String -> Maybe Nat
r174ProvisionRank (MkComponent (MkCoeffectSpec [] unique) provision program) =
  if allRecursive (\step => isNothing (registrationYieldTag step)) program
    then Just 1 else Just 0
r174ProvisionRank (MkComponent (MkCoeffectSpec (key :: rest) unique) provision program) = Nothing
