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
