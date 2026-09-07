module DGamma.R180O19ObservedCompletion

import DGamma.Core
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Metatheory
import DGamma.Section3Example
import DGamma.Unified
import DGamma.R179O19ObservedExecution
import Data.Maybe
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Observe the actual normalization VALUE before projecting its binding.
||| This is not a consumer-target claim: the result retains the observed Boolean
||| and neither assumes nor concludes that the service is available.
export
0 r180ProviderResolutionObserved :
  (table : OwnedTable ToyKey ToyValue DGamma.Section3Example.toySpecA) ->
  (0 tableObserved : (restrictOwnedPreservingOrder @{%search}
    DGamma.Section3Example.toySpecA (ownedValues (ownedA True)) = table)) ->
  (present : Bool) ->
  (0 bindingObserved : (memberKey @{%search} ServiceA (ownedValues table) = present)) ->
  (providerOf {name = Nat} {key = ToyKey} {value = ToyValue}
    {world = ToyRuntime} {error = String} @{%search} @{%search} ServiceA
    (registry {name = Nat} {key = ToyKey} {value = ToyValue}
      {world = ToyRuntime} {error = String} r179ObservedProviderFinished) =
    (if present then Just 0 else Nothing))
r180ProviderResolutionObserved table tableObserved True bindingObserved =
  rewrite tableObserved in rewrite bindingObserved in Refl
r180ProviderResolutionObserved table tableObserved False bindingObserved =
  rewrite tableObserved in rewrite bindingObserved in Refl
