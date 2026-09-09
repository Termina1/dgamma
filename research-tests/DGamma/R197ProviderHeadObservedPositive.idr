module DGamma.R197ProviderHeadObservedPositive

import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.Section3Example
import DGamma.CP5ProviderHeadObservedSpike
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| The executable producer on a TWO-binding registry: an active ServiceA
||| provider at the head and an inactive consumer in the tail. Its packet
||| includes both before/retired head equations, not an assumed resolver fact.
public export
r197ActiveProviderHead :
  ProviderHeadObserved Nat ToyKey ToyRuntime String ToyValue %search %search ServiceA 0
    DGamma.CalculusChecks.providerComponent Root False (ownedA True) (Active id EmptyView)
    [Bind 1 (freshFiber emptyConsumerComponent Root)]
r197ActiveProviderHead =
  providerHeadObserved {name = Nat} {key = ToyKey} {world = ToyRuntime} {error = String} {value = ToyValue}
    %search %search ServiceA 0 DGamma.CalculusChecks.providerComponent Root False
    (ownedA True) (Active id EmptyView) [Bind 1 (freshFiber emptyConsumerComponent Root)]
