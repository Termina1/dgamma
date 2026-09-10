module DGamma.R208AttachedTransportPositive

import DGamma.Core
import DGamma.Effects
import DGamma.Unified
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.Section3Example
import DGamma.CP5O19AttachedPairsSpike
import DGamma.CP5O19AttachedTransportSpike
import DGamma.R206AttachedGrammarPositive
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| The actual release's ordinal may move by any executable prefix, while
||| its exact child1 source fiber and ServiceA reason survive. This is native
||| occurrence transport, NOT action-word reconstruction or a sanctioned swap.
export
0 r208ReleaseReasonAfterNativePrefix :
  {initial : SystemState Nat ToyKey ToyValue ToyRuntime String} ->
  (earlier : Transitions initial r206ReleaseSource) ->
  AttachedReason (the (DecEq Nat) %search) 0
    (appendTransitions earlier (MoreTransitions r206ReleaseEdge NoTransitions)) []
    DGamma.CalculusChecks.providerComponent
r208ReleaseReasonAfterNativePrefix earlier = KeyReleased
  (o19AttachedReleaseAtReplay
    (MkAttachedRelease 1
      (retireFiber (freshFiber DGamma.CalculusChecks.providerComponent (ChildOf 0)))
      (MkLocatedActionOccurrence r206ReleaseSource r206Released NoTransitions
        r206ReleaseEdge NoTransitions Refl Refl)
      Refl Refl ServiceA Here Here)
    (MkLocatedActionOccurrence r206ReleaseSource r206Released earlier
      r206ReleaseEdge NoTransitions Refl Refl) Refl)
