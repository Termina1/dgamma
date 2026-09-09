module DGamma.L2R3BundlePhaseStates

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.L2R2SmallStates
import DGamma.L2R3BarrierStates
import Decidable.Equality

%default total
%unbound_implicits off

||| Post-LAST-release three-edge paths from smallState4:
||| 0-1-2-3 = Begin2,R,S; 0-4-5-6 = R,Begin2,S; 0-4-7-8 = R,S,Begin2.
||| Imported states and the two new S insertions share the same native origin.
||| Alternate endpoints are kept separate; only runtime equality is intended.
||| Indices >=8 denote the final moved state, not additional checked edges.
public export
bundlePhaseState : Nat -> SystemState Nat Bool (\key => Unit) Unit String
bundlePhaseState Z = smallState 4
bundlePhaseState (S Z) = smallState 8
bundlePhaseState (S (S Z)) = smallState 9
bundlePhaseState (S (S (S Z))) = MkSystemState () (insertBinding @{%search} 4 (freshFiber (smallComponent False) Root) (registry (smallState 9)) Refl)
bundlePhaseState (S (S (S (S Z)))) = smallState 5
bundlePhaseState (S (S (S (S (S Z))))) = smallState 6
bundlePhaseState (S (S (S (S (S (S Z)))))) = MkSystemState () (insertBinding @{%search} 4 (freshFiber (smallComponent False) Root) (registry (smallState 6)) Refl)
bundlePhaseState (S (S (S (S (S (S (S Z))))))) = barrierState 6
bundlePhaseState (S (S (S (S (S (S (S (S later)))))))) = barrierState 7
