module DGamma.L2R3BarrierStates

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.L2R2SmallStates
import Decidable.Equality

%default total
%unbound_implicits off

||| One-origin barrier fixture: cuts0..5 ARE the inherited native small states.
||| At cut5 insert always-available Root4 S after key-forced Root3 R; then
||| Begin2/Finish2. Every new registry expression is native insertion/replacement
||| from smallState5, never an independently reconstructed uniqueness proof.
||| Indices >=8 denote the final state and do not assert additional edges.
public export
barrierState : Nat -> SystemState Nat Bool (\key => Unit) Unit String
barrierState Z = smallState 0
barrierState (S Z) = smallState 1
barrierState (S (S Z)) = smallState 2
barrierState (S (S (S Z))) = smallState 3
barrierState (S (S (S (S Z)))) = smallState 4
barrierState (S (S (S (S (S Z))))) = smallState 5
barrierState (S (S (S (S (S (S Z)))))) = MkSystemState ()
  (insertBinding @{%search} 4 (freshFiber (smallComponent False) Root) (registry (smallState 5)) Refl)
barrierState (S (S (S (S (S (S (S Z))))))) = MkSystemState ()
  (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) (insertBinding @{%search} 4 (freshFiber (smallComponent False) Root) (registry (smallState 5)) Refl))
barrierState (S (S (S (S (S (S (S (S later)))))))) = MkSystemState ()
  (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) (insertBinding @{%search} 4 (freshFiber (smallComponent False) Root) (registry (smallState 5)) Refl)))
