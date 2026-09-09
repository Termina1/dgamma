module DGamma.L2R7ControlStates

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.L2R2SmallStates
import DGamma.L2R3BarrierStates
import Decidable.Equality

%default total
%unbound_implicits off

||| One-origin states: unchanged barrier cuts0..6, then Retire3/Remove3,
||| then Begin2/Finish2. No independently reconstructed registry endpoints.
||| Inputs >=10 select the final state, not extra edges.
public export
controlState : Nat -> SystemState Nat Bool (\key => Unit) Unit String
controlState Z = barrierState 0
controlState (S Z) = barrierState 1
controlState (S (S Z)) = barrierState 2
controlState (S (S (S Z))) = barrierState 3
controlState (S (S (S (S Z)))) = barrierState 4
controlState (S (S (S (S (S Z))))) = barrierState 5
controlState (S (S (S (S (S (S Z)))))) = barrierState 6
controlState (S (S (S (S (S (S (S Z))))))) = MkSystemState () (replaceBinding @{%search} 3 (retireFiber (freshFiber (smallComponent True) Root)) (registry (barrierState 6)))
controlState (S (S (S (S (S (S (S (S Z)))))))) = MkSystemState () (deleteBinding @{%search} 3 (replaceBinding @{%search} 3 (retireFiber (freshFiber (smallComponent True) Root)) (registry (barrierState 6))))
controlState (S (S (S (S (S (S (S (S (S Z))))))))) = MkSystemState () (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) (deleteBinding @{%search} 3 (replaceBinding @{%search} 3 (retireFiber (freshFiber (smallComponent True) Root)) (registry (barrierState 6)))))
controlState (S (S (S (S (S (S (S (S (S (S later)))))))))) = MkSystemState () (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) (deleteBinding @{%search} 3 (replaceBinding @{%search} 3 (retireFiber (freshFiber (smallComponent True) Root)) (registry (barrierState 6))))))
