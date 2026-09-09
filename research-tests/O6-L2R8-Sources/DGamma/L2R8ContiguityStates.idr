module DGamma.L2R8ContiguityStates

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.L2R2SmallStates
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Explicit states for three schedules from the SAME smallState4 prefix.
||| Original I5;Begin2;Finish2;Retire5;Remove5;R;S. Intermediate R crosses
||| Remove5 into B's core. Restored R is before I5 and B's original action
||| word is contiguous again. These are states, not native edge proofs.
public export
contiguityState : Nat -> SystemState Nat Bool (\key => Unit) Unit String
contiguityState Z = smallState 4
contiguityState (S Z) = MkSystemState ()
  (insertBinding @{%search} 5 (freshFiber (smallComponent False) (ChildOf 2)) (registry (smallState 4)) Refl)
contiguityState (S (S Z)) = MkSystemState ()
  (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) (insertBinding @{%search} 5 (freshFiber (smallComponent False) (ChildOf 2)) (registry (smallState 4)) Refl))
contiguityState (S (S (S Z))) = MkSystemState ()
  (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) (insertBinding @{%search} 5 (freshFiber (smallComponent False) (ChildOf 2)) (registry (smallState 4)) Refl)))
contiguityState (S (S (S (S Z)))) = MkSystemState ()
  (replaceBinding @{%search} 5 (retireFiber (freshFiber (smallComponent False) (ChildOf 2))) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) (insertBinding @{%search} 5 (freshFiber (smallComponent False) (ChildOf 2)) (registry (smallState 4)) Refl))))
contiguityState (S (S (S (S (S Z))))) = MkSystemState ()
  (deleteBinding @{%search} 5 (replaceBinding @{%search} 5 (retireFiber (freshFiber (smallComponent False) (ChildOf 2))) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) (insertBinding @{%search} 5 (freshFiber (smallComponent False) (ChildOf 2)) (registry (smallState 4)) Refl)))))
contiguityState (S (S (S (S (S (S Z)))))) = MkSystemState ()
  (insertBinding @{%search} 3 (freshFiber (smallComponent True) Root) (deleteBinding @{%search} 5 (replaceBinding @{%search} 5 (retireFiber (freshFiber (smallComponent False) (ChildOf 2))) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) (insertBinding @{%search} 5 (freshFiber (smallComponent False) (ChildOf 2)) (registry (smallState 4)) Refl))))) Refl)
contiguityState (S (S (S (S (S (S (S Z))))))) = MkSystemState ()
  (insertBinding @{%search} 4 (freshFiber (smallComponent False) Root) (insertBinding @{%search} 3 (freshFiber (smallComponent True) Root) (deleteBinding @{%search} 5 (replaceBinding @{%search} 5 (retireFiber (freshFiber (smallComponent False) (ChildOf 2))) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) (insertBinding @{%search} 5 (freshFiber (smallComponent False) (ChildOf 2)) (registry (smallState 4)) Refl))))) Refl) Refl)
contiguityState (S (S (S (S (S (S (S (S Z)))))))) = MkSystemState ()
  (insertBinding @{%search} 3 (freshFiber (smallComponent True) Root) (replaceBinding @{%search} 5 (retireFiber (freshFiber (smallComponent False) (ChildOf 2))) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) (insertBinding @{%search} 5 (freshFiber (smallComponent False) (ChildOf 2)) (registry (smallState 4)) Refl)))) Refl)
contiguityState (S (S (S (S (S (S (S (S (S Z))))))))) = MkSystemState ()
  (deleteBinding @{%search} 5 (insertBinding @{%search} 3 (freshFiber (smallComponent True) Root) (replaceBinding @{%search} 5 (retireFiber (freshFiber (smallComponent False) (ChildOf 2))) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) (insertBinding @{%search} 5 (freshFiber (smallComponent False) (ChildOf 2)) (registry (smallState 4)) Refl)))) Refl))
contiguityState (S (S (S (S (S (S (S (S (S (S Z)))))))))) = MkSystemState ()
  (insertBinding @{%search} 4 (freshFiber (smallComponent False) Root) (deleteBinding @{%search} 5 (insertBinding @{%search} 3 (freshFiber (smallComponent True) Root) (replaceBinding @{%search} 5 (retireFiber (freshFiber (smallComponent False) (ChildOf 2))) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) (insertBinding @{%search} 5 (freshFiber (smallComponent False) (ChildOf 2)) (registry (smallState 4)) Refl)))) Refl)) Refl)
contiguityState (S (S (S (S (S (S (S (S (S (S (S Z))))))))))) = MkSystemState ()
  (insertBinding @{%search} 3 (freshFiber (smallComponent True) Root) (registry (smallState 4)) Refl)
contiguityState (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))) = MkSystemState ()
  (insertBinding @{%search} 5 (freshFiber (smallComponent False) (ChildOf 2)) (insertBinding @{%search} 3 (freshFiber (smallComponent True) Root) (registry (smallState 4)) Refl) Refl)
contiguityState (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))) = MkSystemState ()
  (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) (insertBinding @{%search} 5 (freshFiber (smallComponent False) (ChildOf 2)) (insertBinding @{%search} 3 (freshFiber (smallComponent True) Root) (registry (smallState 4)) Refl) Refl))
contiguityState (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))) = MkSystemState ()
  (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) (insertBinding @{%search} 5 (freshFiber (smallComponent False) (ChildOf 2)) (insertBinding @{%search} 3 (freshFiber (smallComponent True) Root) (registry (smallState 4)) Refl) Refl)))
contiguityState (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))) = MkSystemState ()
  (replaceBinding @{%search} 5 (retireFiber (freshFiber (smallComponent False) (ChildOf 2))) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) (insertBinding @{%search} 5 (freshFiber (smallComponent False) (ChildOf 2)) (insertBinding @{%search} 3 (freshFiber (smallComponent True) Root) (registry (smallState 4)) Refl) Refl))))
contiguityState (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))) = MkSystemState ()
  (deleteBinding @{%search} 5 (replaceBinding @{%search} 5 (retireFiber (freshFiber (smallComponent False) (ChildOf 2))) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) (insertBinding @{%search} 5 (freshFiber (smallComponent False) (ChildOf 2)) (insertBinding @{%search} 3 (freshFiber (smallComponent True) Root) (registry (smallState 4)) Refl) Refl)))))
contiguityState (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))) = MkSystemState ()
  (insertBinding @{%search} 4 (freshFiber (smallComponent False) Root) (deleteBinding @{%search} 5 (replaceBinding @{%search} 5 (retireFiber (freshFiber (smallComponent False) (ChildOf 2))) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) (replaceBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) (insertBinding @{%search} 5 (freshFiber (smallComponent False) (ChildOf 2)) (insertBinding @{%search} 3 (freshFiber (smallComponent True) Root) (registry (smallState 4)) Refl) Refl))))) Refl)
contiguityState (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S later)))))))))))))))))) = smallState 4
