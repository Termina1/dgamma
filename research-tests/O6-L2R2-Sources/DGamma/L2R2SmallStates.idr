module DGamma.L2R2SmallStates

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Two effectless, dependency-free components. True declares the single key
||| True; False declares no keys. Declaration occupancy, not active table
||| contents, makes the child's/root's True provisions collide natively.
public export
smallComponent : Bool -> Component Bool (\key => Unit) Unit String
smallComponent False = MkComponent (MkCoeffectSpec [] UniqueNil) (MkCoeffectSpec [] UniqueNil) []
smallComponent True = MkComponent (MkCoeffectSpec [] UniqueNil)
  (MkCoeffectSpec [True] (UniqueCons (\present => uninhabited present) UniqueNil)) []

||| Explicit small native states, never produced by recursive checked-evaluator
||| builders: parent0 and child1 (declares True), unrelated actor2, late root3
||| (declares True). Cuts0..7 are Begin0/Finish0/Retire1/Remove1/Insert3/Begin2/
||| Finish2; cut8 is the alternate Begin2-before-Insert3 intermediate. Larger
||| indices denote the same final state and are NOT additional checked edges.
public export
smallState : Nat -> SystemState Nat Bool (\key => Unit) Unit String
smallState Z = MkSystemState ()
  (insertBinding @{%search} 1 (freshFiber (smallComponent True) (ChildOf 0)) (insertBinding @{%search} 2 (freshFiber (smallComponent False) Root) (insertBinding @{%search} 0 (freshFiber (smallComponent False) Root) emptyContext Refl) Refl) Refl)
smallState (S Z) = MkSystemState ()
  (insertBinding @{%search} 1 (freshFiber (smallComponent True) (ChildOf 0)) (insertBinding @{%search} 2 (freshFiber (smallComponent False) Root) (insertBinding @{%search} 0 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) emptyContext Refl) Refl) Refl)
smallState (S (S Z)) = MkSystemState ()
  (insertBinding @{%search} 1 (freshFiber (smallComponent True) (ChildOf 0)) (insertBinding @{%search} 2 (freshFiber (smallComponent False) Root) (insertBinding @{%search} 0 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) emptyContext Refl) Refl) Refl)
smallState (S (S (S Z))) = MkSystemState ()
  (insertBinding @{%search} 1 (retireFiber (freshFiber (smallComponent True) (ChildOf 0))) (insertBinding @{%search} 2 (freshFiber (smallComponent False) Root) (insertBinding @{%search} 0 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) emptyContext Refl) Refl) Refl)
smallState (S (S (S (S Z)))) = MkSystemState ()
  (insertBinding @{%search} 2 (freshFiber (smallComponent False) Root) (insertBinding @{%search} 0 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) emptyContext Refl) Refl)
smallState (S (S (S (S (S Z))))) = MkSystemState ()
  (insertBinding @{%search} 3 (freshFiber (smallComponent True) Root) (insertBinding @{%search} 2 (freshFiber (smallComponent False) Root) (insertBinding @{%search} 0 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) emptyContext Refl) Refl) Refl)
smallState (S (S (S (S (S (S Z)))))) = MkSystemState ()
  (insertBinding @{%search} 3 (freshFiber (smallComponent True) Root) (insertBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) (insertBinding @{%search} 0 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) emptyContext Refl) Refl) Refl)
smallState (S (S (S (S (S (S (S Z))))))) = MkSystemState ()
  (insertBinding @{%search} 3 (freshFiber (smallComponent True) Root) (insertBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) (insertBinding @{%search} 0 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) emptyContext Refl) Refl) Refl)
smallState (S (S (S (S (S (S (S (S Z)))))))) = MkSystemState ()
  (insertBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView)) (insertBinding @{%search} 0 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) emptyContext Refl) Refl)
smallState (S (S (S (S (S (S (S (S (S later))))))))) = MkSystemState ()
  (insertBinding @{%search} 3 (freshFiber (smallComponent True) Root) (insertBinding @{%search} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) (insertBinding @{%search} 0 (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView)) emptyContext Refl) Refl) Refl)
