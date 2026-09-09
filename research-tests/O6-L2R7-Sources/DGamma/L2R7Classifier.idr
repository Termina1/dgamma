module DGamma.L2R7Classifier

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3ForcedClosure
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R7ObservedAny
import Data.Bool
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Extract both true factors by one Bool elimination. Call sites pass the
||| actual two observations; no equality of reconstructed dependent records.
export
0 acceptedConjunction : (left, right : Bool) -> (0 accepted : left && right = True) ->
  (left = True, right = True)
acceptedConjunction False right accepted = absurd accepted
acceptedConjunction True right accepted = (Refl, accepted)

||| The Ord Nat zero comparison agrees with Data.Nat.lte.
export
0 leZero : (n : Nat) -> (Z <= n) = True
leZero Z = Refl
leZero (S n) = Refl

||| Right-argument elimination for the successor bridge, separate from the
||| recursive left-argument elimination in leToLte.
export
0 leSuccessorBridge : (n : Nat) ->
  (0 earlier : (m : Nat) -> (n <= m) = lte n m) -> (m : Nat) ->
  (S n <= m) = lte (S n) m
leSuccessorBridge n earlier Z = Refl
leSuccessorBridge n earlier (S m) = earlier m

||| Library Ord Nat comparison equals the structurally reflected lte test.
export
0 leToLte : (n, m : Nat) -> (n <= m) = lte n m
leToLte Z m = leZero m
leToLte (S n) m = leSuccessorBridge n (leToLte n) m

||| Close a non-strict seed bound by observing the strict-order decider.
||| Equality is obtained by antisymmetry, not a nonlinear two-index pattern.
export
0 forcedSeedBeforeObserved : {rootInput, keyForced : Nat -> Type} ->
  (seed, target : Nat) -> (observed : Dec (LT seed target)) ->
  (0 equation : isLT seed target = observed) -> (0 ordered : LTE seed target) ->
  (0 prior : ForcedRootInput rootInput keyForced seed) -> (0 root : rootInput target) ->
  ForcedRootInput rootInput keyForced target
forcedSeedBeforeObserved seed target (Yes earlier) equation ordered prior root = OrderForces prior root earlier
forcedSeedBeforeObserved {rootInput} {keyForced} seed target (No notEarlier) equation ordered prior root =
  replace {p = ForcedRootInput rootInput keyForced}
    (antisymmetric ordered (notLTImpliesGTE notEarlier)) prior

||| A successful computed prefix-seed test gives an independent KeyForces or
||| OrderForces derivation. Catalog authenticity is fixed to the actual trail.
export
0 classifyForcedHitSound : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (entry : RootCatalogEntry name key world error value) ->
  (0 member : Elem entry (scanRootCatalog 0 trail)) ->
  AnyHit (\seed => catalogOrdinal seed <= catalogOrdinal entry &&
    keyForcedOrdinal nameEq keyEq trail (catalogOrdinal seed)) (scanRootCatalog 0 trail) ->
  ForcedOnTrace nameEq keyEq trail (catalogOrdinal entry)
classifyForcedHitSound nameEq keyEq trail entry member hit =
  forcedSeedBeforeObserved (catalogOrdinal (hitItem hit)) (catalogOrdinal entry)
    (isLT (catalogOrdinal (hitItem hit)) (catalogOrdinal entry)) Refl
    (lteReflectsLTE (catalogOrdinal (hitItem hit)) (catalogOrdinal entry)
      (trans (sym (leToLte (catalogOrdinal (hitItem hit)) (catalogOrdinal entry)))
        (fst (acceptedConjunction (catalogOrdinal (hitItem hit) <= catalogOrdinal entry)
          (keyForcedOrdinal nameEq keyEq trail (catalogOrdinal (hitItem hit))) (hitAccepted hit)))))
    (KeyForces (elemMap catalogOrdinal (hitMember hit))
      (snd (acceptedConjunction (catalogOrdinal (hitItem hit) <= catalogOrdinal entry)
        (keyForcedOrdinal nameEq keyEq trail (catalogOrdinal (hitItem hit))) (hitAccepted hit))))
    (elemMap catalogOrdinal member)
