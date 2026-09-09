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

||| GENERAL soundness of the precise per-entry Boolean used by classifyForced.
||| Entries are indexed by actual occurrence, never a potentially reused name.
export
0 classifyForcedSound : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (entry : RootCatalogEntry name key world error value) ->
  (0 member : Elem entry (scanRootCatalog 0 trail)) -> (observed : Bool) ->
  (0 equation : any (\seed => catalogOrdinal seed <= catalogOrdinal entry &&
    keyForcedOrdinal nameEq keyEq trail (catalogOrdinal seed)) (scanRootCatalog 0 trail) = observed) ->
  (0 accepted : observed = True) -> ForcedOnTrace nameEq keyEq trail (catalogOrdinal entry)
classifyForcedSound nameEq keyEq trail entry member observed equation accepted =
  classifyForcedHitSound nameEq keyEq trail entry member
    (anyHitObserved (\seed => catalogOrdinal seed <= catalogOrdinal entry &&
      keyForcedOrdinal nameEq keyEq trail (catalogOrdinal seed)) (scanRootCatalog 0 trail) observed equation accepted)

||| A genuine key seed below an inductively forced root. This extracts the
||| least-closure derivation's origin, independently of classifier truth.
public export
record ForcedSeedBasis (rootInput, keyForced : Nat -> Type) (target : Nat) where
  constructor MkForcedSeedBasis
  basisOrdinal : Nat
  0 basisRoot : rootInput basisOrdinal
  0 basisKey : keyForced basisOrdinal
  0 basisBefore : LTE basisOrdinal target

||| Structural induction on the independent least family produces its seed.
export
0 forcedSeedBasis : {rootInput, keyForced : Nat -> Type} -> {ordinal : Nat} ->
  ForcedRootInput rootInput keyForced ordinal -> ForcedSeedBasis rootInput keyForced ordinal
forcedSeedBasis (KeyForces {ordinal} root released) = MkForcedSeedBasis ordinal root released reflexive
forcedSeedBasis (OrderForces prior root ordered) = MkForcedSeedBasis
  (basisOrdinal (forcedSeedBasis prior)) (basisRoot (forcedSeedBasis prior))
  (basisKey (forcedSeedBasis prior))
  (transitive (basisBefore (forcedSeedBasis prior)) (lteSuccLeft ordered))

||| Single membership elimination for any over mapped ordinal membership.
export
0 anyMappedCons : {a, b : Type} -> (f : a -> b) -> (predicate : b -> Bool) ->
  (head : a) -> (items : List a) -> (wanted : b) ->
  (0 tail : Elem wanted (map f items) -> any (\item => predicate (f item)) items = True) ->
  (0 member : Elem wanted (f head :: map f items)) -> (0 accepted : predicate wanted = True) ->
  any (\item => predicate (f item)) (head :: items) = True
anyMappedCons f predicate head items _ tail Here accepted =
  rewrite accepted in anyFoldTrue (\item => predicate (f item)) items
anyMappedCons f predicate head items wanted tail (There later) accepted =
  trans (anyFoldObserved (\item => predicate (f item)) items (predicate (f head)))
    (trans (cong (\flag => predicate (f head) || flag) (tail later)) (orTrueTrue (predicate (f head))))

||| Completeness of any for actual mapped-list membership; no inverse catalog
||| oracle or reconstructed existential state is needed.
export
0 anyMappedMember : {a, b : Type} -> (f : a -> b) -> (predicate : b -> Bool) ->
  (items : List a) -> (wanted : b) -> (0 member : Elem wanted (map f items)) ->
  (0 accepted : predicate wanted = True) -> any (\item => predicate (f item)) items = True
anyMappedMember f predicate [] wanted member accepted = absurd member
anyMappedMember f predicate (head :: items) wanted member accepted =
  anyMappedCons f predicate head items wanted
    (\later => anyMappedMember f predicate items wanted later accepted) member accepted

||| Positive reflection of LTE into the exact Ord Nat Boolean. One proof
||| elimination per recursive call, not simultaneous two-head Nat matching.
export
0 lteToLeTrue : {n, m : Nat} -> LTE n m -> (n <= m) = True
lteToLeTrue {m} LTEZero = leZero m
lteToLeTrue (LTESucc earlier) = lteToLeTrue earlier
