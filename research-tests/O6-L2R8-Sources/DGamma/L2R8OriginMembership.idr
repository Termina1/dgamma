module DGamma.L2R8OriginMembership

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6Anchors
import DGamma.L2R6FrontNormal
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Maximum chooses an authentic member. The library comparison Bool is
||| observed by its OWN equation at the caller, not re-cased internally.
export
0 maxMemberObserved : (universe : List Nat) -> (left, right : Nat) ->
  (0 leftMember : Elem left universe) -> (0 rightMember : Elem right universe) ->
  (seen : Bool) -> (0 equation : (left > right) = seen) -> Elem (max left right) universe
maxMemberObserved universe left right leftMember rightMember True equation = rewrite equation in leftMember
maxMemberObserved universe left right leftMember rightMember False equation = rewrite equation in rightMember

||| General authentic membership of a left-fold maximum. Membership of the
||| input accumulator and scan items is transported structurally, not assumed
||| for the computed maximum. Every comparison observes its call-site result.
export
0 foldMaximumMember : (universe, items : List Nat) -> (accumulator : Nat) ->
  (0 initialMember : Elem accumulator universe) ->
  (0 inclusion : (item : Nat) -> Elem item items -> Elem item universe) ->
  Elem (foldl max accumulator items) universe
foldMaximumMember universe [] accumulator initialMember inclusion = initialMember
foldMaximumMember universe (head :: items) accumulator initialMember inclusion =
  foldMaximumMember universe items (max accumulator head)
    (maxMemberObserved universe accumulator head initialMember (inclusion head Here) (accumulator > head) Refl)
    (\item, present => inclusion item (There present))

||| Decode the exact lastReleaseCut/pred origin computation into membership
||| of its input ordinals. This is an observed result, not a repeated case of
||| the library maximum. Root identity and native birth decoding are separate.
export
0 originMaximumMember : (items : List Nat) -> (observed : Maybe Nat) ->
  (0 equation : map pred (lastReleaseCut items) = observed) -> (ordinal : Nat) ->
  (0 accepted : observed = Just ordinal) -> Elem ordinal items
originMaximumMember [] observed equation ordinal accepted = absurd (trans equation accepted)
originMaximumMember (head :: items) observed equation ordinal accepted =
  replace {p = \n => Elem n (head :: items)}
    (cong (fromMaybe 0) (trans equation accepted))
    (foldMaximumMember (head :: items) items head Here (\item, present => There present))

||| GENERAL rootOriginAt observation -> membership of its exact filtered
||| catalog-ordinal list. No raw-name birth oracle or supplied membership.
||| Inverting map/filter into a matching catalog ENTRY and applying
||| scanCatalogBirth, and the reverse/maximality direction, remain open.
export
0 rootOriginCatalogOrdinal : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) -> (cut : Nat) ->
  (catalog : List (RootCatalogEntry name key world error value)) ->
  (observed : Maybe Nat) -> (0 equation : rootOriginAt nameEq actor cut catalog = observed) ->
  (ordinal : Nat) -> (0 accepted : observed = Just ordinal) ->
  Elem ordinal (map catalogOrdinal (filter (\entry => catalogOrdinal entry <= cut &&
    isYes (decEq @{nameEq} actor (catalogRoot entry))) catalog))
rootOriginCatalogOrdinal nameEq actor cut catalog observed equation ordinal accepted =
  originMaximumMember (map catalogOrdinal (filter (\entry => catalogOrdinal entry <= cut &&
    isYes (decEq @{nameEq} actor (catalogRoot entry))) catalog)) observed equation ordinal accepted

||| Executable origin observation, tied to the ORIGINAL computed catalog.
||| Its conditional proof is ordinal membership, NOT yet a native birth and
||| root-identity/maximality decoder or the full rootOriginAt equivalence.
public export
record OriginObservation
  (name, key, world, error : Type) (value : key -> Type) (nameEq : DecEq name)
  {0 first, finalState : SystemState name key value world error}
  {0 trace : Transitions first finalState}
  (trail : AvailabilityTrace name key world error value trace) (actor : name) (cut : Nat) where
  constructor MkOriginObservation
  originObserved : Maybe Nat
  0 originEquation : rootOriginAt nameEq actor cut (scanRootCatalog 0 trail) = originObserved
  0 originOrdinalMember : (ordinal : Nat) -> originObserved = Just ordinal ->
    Elem ordinal (map catalogOrdinal (filter (\entry => catalogOrdinal entry <= cut &&
      isYes (decEq @{nameEq} actor (catalogRoot entry))) (scanRootCatalog 0 trail)))
