module DGamma.L2R12SelectedAdjacency

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.Num
import Prelude.EqOrd
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6Anchors
import DGamma.L2R7CatalogBirth
import DGamma.L2R10MoveCutObservation
import DGamma.L2R11LocatedCut
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Zero physical position cannot have a positive saturating distance,
||| regardless of the observed anchor guard and the computed target.
export
0 zeroDistanceAtGuard : (seen : Bool) -> (target : Nat) ->
  (the Nat (if seen then minus Z target else Z)) = Z
zeroDistanceAtGuard False target = Refl
zeroDistanceAtGuard True target = Refl

||| Native distance at physical cut zero, independent of anchor availability.
export
0 rootDistanceAtZero : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (seen : Bool) -> (0 equation : isJust (anchorOf nameEq keyEq trail 0) = seen) ->
  rootDistance nameEq keyEq trail 0 = 0
rootDistanceAtZero nameEq keyEq trail False equation = rewrite equation in Refl
rootDistanceAtZero nameEq keyEq trail True equation = rewrite equation in Refl

||| A genuinely selected positive-distance root cannot occur at cut zero.
||| The library anchor Bool is observed at this call site with its equation.
export
0 selectedBirthNotZero : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (cut : SelectedSquareCut name key world error value nameEq keyEq trail) ->
  catalogOrdinal (cutEntry cut) = 0 -> Void
selectedBirthNotZero nameEq keyEq trail cut equation =
  SIsNotZ {x = positivePredecessor cut}
    (trans (sym (selectedDistanceEquation cut))
      (trans (cong (rootDistance nameEq keyEq trail) equation)
        (rootDistanceAtZero nameEq keyEq trail (isJust (anchorOf nameEq keyEq trail 0)) Refl)))

||| Exact successor/predecessor cancellation, with zero explicitly excluded.
export
0 successorPredPositive : (ordinal : Nat) -> (0 positive : ordinal = 0 -> Void) ->
  S (pred ordinal) = ordinal
successorPredPositive Z positive = absurd (positive Refl)
successorPredPositive (S ordinal) positive = Refl
