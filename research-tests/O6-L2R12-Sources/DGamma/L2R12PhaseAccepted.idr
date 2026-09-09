module DGamma.L2R12PhaseAccepted

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R9OrdinalScan
import DGamma.L2R10PhaseScan
import DGamma.L2R7ObservedAny
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Library all is an accumulator fold, dual to the inherited any decoder.
export
0 phaseAllFoldFalse : {a : Type} -> (predicate : a -> Bool) -> (items : List a) ->
  foldl (\acc, item => acc && predicate item) False items = False
phaseAllFoldFalse predicate [] = Refl
phaseAllFoldFalse predicate (head :: items) = phaseAllFoldFalse predicate items

||| The observed accumulator equation for the native all fold.
export
0 phaseAllFoldObserved : {a : Type} -> (predicate : a -> Bool) -> (items : List a) ->
  (seen : Bool) -> foldl (\acc, item => acc && predicate item) seen items =
    (seen && all predicate items)
phaseAllFoldObserved predicate items False = phaseAllFoldFalse predicate items
phaseAllFoldObserved predicate items True = Refl

||| Extract acceptance at any authentic list member from the native fold.
||| Only the membership is eliminated, with accumulator conversion explicit.
export
0 phaseAllMember : {a : Type} -> (predicate : a -> Bool) ->
  {item : a} -> {items : List a} ->
  (0 member : Elem item items) -> (0 accepted : all predicate items = True) ->
  predicate item = True
phaseAllMember predicate {items = head :: rest} Here accepted =
  boolAndLeft (predicate head) (all predicate rest)
    (trans (sym (phaseAllFoldObserved predicate rest (predicate head))) accepted)
phaseAllMember predicate {items = head :: rest} (There later) accepted =
  phaseAllMember predicate later
    (boolAndRight (predicate head) (all predicate rest)
      (trans (sym (phaseAllFoldObserved predicate rest (predicate head))) accepted))

||| Named executable spelling of the ACTUAL phaseScanOk seed predicate.
||| This does not change scanner semantics or assume the seed exists.
public export
phaseAnchorSeedCheck : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (entry : RootCatalogEntry name key world error value) -> (anchor : Nat) ->
  (seed : RootCatalogEntry name key world error value) -> Bool
phaseAnchorSeedCheck nameEq keyEq trail entry anchor seed =
  catalogOrdinal seed <= catalogOrdinal entry &&
  keyForcedOrdinal nameEq keyEq trail (catalogOrdinal seed) &&
  elemDec (pred anchor)
    (filter (\ordinal => ordinal < catalogOrdinal seed)
      (releaseOrdinalScan nameEq keyEq (catalogComponent seed) trail)) &&
  maybe False
    (\event => maybe False
      (\actor => phaseReleaseCheck nameEq actor 0 (pred anchor) False (phaseEvents nameEq trail))
      (fst event))
    (head' (drop (pred anchor) (phaseEvents nameEq trail)))
