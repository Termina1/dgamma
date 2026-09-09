module DGamma.L2R6FrontNormal

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3Attached
import DGamma.L2R3AttachedGap
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Latest matching birth occurrence at/before the action cut. None denotes
||| an initially installed root. Raw-name reuse does not select the first
||| birth. General agreement with the accepted generation scanner is OPEN.
public export
rootOriginAt : {name, key, world, error : Type} -> {value : key -> Type} ->
  DecEq name -> name -> Nat -> List (RootCatalogEntry name key world error value) -> Maybe Nat
rootOriginAt nameEq actor cut catalog = map pred (lastReleaseCut
  (map catalogOrdinal (filter (\entry => catalogOrdinal entry <= cut &&
    isYes (decEq @{nameEq} actor (catalogRoot entry))) catalog)))

||| Test whether the observed birth origin has an assigned release anchor.
||| Initially installed roots have no in-trace forced origin. Equivalence
||| with the independent inductive ForcedOnTrace classifier remains owed.
public export
originForced : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  DecEq name -> DecEq key -> AvailabilityTrace name key world error value trace -> Maybe Nat -> Bool
originForced nameEq keyEq trail Nothing = False
originForced nameEq keyEq trail (Just ordinal) = isJust (anchorOf nameEq keyEq trail ordinal)
