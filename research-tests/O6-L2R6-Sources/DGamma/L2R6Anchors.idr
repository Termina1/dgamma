module DGamma.L2R6Anchors

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3Attached
import DGamma.L2R3AttachedGap
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Observed maximum removal-ending cut; Nothing means no release. Ordinals
||| remain current-trace positions, NOT stable identities across a swap.
public export
lastReleaseCut : List Nat -> Maybe Nat
lastReleaseCut [] = Nothing
lastReleaseCut (ordinal :: later) = Just (S (foldl max ordinal later))

||| Maximum of actual key-release scans for catalog roots at or before this
||| root in orchestration order. An unseeded barrier inherits earlier releases;
||| a later key release raises the anchor. Non-forced prefixes return Nothing.
public export
anchorOf : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  DecEq name -> DecEq key -> AvailabilityTrace name key world error value trace -> Nat -> Maybe Nat
anchorOf nameEq keyEq trail ordinal = lastReleaseCut (concatMap
  (\entry => scanReleaseOrdinals nameEq keyEq (catalogComponent entry) 0 (catalogOrdinal entry) trail)
  (filter (\entry => catalogOrdinal entry <= ordinal) (scanRootCatalog 0 trail)))
