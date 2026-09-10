module DGamma.L2R12PhaseContract

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
import DGamma.L2R6Phase
import DGamma.L2R9OrdinalScan
import DGamma.L2R10PhaseScan
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| NEW per-root producer obligation with the exhausted whole-trail bounded
||| agreement made an EXPLICIT observed premise, not retried or postulated.
||| This is a TYPE, not its inhabitant. The requested phase and located birth
||| still have to be constructed from scanner acceptance in later connectors.
public export
ForcedRootPhaseFromObservedAgreement :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace) ->
  (entry : RootCatalogEntry name key world error value) -> Type
ForcedRootPhaseFromObservedAgreement {name} {key} {world} {error} {value}
  nameEq keyEq trail entry =
  (0 member : Elem entry (scanRootCatalog 0 trail)) ->
  (0 accepted : phaseScanOk nameEq keyEq trail = True) ->
  (0 classified : any (\seed => catalogOrdinal seed <= catalogOrdinal entry &&
    keyForcedOrdinal nameEq keyEq trail (catalogOrdinal seed)) (scanRootCatalog 0 trail) = True) ->
  (0 agreement : (seed : RootCatalogEntry name key world error value) ->
    Elem seed (scanRootCatalog 0 trail) ->
    (observed : List Nat) ->
    filter (\ordinal => ordinal < catalogOrdinal seed)
      (releaseOrdinalScan nameEq keyEq (catalogComponent seed) trail) = observed ->
    scanReleaseOrdinals nameEq keyEq (catalogComponent seed) 0 (catalogOrdinal seed) trail = observed) ->
  ForcedRootPhase name key world error value nameEq keyEq trail entry
