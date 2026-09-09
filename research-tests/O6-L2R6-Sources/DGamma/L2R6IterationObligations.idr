module DGamma.L2R6IterationObligations

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R5Extensional
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R6FrontNormal
import DGamma.L2R6Iteration
import DGamma.L2R6Phase
import Control.WellFounded
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Exact result TYPE for phase-scoped distance iteration: actual checked
||| output trail, finite admitted iteration, zero distance, extensional end,
||| front/no-forced-control and genuine core-release phase invariants. No
||| general producer, terminal-earliest, placed-gap NF or selector theorem is
||| supplied by this record. In particular distance zero is not renamed NF.
public export
record PhaseIterationResult
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, oldFinal : SystemState name key value world error}
  {oldTrace : Transitions initial oldFinal}
  (oldTrail : AvailabilityTrace name key world error value oldTrace) where
  constructor MkPhaseIterationResult
  iterationFinal : SystemState name key value world error
  iterationTrace : Transitions initial iterationFinal
  iterationTrail : AvailabilityTrace name key world error value iterationTrace
  0 finiteIteration : DistanceIteration nameEq keyEq oldTrail iterationTrail
  0 iterationDistanceZero : totalDistance nameEq keyEq iterationTrail = 0
  0 extensionalIterationEnd : RegistryExtensional name key world error value nameEq oldFinal iterationFinal
  0 iterationFront : FrontNormal name key world error value nameEq keyEq iterationTrail
  0 iterationNeverRetired : ForcedRootNeverRetired name key world error value nameEq keyEq iterationTrail
  0 iterationPhases : (entry : RootCatalogEntry name key world error value) ->
    Elem entry (scanRootCatalog 0 iterationTrail) -> ForcedOnTrace nameEq keyEq iterationTrail (catalogOrdinal entry) ->
    ForcedRootPhase name key world error value nameEq keyEq iterationTrail entry
