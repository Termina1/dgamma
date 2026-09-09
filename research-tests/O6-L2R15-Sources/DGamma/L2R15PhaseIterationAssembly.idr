module DGamma.L2R15PhaseIterationAssembly

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R5Extensional
import DGamma.L2R5ExtensionalRetire
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R6FrontNormal
import DGamma.L2R6Phase
import DGamma.L2R6Iteration
import DGamma.L2R6IterationObligations
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| General ZERO-distance base case of the existing PhaseIterationResult.
||| Front/NeverRetired/phase invariants are explicit, not inferred from zero.
||| No move existence or general normalization theorem is claimed.
export
0 phaseIterationAtZero : {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, finalState : SystemState name key value world error} ->
  {trace : Transitions initial finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (0 zero : totalDistance nameEq keyEq trail = 0) ->
  (0 front : FrontNormal name key world error value nameEq keyEq trail) ->
  (0 never : ForcedRootNeverRetired name key world error value nameEq keyEq trail) ->
  (0 phases : (entry : RootCatalogEntry name key world error value) ->
    Elem entry (scanRootCatalog 0 trail) -> ForcedOnTrace nameEq keyEq trail (catalogOrdinal entry) ->
    ForcedRootPhase name key world error value nameEq keyEq trail entry) ->
  PhaseIterationResult name key world error value nameEq keyEq trail
phaseIterationAtZero {finalState} {trace} nameEq keyEq trail zero front never phases =
  MkPhaseIterationResult finalState trace trail (IterationDone trail) zero
    (MkRegistryExtensional Refl (\wanted => Refl)) front never phases
