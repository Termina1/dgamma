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

||| General STEP assembly for the existing result record. Consumes an ACTUAL
||| admitted move and an already-produced terminal result; its endpoint is
||| composed extensionally and final invariants remain literally shared.
||| This does not supply GeneralAdmittedMoveExistenceUnique or a recursive
||| result by fiat, and is NOT named normalizePhaseDistance.
export
0 phaseIterationPrepend : {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, oldFinal, middleFinal : SystemState name key value world error} ->
  {oldTrace : Transitions initial oldFinal} -> {middleTrace : Transitions initial middleFinal} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (oldTrail : AvailabilityTrace name key world error value oldTrace) ->
  (middleTrail : AvailabilityTrace name key world error value middleTrace) ->
  (0 move : AdmittedDistanceMove name key world error value nameEq keyEq oldTrail middleTrail) ->
  (result : PhaseIterationResult name key world error value nameEq keyEq middleTrail) ->
  PhaseIterationResult name key world error value nameEq keyEq oldTrail
phaseIterationPrepend nameEq keyEq oldTrail middleTrail move result =
  MkPhaseIterationResult (iterationFinal result) (iterationTrace result) (iterationTrail result)
    (IterationMove move (finiteIteration result)) (iterationDistanceZero result)
    (extensionalTransitive (moveEndpoints move) (extensionalIterationEnd result))
    (iterationFront result) (iterationNeverRetired result) (iterationPhases result)
