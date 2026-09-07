module DGamma.CP5GeneratedOrchestrationMatched

import DGamma.Calculus
import DGamma.CP3
import Decidable.Equality
import Data.Nat

%default total
%unbound_implicits off

||| False is retirement, True is removal. Births are already covered by the
||| accepted RegistrationTraceCorrespondence, not by this A9 operation code.
public export
generatedOrchestrationAction :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  Bool -> name -> Action name key value world error
generatedOrchestrationAction name key world error value False actor = ORetire actor
generatedOrchestrationAction name key world error value True actor = ORemove actor

||| One ACTUAL non-root retirement/removal, at the generation current immediately
||| before that exact occurrence. The empty-origin prefix scan forbids choosing
||| a detached historical birth merely because its raw name agrees.
public export
record LocatedGeneratedOrchestration
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name)
  {0 initial, finalState : SystemState name key value world error}
  (0 trace : Transitions initial finalState) where
  constructor MkLocatedGeneratedOrchestration
  0 generatedActor : name
  0 generatedRemoval : Bool
  0 generatedOccurrence : LocatedActionOccurrence
    (generatedOrchestrationAction name key world error value generatedRemoval generatedActor) trace
  0 generatedFiber : Fiber name key value world error
  0 generatedParent : name
  0 generatedFound :
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} generatedActor (registry (actionBeforeState generatedOccurrence)) = Just generatedFiber)
  0 generatedParentExact : (fiberParent generatedFiber = ChildOf generatedParent)
  0 generatedScanOrdinal : Nat
  0 generatedLive : GenerationEnvironment name
  0 generatedScan : GenerationTraceScan nameEq 0 []
    (beforeActionOccurrence generatedOccurrence) generatedScanOrdinal generatedLive
  0 generatedCurrent : RegistrationGeneration name
  0 generatedCurrentExact :
    (lookupCurrentGeneration @{nameEq} generatedActor generatedLive = Just generatedCurrent)

||| R178 A9: extra research hypothesis, NOT a frozen CP3 strengthening.
||| Both occurrence domains are covered; inverse laws compare positions, not
||| dependent proof tokens. Strict order preserves multiplicity and relative
||| order even for repeated idempotent retirements of one generation.
public export
record GeneratedOrchestrationMatched
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name)
  {0 initial, leftFinal, rightFinal : SystemState name key value world error}
  (0 leftTrace : Transitions initial leftFinal)
  (0 rightTrace : Transitions initial rightFinal)
  (renaming : RegistrationGenerationBijection name) where
  constructor MkGeneratedOrchestrationMatched
  0 generatedForward :
    LocatedGeneratedOrchestration name key world error value nameEq leftTrace ->
    LocatedGeneratedOrchestration name key world error value nameEq rightTrace
  0 generatedBackward :
    LocatedGeneratedOrchestration name key world error value nameEq rightTrace ->
    LocatedGeneratedOrchestration name key world error value nameEq leftTrace
  0 generatedForwardKind :
    (occurrence : LocatedGeneratedOrchestration name key world error value nameEq leftTrace) ->
    (generatedRemoval (generatedForward occurrence) = generatedRemoval occurrence)
  0 generatedForwardGeneration :
    (occurrence : LocatedGeneratedOrchestration name key world error value nameEq leftTrace) ->
    (generationForward renaming (generatedCurrent occurrence) = generatedCurrent (generatedForward occurrence))
  0 generatedBackwardKind :
    (occurrence : LocatedGeneratedOrchestration name key world error value nameEq rightTrace) ->
    (generatedRemoval (generatedBackward occurrence) = generatedRemoval occurrence)
  0 generatedBackwardGeneration :
    (occurrence : LocatedGeneratedOrchestration name key world error value nameEq rightTrace) ->
    (generationBackward renaming (generatedCurrent occurrence) = generatedCurrent (generatedBackward occurrence))
  0 generatedLeftInverse :
    (occurrence : LocatedGeneratedOrchestration name key world error value nameEq leftTrace) ->
    (locatedActionOrdinal (generatedOccurrence (generatedBackward (generatedForward occurrence))) =
      locatedActionOrdinal (generatedOccurrence occurrence))
  0 generatedRightInverse :
    (occurrence : LocatedGeneratedOrchestration name key world error value nameEq rightTrace) ->
    (locatedActionOrdinal (generatedOccurrence (generatedForward (generatedBackward occurrence))) =
      locatedActionOrdinal (generatedOccurrence occurrence))
  0 generatedOrderPreserved :
    (earlier, later : LocatedGeneratedOrchestration name key world error value nameEq leftTrace) ->
    (LT (locatedActionOrdinal (generatedOccurrence earlier)) (locatedActionOrdinal (generatedOccurrence later))) ->
    (LT (locatedActionOrdinal (generatedOccurrence (generatedForward earlier)))
      (locatedActionOrdinal (generatedOccurrence (generatedForward later))))
  0 generatedOrderReflected :
    (earlier, later : LocatedGeneratedOrchestration name key world error value nameEq rightTrace) ->
    (LT (locatedActionOrdinal (generatedOccurrence earlier)) (locatedActionOrdinal (generatedOccurrence later))) ->
    (LT (locatedActionOrdinal (generatedOccurrence (generatedBackward earlier)))
      (locatedActionOrdinal (generatedOccurrence (generatedBackward later))))
