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
