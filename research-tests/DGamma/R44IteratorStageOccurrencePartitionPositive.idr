module DGamma.R44IteratorStageOccurrencePartitionPositive

import Decidable.Equality
import DGamma.Core
import DGamma.Coeffects
import DGamma.Unified
import DGamma.Calculus
import DGamma.Metatheory

%default total

||| Exact two-way view of an occurrence in a cons trace. There is no third
||| constructible stage-occurrence configuration: the selected transition is
||| either the head itself or occurs in the indexed tail.
data ConsStageOccurrenceView :
  {selectedBefore, selectedAfter, first, middle, last :
    SystemState name key value world error} ->
  {selected : Transition selectedBefore selectedAfter} ->
  {head : Transition first middle} ->
  {tail : Transitions middle last} ->
  (occurs : OccursIn selected (MoreTransitions head tail)) -> Type where
  ConsStageOccursHere : ConsStageOccurrenceView OccursHere
  ConsStageOccursLater :
    (head : Transition first middle) ->
    (later : OccursIn selected tail) ->
    ConsStageOccurrenceView {head} {tail}
      (OccursLater {transition = head} later)

0 viewConsStageOccurrence :
  (occurs : OccursIn selected (MoreTransitions head tail)) ->
  ConsStageOccurrenceView occurs
viewConsStageOccurrence OccursHere = ConsStageOccursHere
viewConsStageOccurrence {head} (OccursLater later) =
  ConsStageOccursLater head later

||| Matching the stage once and eliminating its occurrence in a nested case is
||| accepted as total. This pins the representation needed by cure (b): the
||| generator wrapper must not enumerate nested stage/occurrence patterns in its
||| own left-hand sides.
||| Full stage-indexed package for cure (b). The stored stage and its exact
||| occurrence view are introduced by one StageFromAdvance elimination.
data LocatedConsIteratorStageProbe :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, last : SystemState name key value world error} ->
  (head : Transition first middle) ->
  (tail : Transitions middle last) ->
  (actor : name) ->
  IteratorStage name key world error value actor
    (MoreTransitions head tail) -> Type where
  MkLocatedConsIteratorStageProbe :
    (before, afterState : SystemState name key value world error) ->
    (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
    (tag : RuleTag) ->
    (equation : checkedApplyAction @{nameEq} @{keyEq} (LAdvance actor) before =
      Just (tag, afterState)) ->
    (0 occurs : OccursIn
      (Fired {before} {afterState} nameEq keyEq (LAdvance actor) tag equation)
      (MoreTransitions head tail)) ->
    (0 occurrenceView : ConsStageOccurrenceView occurs) ->
    (fiber : Fiber name key value world error) ->
    (found : lookupFiber @{nameEq} actor (registry before) = Just fiber) ->
    (remaining : List (StepEffect key value world error
      (dependencies (componentDependencies (fiberComponent fiber)))
      (componentProvisions (fiberComponent fiber)))) ->
    (accumulator : LocalState key value world
        (componentProvisions (fiberComponent fiber)) ->
      LocalState key value world
        (componentProvisions (fiberComponent fiber))) ->
    (view : View name
      (dependencies (componentDependencies (fiberComponent fiber)))) ->
    (lifecycle : fiberLifecycle fiber = Reloading remaining accumulator view) ->
    (step : StepEffect key value world error
      (dependencies (componentDependencies (fiberComponent fiber)))
      (componentProvisions (fiberComponent fiber))) ->
    (rest : List (StepEffect key value world error
      (dependencies (componentDependencies (fiberComponent fiber)))
      (componentProvisions (fiberComponent fiber)))) ->
    (suffix : ReachableSuffix remaining (step :: rest)) ->
    LocatedConsIteratorStageProbe name key world error value head tail actor
      (StageFromAdvance nameEq keyEq actor tag equation occurs fiber found
        remaining accumulator view lifecycle step rest suffix)

0 locateConsIteratorStageProbe :
  (stage : IteratorStage name key world error value actor
    (MoreTransitions head tail)) ->
  LocatedConsIteratorStageProbe name key world error value head tail actor stage
locateConsIteratorStageProbe
  (StageFromAdvance {before} {afterState} nameEq keyEq actor tag equation occurs
    fiber found remaining accumulator view lifecycle step rest suffix) =
      MkLocatedConsIteratorStageProbe before afterState nameEq keyEq actor tag
        equation occurs (viewConsStageOccurrence occurs) fiber found remaining
        accumulator view lifecycle step rest suffix

||| Exact generator-indexed wrapper. Forward and yielded generators retain the
||| original whole generator while consuming the stage package once.
data LocatedConsGeneratorProbe :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, last : SystemState name key value world error} ->
  (head : Transition first middle) ->
  (tail : Transitions middle last) ->
  (actor : name) ->
  TraceEffectGenerator name key world error value actor
    (MoreTransitions head tail) -> Type where
  LocatedActualGeneratorProbe :
    (before, afterState : SystemState name key value world error) ->
    (nameEq : DecEq name) -> (keyEq : DecEq key) ->
    (action : Action name key value world error) -> (tag : RuleTag) ->
    (equation : checkedApplyAction @{nameEq} @{keyEq} action before =
      Just (tag, afterState)) ->
    (0 occurs : OccursIn
      (Fired {before} {afterState} nameEq keyEq action tag equation)
      (MoreTransitions head tail)) ->
    (0 owned : actionOwner action = actor) ->
    LocatedConsGeneratorProbe name key world error value head tail actor
      (ActualForwardGenerator before afterState nameEq keyEq action tag equation
        occurs owned)
  LocatedForwardGeneratorProbe :
    (stage : IteratorStage name key world error value actor
      (MoreTransitions head tail)) ->
    (0 located : LocatedConsIteratorStageProbe name key world error value
      head tail actor stage) ->
    LocatedConsGeneratorProbe name key world error value head tail actor
      (IteratorForwardGenerator stage)
  LocatedYieldedGeneratorProbe :
    (stage : IteratorStage name key world error value actor
      (MoreTransitions head tail)) ->
    (origin : EffectState name key value world) ->
    (0 located : LocatedConsIteratorStageProbe name key world error value
      head tail actor stage) ->
    LocatedConsGeneratorProbe name key world error value head tail actor
      (IteratorYieldedGenerator stage origin)

0 locateConsGeneratorProbe :
  (generator : TraceEffectGenerator name key world error value actor
    (MoreTransitions head tail)) ->
  LocatedConsGeneratorProbe name key world error value head tail actor generator
locateConsGeneratorProbe
  (ActualForwardGenerator before afterState nameEq keyEq action tag equation
    occurs owned) =
      LocatedActualGeneratorProbe before afterState nameEq keyEq action tag
        equation occurs owned
locateConsGeneratorProbe (IteratorForwardGenerator stage) =
  LocatedForwardGeneratorProbe stage (locateConsIteratorStageProbe stage)
locateConsGeneratorProbe (IteratorYieldedGenerator stage origin) =
  LocatedYieldedGeneratorProbe stage origin (locateConsIteratorStageProbe stage)
