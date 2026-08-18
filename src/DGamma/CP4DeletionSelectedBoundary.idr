module DGamma.CP4DeletionSelectedBoundary

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionSelectedEffectCore
import Decidable.Equality

%default total

||| Control agreement needed only for actors whose current generation is not
||| erased and which are not the selected activation itself.  During the closed
||| episode the selected fiber deliberately has different lifecycle control in
||| the original and survivor, while exact R generations may be absent.
public export
SelectedControlsOutside :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  List (RegistrationGeneration name) -> GenerationEnvironment name ->
  SystemState name key value world error ->
  SystemState name key value world error -> Type
SelectedControlsOutside {name} nameEq selected registered live original
  survivor =
    (actor : name) -> Not (actor = selected) ->
    CurrentGenerationOutside {nameEq = nameEq} registered live actor ->
    FiberControlMaybeRelated
      (lookupFiber @{nameEq} actor (registry original))
      (lookupFiber @{nameEq} actor (registry survivor))

||| Combined intermediate boundary for the selected-episode quotient.  It owns
||| the exact current-R deletion plan, Theorem-61 effect recovery, outside
||| controls, generation uniqueness, and both checked-validity facts.  Unlike
||| `NoEpisodeReplayBoundary`, no raw runtime-snapshot equality is claimed:
||| selected effects are related only after applying the live accumulator.
public export
record SelectedEpisodeReplayBoundary
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (registered : List (RegistrationGeneration name))
  (ordinal : Nat) (live : GenerationEnvironment name)
  {wholeFirst, wholeLast : SystemState name key value world error}
  (whole : Transitions wholeFirst wholeLast)
  (original, survivor : SystemState name key value world error) where
  constructor MkSelectedEpisodeReplayBoundary
  0 selectedBoundaryEffects : SelectedEffectReplayBoundary name key world error
    value nameEq keyEq selected whole original survivor
  selectedBoundaryPlan : CompleteCurrentRegisteredPlanResult name key world
    error value nameEq registered live (registry original)
  0 selectedBoundaryControls : SelectedControlsOutside nameEq selected registered
    live original survivor
  0 selectedOriginalWellFormed : registryWellFormed @{nameEq} @{keyEq}
    original = True
  0 selectedSurvivorWellFormed : registryWellFormed @{nameEq} @{keyEq}
    survivor = True

0 openingForeignLookup :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected, actor : name) ->
  Not (actor = selected) ->
  {preStart, start : SystemState name key value world error} ->
  (opening : BeginStep nameEq keyEq selected preStart start) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor (registry start) =
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor (registry preStart)
openingForeignLookup nameEq keyEq selected actor distinct {preStart} {start}
  opening =
    let 0 raw = checkedActionProjects nameEq keyEq (LBegin selected) preStart
          start LBeginTag (beginEquation opening)
        0 update = applyActionLocalUpdate nameEq keyEq (LBegin selected) preStart
          start LBeginTag raw
    in systemLocalUpdateForeign nameEq actor selected distinct preStart start
      update

||| Delete the checked opening and establish the first installed quotient
||| boundary.  The supplied complete plan is normally empty of current R births
||| at this ordinal; keeping it indexed avoids a second special representation.
public export
0 beginSelectedEpisodeReplayBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  {preStart, start : SystemState name key value world error} ->
  (whole : Transitions start wholeLast) ->
  (opening : BeginStep nameEq keyEq selected preStart start) ->
  (plan : CompleteCurrentRegisteredPlanResult name key world error value nameEq
    registered live (registry start)) ->
  registryWellFormed @{nameEq} @{keyEq} preStart = True ->
  SelectedEpisodeReplayBoundary name key world error value nameEq keyEq selected
    registered (S ordinal) live whole start preStart
beginSelectedEpisodeReplayBoundary nameEq keyEq selected registered ordinal live
  {preStart} {start} whole opening plan preWellFormed =
    let 0 raw = checkedActionProjects nameEq keyEq (LBegin selected) preStart
          start LBeginTag (beginEquation opening)
        0 startWellFormed = preservationTheoremProof nameEq keyEq
          (LBegin selected) preStart start LBeginTag preWellFormed raw
        0 controls : SelectedControlsOutside nameEq selected registered live
          start preStart
        controls actor distinct outside =
          let 0 lookupSame = openingForeignLookup nameEq keyEq selected actor
                distinct opening
          in replace
            {p = \observed => FiberControlMaybeRelated observed
              (lookupFiber @{nameEq} actor (registry preStart))}
            (sym lookupSame)
            (fiberControlMaybeReflexive
              (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
                {world = world} {error = error} actor (registry preStart)))
    in MkSelectedEpisodeReplayBoundary
      (beginSelectedEffectReplayBoundary nameEq keyEq selected whole opening)
      plan controls startWellFormed preWellFormed

||| Generic structural half for a selected installed step that is skipped by
||| the quotient.  The caller supplies the already-proved effect step and the
||| complete plan transported through the selected registry replacement; this
||| lemma proves that all foreign controls and checked-validity facts persist.
public export
0 skippedSelectedStepPreservesEpisodeBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (survivor : SystemState name key value world error) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  actionOwner action = selected ->
  (nextEffects : SelectedEffectReplayBoundary name key world error value nameEq
    keyEq selected whole afterState survivor) ->
  (nextPlan : CompleteCurrentRegisteredPlanResult name key world error value
    nameEq registered live (registry afterState)) ->
  SelectedEpisodeReplayBoundary name key world error value nameEq keyEq selected
    registered (S ordinal) live whole afterState survivor
skippedSelectedStepPreservesEpisodeBoundary nameEq keyEq selected registered
  ordinal live action tag before afterState checked whole survivor
  (MkSelectedEpisodeReplayBoundary oldEffects oldPlan oldControls
    beforeWellFormed survivorWellFormed)
  owner nextEffects nextPlan =
    let 0 raw = checkedActionProjects nameEq keyEq action before afterState tag
          checked
        0 update = applyActionLocalUpdate nameEq keyEq action before afterState
          tag raw
        0 afterWellFormed = preservationTheoremProof nameEq keyEq action before
          afterState tag beforeWellFormed raw
        0 controls : SelectedControlsOutside nameEq selected registered live
          afterState survivor
        controls actor actorDistinct outside =
          let 0 actorDistinctOwner : Not (actor = actionOwner action)
              actorDistinctOwner same = actorDistinct (trans same owner)
              0 lookupSame : lookupFiber @{nameEq} {name = name} {key = key}
                    {value = value} {world = world} {error = error} actor
                    (registry afterState) =
                  lookupFiber @{nameEq} {name = name} {key = key}
                    {value = value} {world = world} {error = error} actor
                    (registry before)
              lookupSame = systemLocalUpdateForeign nameEq actor
                (actionOwner action) actorDistinctOwner before afterState update
          in replace
            {p = \observed => FiberControlMaybeRelated observed
              (lookupFiber @{nameEq} actor (registry survivor))}
            (sym lookupSame) (oldControls actor actorDistinct outside)
    in MkSelectedEpisodeReplayBoundary nextEffects nextPlan controls
      afterWellFormed survivorWellFormed
