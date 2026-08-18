module DGamma.CP4ProgressNoDeadlock

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressFinite
import DGamma.CP4ProgressReliance
import Control.WellFounded
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

||| Raw preservation turns a successful rule at a well-formed source into a
||| transition admitted by the checked evaluator.
public export
0 checkedFromRaw :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  registryWellFormed @{nameEq} @{keyEq} before = True ->
  applyAction @{nameEq} @{keyEq} {value = value} {world = world} {error = error} action before = Just (tag, afterState) ->
  checkedApplyAction @{nameEq} @{keyEq} {value = value} {world = world} {error = error} action before =
    Just (tag, afterState)
checkedFromRaw {name = name} {key = key} {value = value}
        {world = world} {error = error} nameEq keyEq action before afterState tag valid raw =
  rewrite raw in
  rewrite preservationTheoremProof nameEq keyEq action before afterState tag
    valid raw in Refl

0 selectedFiberViewValid :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) ->
  (fibers : Registry name key value world error) ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} selected fibers = Just fiber ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error}
    (MkSystemState ambient fibers) = True ->
  fiberViewInvariant @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} fiber fibers = True
selectedFiberViewValid nameEq keyEq ambient
  fibers@(MkCoeffectContext entries unique) selected fiber found wellFormed =
    viewsInvariantLookup nameEq keyEq selected fiber entries fibers
      (lookupFiberEntries nameEq selected fiber fibers found)
      (wellFormedViewsInvariant nameEq keyEq ambient fibers wellFormed)

public export
0 RawActionResult :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  Action name key value world error ->
  SystemState name key value world error -> Type
RawActionResult name key world error value nameEq keyEq action before =
  (tag : RuleTag **
    (afterState : SystemState name key value world error **
      applyAction @{nameEq} @{keyEq} {value = value} {world = world} {error = error} action before = Just (tag, afterState)))

0 reloadingAdvanceResolvedRaw :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (actor : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (rest : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (capability : DepValues key value
    (dependencies (componentDependencies component))) ->
  resolveCommittedValues @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} (dependencies (componentDependencies component)) view
    fibers = Just capability ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} actor fibers = Just
    (MkFiber component parent retiredFlag table
      (Reloading (step :: rest) accumulator view)) ->
  RawActionResult name key world error value nameEq keyEq (LAdvance actor)
    (MkSystemState ambient fibers)
reloadingAdvanceResolvedRaw nameEq keyEq ambient fibers actor component parent
  retiredFlag table step rest accumulator view capability resolved found
  with (runStepEffect step capability
    (MkLocalState ambient
      (restrictOwnedPreservingOrder (componentProvisions component)
        (ownedValues table)))) proof ran
  reloadingAdvanceResolvedRaw nameEq keyEq ambient fibers actor component parent
    retiredFlag table step rest accumulator view capability resolved found |
    Left err =
      let afterState : SystemState name key value world error
          afterState = MkSystemState ambient
            (replaceBinding @{nameEq} actor
              (setFiberLifecycle
                (MkFiber component parent retiredFlag table
                  (Reloading (step :: rest) accumulator view))
                (Unloading accumulator view (Just err))) fibers)
          0 raw : (applyAction @{nameEq} @{keyEq} {value = value}
            {world = world} {error = error} (LAdvance actor)
            (MkSystemState ambient fibers) = Just (LRaiseTag, afterState))
          raw = rewrite found in rewrite resolved in rewrite ran in Refl
      in (LRaiseTag ** (afterState ** raw))
  reloadingAdvanceResolvedRaw nameEq keyEq ambient fibers actor component parent
    retiredFlag table step rest accumulator view capability resolved found |
    Right (localAfter, undo)
    with (targetMatches @{nameEq}
      (targetFiber @{nameEq} @{keyEq} {value = value} {world = world}
        {error = error}
        (MkFiber component parent retiredFlag table
          (Reloading (step :: rest) accumulator view)) fibers) view) proof matches
    reloadingAdvanceResolvedRaw nameEq keyEq ambient fibers actor component parent
      retiredFlag table step rest accumulator view capability resolved found |
      Right (localAfter, undo) | False =
        let afterState : SystemState name key value world error
            afterState = MkSystemState (localWorld localAfter)
              (replaceBinding @{nameEq} actor
                (setFiberRuntime
                  (MkFiber component parent retiredFlag table
                    (Reloading (step :: rest) accumulator view))
                  (localTable localAfter)
                  (Unloading (pushLocalUndo (componentProvisions component) accumulator undo) view Nothing)) fibers)
            0 raw : (applyAction @{nameEq} @{keyEq} {value = value}
              {world = world} {error = error} (LAdvance actor)
              (MkSystemState ambient fibers) = Just (LDivertTag, afterState))
            raw = rewrite found in rewrite resolved in rewrite ran in
              rewrite matches in Refl
        in (LDivertTag ** (afterState ** raw))
    reloadingAdvanceResolvedRaw nameEq keyEq ambient fibers actor component parent
      retiredFlag table step [] accumulator view capability resolved found |
      Right (localAfter, undo) | True =
        let afterState : SystemState name key value world error
            afterState = MkSystemState (localWorld localAfter)
              (replaceBinding @{nameEq} actor
                (setFiberRuntime
                  (MkFiber component parent retiredFlag table
                    (Reloading [step] accumulator view))
                  (localTable localAfter)
                  (Active (pushLocalUndo (componentProvisions component) accumulator undo) view)) fibers)
            0 raw : (applyAction @{nameEq} @{keyEq} {value = value}
              {world = world} {error = error} (LAdvance actor)
              (MkSystemState ambient fibers) = Just (LFinishTag, afterState))
            raw = rewrite found in rewrite resolved in rewrite ran in
              rewrite matches in Refl
        in (LFinishTag ** (afterState ** raw))
    reloadingAdvanceResolvedRaw nameEq keyEq ambient fibers actor component parent
      retiredFlag table step (next :: more) accumulator view capability resolved
      found | Right (localAfter, undo) | True =
        let afterState : SystemState name key value world error
            afterState = MkSystemState (localWorld localAfter)
              (replaceBinding @{nameEq} actor
                (setFiberRuntime
                  (MkFiber component parent retiredFlag table
                    (Reloading (step :: next :: more) accumulator view))
                  (localTable localAfter)
                  (Reloading (next :: more) (pushLocalUndo (componentProvisions component) accumulator undo) view)) fibers)
            0 raw : (applyAction @{nameEq} @{keyEq} {value = value}
              {world = world} {error = error} (LAdvance actor)
              (MkSystemState ambient fibers) = Just (LIterTag, afterState))
            raw = rewrite found in rewrite resolved in rewrite ran in
              rewrite matches in Refl
        in (LIterTag ** (afterState ** raw))

0 reloadingAdvanceRaw :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (actor : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} actor fibers = Just
    (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator view)) ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error}
    (MkSystemState ambient fibers) = True ->
  RawActionResult name key world error value nameEq keyEq (LAdvance actor)
    (MkSystemState ambient fibers)
reloadingAdvanceRaw nameEq keyEq ambient fibers actor component parent
  retiredFlag table [] accumulator view found wellFormed
  with (targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
      (MkFiber component parent retiredFlag table
        (Reloading [] accumulator view)) fibers) view) proof matches
  reloadingAdvanceRaw nameEq keyEq ambient fibers actor component parent
    retiredFlag table [] accumulator view found wellFormed | True =
      let afterState : SystemState name key value world error
          afterState = MkSystemState ambient
            (replaceBinding @{nameEq} actor
              (setFiberLifecycle
                (MkFiber component parent retiredFlag table
                  (Reloading [] accumulator view))
                (Active accumulator view)) fibers)
          0 raw : (applyAction @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (LAdvance actor)
            (MkSystemState ambient fibers) = Just (LFinishTag, afterState))
          raw = rewrite found in rewrite matches in Refl
      in (LFinishTag ** (afterState ** raw))
  reloadingAdvanceRaw nameEq keyEq ambient fibers actor component parent
    retiredFlag table [] accumulator view found wellFormed | False =
      let afterState : SystemState name key value world error
          afterState = MkSystemState ambient
            (replaceBinding @{nameEq} actor
              (setFiberLifecycle
                (MkFiber component parent retiredFlag table
                  (Reloading [] accumulator view))
                (Unloading accumulator view Nothing)) fibers)
          0 raw : (applyAction @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (LAdvance actor)
            (MkSystemState ambient fibers) = Just (LDivertTag, afterState))
          raw = rewrite found in rewrite matches in Refl
      in (LDivertTag ** (afterState ** raw))
reloadingAdvanceRaw nameEq keyEq ambient fibers actor component parent
  retiredFlag table (step :: rest) accumulator view found wellFormed =
    let 0 selectedValid : (fiberViewInvariant @{nameEq} @{keyEq}
          {value = value} {world = world} {error = error}
          (MkFiber component parent retiredFlag table
            (Reloading (step :: rest) accumulator view)) fibers = True)
        selectedValid = selectedFiberViewValid nameEq keyEq ambient fibers actor
          (MkFiber component parent retiredFlag table
            (Reloading (step :: rest) accumulator view)) found wellFormed
        0 bindingsValid : (viewBindingsInvariant @{nameEq} @{keyEq}
          {value = value} {world = world} {error = error}
          (dependencies (componentDependencies component)) view fibers = True)
        bindingsValid = committedViewBindingsValid nameEq keyEq
          (MkFiber component parent retiredFlag table
            (Reloading (step :: rest) accumulator view)) fibers view
          selectedValid Refl
        0 capabilityIsJust :
          (isJust (resolveCommittedValues @{nameEq} @{keyEq} {value = value}
            {world = world} {error = error}
            (dependencies (componentDependencies component)) view fibers) = True)
        capabilityIsJust = boolAndRight _ _ bindingsValid
        0 capabilityWitness :
          (capability : DepValues key value
            (dependencies (componentDependencies component)) **
           resolveCommittedValues @{nameEq} @{keyEq} {value = value}
             {world = world} {error = error}
             (dependencies (componentDependencies component)) view fibers =
               Just capability)
        capabilityWitness = isJustTrueWitness
          (resolveCommittedValues @{nameEq} @{keyEq} {value = value}
            {world = world} {error = error}
            (dependencies (componentDependencies component)) view fibers)
          capabilityIsJust
    in case capabilityWitness of
      (capability ** resolved) => reloadingAdvanceResolvedRaw nameEq keyEq
        ambient fibers actor component parent retiredFlag table step rest
        accumulator view capability resolved found

public export
0 reloadingLifecycleMove :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} state = True ->
  (actor : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} actor (registry state) = Just
    (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator view)) ->
  LifecycleMove nameEq keyEq state
reloadingLifecycleMove nameEq keyEq (MkSystemState ambient fibers) wellFormed
  actor component parent retiredFlag table remaining accumulator view found =
    case reloadingAdvanceRaw nameEq keyEq ambient fibers actor component parent
      retiredFlag table remaining accumulator view found wellFormed of
      (tag ** (afterState ** raw)) => CanAdvance actor tag afterState raw

public export
0 beginLifecycleMove :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} state = True ->
  (actor : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} actor (registry state) = Just
    (MkFiber component parent retiredFlag table (Inactive Nothing)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  targetFiber @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
    (MkFiber component parent retiredFlag table (Inactive Nothing))
    (registry state) = Just view ->
  LifecycleMove nameEq keyEq state
beginLifecycleMove nameEq keyEq (MkSystemState ambient fibers) wellFormed actor component parent
  retiredFlag table found view target =
    let sourceFiber : Fiber name key value world error
        sourceFiber = MkFiber component parent retiredFlag table (Inactive Nothing)
        afterState : SystemState name key value world error
        afterState = MkSystemState ambient
          (replaceBinding @{nameEq} actor
            (setFiberLifecycle sourceFiber
              (Reloading (componentProgram component) id view)) fibers)
        0 raw : (applyAction @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (LBegin actor)
          (MkSystemState ambient fibers) = Just (LBeginTag, afterState))
        raw = rewrite found in rewrite target in Refl
    in CanBegin actor afterState raw

public export
0 leaveLifecycleMove :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} state = True ->
  (actor : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} actor (registry state) = Just
    (MkFiber component parent retiredFlag table (Active accumulator view)) ->
  targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
      (MkFiber component parent retiredFlag table (Active accumulator view))
      (registry state)) view = False ->
  LifecycleMove nameEq keyEq state
leaveLifecycleMove nameEq keyEq (MkSystemState ambient fibers) wellFormed actor component parent
  retiredFlag table accumulator view found mismatch =
    let sourceFiber : Fiber name key value world error
        sourceFiber = MkFiber component parent retiredFlag table
          (Active accumulator view)
        afterState : SystemState name key value world error
        afterState = MkSystemState ambient
          (replaceBinding @{nameEq} actor
            (setFiberLifecycle sourceFiber
              (Unloading accumulator view Nothing)) fibers)
        0 raw : (applyAction @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (LLeave actor)
          (MkSystemState ambient fibers) = Just (LLeaveTag, afterState))
        raw = rewrite found in rewrite mismatch in Refl
    in CanLeave actor afterState raw

public export
0 unloadLifecycleMove :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} state = True ->
  (actor : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (outcome : Maybe error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} actor (registry state) = Just
    (MkFiber component parent retiredFlag table
      (Unloading accumulator view outcome)) ->
  relied @{nameEq} {key = key} {value = value} {world = world}
    {error = error} actor (registry state) = False ->
  LifecycleMove nameEq keyEq state
unloadLifecycleMove nameEq keyEq (MkSystemState ambient fibers) wellFormed actor component parent
  retiredFlag table accumulator view outcome found unrelied =
    let sourceFiber : Fiber name key value world error
        sourceFiber = MkFiber component parent retiredFlag table
          (Unloading accumulator view outcome)
        restored = accumulator (MkLocalState ambient
          (restrictOwnedPreservingOrder (componentProvisions component)
            (ownedValues table)))
        afterState : SystemState name key value world error
        afterState = MkSystemState (localWorld restored)
          (replaceBinding @{nameEq} actor
            (setFiberRuntime sourceFiber (localTable restored) (Inactive outcome))
            fibers)
        0 raw : (applyAction @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (LUnload actor)
          (MkSystemState ambient fibers) = Just (LUnloadTag, afterState))
        raw = rewrite found in rewrite unrelied in Refl
    in CanUnload actor afterState raw
