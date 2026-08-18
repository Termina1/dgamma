module DGamma.CP4DeletionControlAdvance

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP4DeletionControlCore
import DGamma.CP4DeletionControlBegin
import Decidable.Equality

%default total

0 nothingNotJust : Nothing = Just item -> Void
nothingNotJust Refl impossible

0 boolAndLeft : (left, right : Bool) -> left && right = True -> left = True
boolAndLeft False right valid = case valid of Refl impossible
boolAndLeft True right valid = Refl

0 reloadingProvidersValid :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (fiber : Fiber name key value world error) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)))) ->
  (accumulator : LocalState key value world
      (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world
      (componentProvisions (fiberComponent fiber))) ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  (fibers : Registry name key value world error) ->
  fiberLifecycle fiber = Reloading remaining accumulator view ->
  fiberViewInvariant @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} fiber fibers = True ->
  viewProvidersInvariant @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} fibers view = True
reloadingProvidersValid nameEq keyEq
  (MkFiber component parent retired table (Inactive outcome)) remaining
  accumulator view fibers life valid = case life of Refl impossible
reloadingProvidersValid nameEq keyEq
  (MkFiber component parent retired table
    (Reloading actualRemaining actualAccumulator actualView)) remaining
  accumulator view fibers life valid = case life of
    Refl => boolAndLeft _ _ valid
reloadingProvidersValid nameEq keyEq
  (MkFiber component parent retired table (Active actualAccumulator actualView))
  remaining accumulator view fibers life valid = case life of Refl impossible
reloadingProvidersValid nameEq keyEq
  (MkFiber component parent retired table
    (Unloading actualAccumulator actualView outcome)) remaining accumulator view
  fibers life valid = case life of Refl impossible

0 advanceAfterTarget :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor, removed : name) -> (ambient : world) ->
  (fibers : Registry name key value world error) ->
  (actorFiber : Fiber name key value world error) ->
  (step : StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent actorFiber)))
    (componentProvisions (fiberComponent actorFiber))) ->
  (rest : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent actorFiber)))
    (componentProvisions (fiberComponent actorFiber)))) ->
  (accumulator : LocalState key value world
      (componentProvisions (fiberComponent actorFiber)) ->
    LocalState key value world
      (componentProvisions (fiberComponent actorFiber))) ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent actorFiber)))) ->
  (capability : DepValues key value
    (dependencies (componentDependencies (fiberComponent actorFiber)))) ->
  fiberLifecycle actorFiber = Reloading (step :: rest) accumulator view ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} actor (deleteBinding @{nameEq} removed fibers) =
    Just actorFiber ->
  resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error}
    (dependencies (componentDependencies (fiberComponent actorFiber))) view
    (deleteBinding @{nameEq} removed fibers) = Just capability ->
  targetFiber @{nameEq} @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error} actorFiber
    (deleteBinding @{nameEq} removed fibers) =
    targetFiber @{nameEq} @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error} actorFiber fibers ->
  (localAfter : LocalState key value world
    (componentProvisions (fiberComponent actorFiber))) ->
  (undo : LocalState key value world
      (componentProvisions (fiberComponent actorFiber)) ->
    LocalState key value world
      (componentProvisions (fiberComponent actorFiber))) ->
  runStepEffect step capability
    (MkLocalState ambient
      (restrictOwnedPreservingOrder @{keyEq}
        (componentProvisions (fiberComponent actorFiber))
        (ownedValues (fiberTable actorFiber)))) = Right (localAfter, undo) ->
  (targetStable : Bool) ->
  targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error} actorFiber fibers) view = targetStable ->
  RawActionResult name key world error value nameEq keyEq
    (the (Action name key value world error) (LAdvance actor))
    (MkSystemState ambient (deleteBinding @{nameEq} removed fibers))
advanceAfterTarget nameEq keyEq actor removed ambient fibers actorFiber step []
  accumulator view capability actorLife replayFound replayResolved replayTarget
  localAfter undo ran True matches =
    MkRawActionResult LFinishTag
      (MkSystemState (localWorld localAfter)
        (replaceBinding @{nameEq} actor
          (setFiberRuntime actorFiber (localTable localAfter)
            (Active (pushLocalUndo (componentProvisions (fiberComponent actorFiber)) accumulator undo) view))
          (deleteBinding @{nameEq} removed fibers)))
      (rewrite replayFound in rewrite actorLife in rewrite replayResolved in
        rewrite ran in rewrite replayTarget in rewrite matches in Refl)
advanceAfterTarget nameEq keyEq actor removed ambient fibers actorFiber step
  (next :: later) accumulator view capability actorLife replayFound
  replayResolved replayTarget localAfter undo ran True matches =
    MkRawActionResult LIterTag
      (MkSystemState (localWorld localAfter)
        (replaceBinding @{nameEq} actor
          (setFiberRuntime actorFiber (localTable localAfter)
            (Reloading (next :: later) (pushLocalUndo (componentProvisions (fiberComponent actorFiber)) accumulator undo) view))
          (deleteBinding @{nameEq} removed fibers)))
      (rewrite replayFound in rewrite actorLife in rewrite replayResolved in
        rewrite ran in rewrite replayTarget in rewrite matches in Refl)
advanceAfterTarget nameEq keyEq actor removed ambient fibers actorFiber step rest
  accumulator view capability actorLife replayFound replayResolved replayTarget
  localAfter undo ran False matches =
    MkRawActionResult LDivertTag
      (MkSystemState (localWorld localAfter)
        (replaceBinding @{nameEq} actor
          (setFiberRuntime actorFiber (localTable localAfter)
            (Unloading (pushLocalUndo (componentProvisions (fiberComponent actorFiber)) accumulator undo) view Nothing))
          (deleteBinding @{nameEq} removed fibers)))
      (rewrite replayFound in rewrite actorLife in rewrite replayResolved in
        rewrite ran in rewrite replayTarget in rewrite matches in Refl)

0 advanceAfterRun :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor, removed : name) -> (ambient : world) ->
  (fibers : Registry name key value world error) ->
  (actorFiber : Fiber name key value world error) ->
  (step : StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent actorFiber)))
    (componentProvisions (fiberComponent actorFiber))) ->
  (rest : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent actorFiber)))
    (componentProvisions (fiberComponent actorFiber)))) ->
  (accumulator : LocalState key value world
      (componentProvisions (fiberComponent actorFiber)) ->
    LocalState key value world
      (componentProvisions (fiberComponent actorFiber))) ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent actorFiber)))) ->
  (capability : DepValues key value
    (dependencies (componentDependencies (fiberComponent actorFiber)))) ->
  fiberLifecycle actorFiber = Reloading (step :: rest) accumulator view ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} actor (deleteBinding @{nameEq} removed fibers) =
    Just actorFiber ->
  resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error}
    (dependencies (componentDependencies (fiberComponent actorFiber))) view
    (deleteBinding @{nameEq} removed fibers) = Just capability ->
  targetFiber @{nameEq} @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error} actorFiber
    (deleteBinding @{nameEq} removed fibers) =
    targetFiber @{nameEq} @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error} actorFiber fibers ->
  RawActionResult name key world error value nameEq keyEq
    (the (Action name key value world error) (LAdvance actor))
    (MkSystemState ambient (deleteBinding @{nameEq} removed fibers))
advanceAfterRun nameEq keyEq actor removed ambient fibers actorFiber step rest
  accumulator view capability actorLife replayFound replayResolved replayTarget
  with (runStepEffect step capability
    (MkLocalState ambient
      (restrictOwnedPreservingOrder @{keyEq}
        (componentProvisions (fiberComponent actorFiber))
        (ownedValues (fiberTable actorFiber))))) proof ran
  advanceAfterRun nameEq keyEq actor removed ambient fibers actorFiber step rest
    accumulator view capability actorLife replayFound replayResolved replayTarget
    | Left failure =
      MkRawActionResult LRaiseTag
        (MkSystemState ambient
          (replaceBinding @{nameEq} actor
            (setFiberLifecycle actorFiber
              (Unloading accumulator view (Just failure)))
            (deleteBinding @{nameEq} removed fibers)))
        (rewrite replayFound in rewrite actorLife in rewrite replayResolved in
          rewrite ran in Refl)
  advanceAfterRun nameEq keyEq actor removed ambient fibers actorFiber step rest
    accumulator view capability actorLife replayFound replayResolved replayTarget
    | Right (localAfter, undo)
    with (targetMatches @{nameEq}
      (targetFiber @{nameEq} @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error} actorFiber fibers) view) proof matches
    advanceAfterRun nameEq keyEq actor removed ambient fibers actorFiber step rest
      accumulator view capability actorLife replayFound replayResolved replayTarget
      | Right (localAfter, undo) | targetStable =
        advanceAfterTarget nameEq keyEq actor removed ambient fibers actorFiber
          step rest accumulator view capability actorLife replayFound
          replayResolved replayTarget localAfter undo ran
          targetStable matches

||| L-Advance replays after erasing a distinct Inactive entry. Definition-58
||| well-formedness excludes that entry from the committed provider view, while
||| target resolution is unchanged because an Inactive fiber provides no key.
public export
0 advanceApplicableAfterInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor, removed : name) -> Not (actor = removed) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (removedComponent : Component key value world error) ->
  (removedParent : Parent name) -> (removedRetired : Bool) ->
  (removedTable : OwnedTable key value
    (componentProvisions removedComponent)) ->
  (removedOutcome : Maybe error) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} removed fibers = Just
    (MkFiber removedComponent removedParent removedRetired removedTable
      (Inactive removedOutcome)) ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (MkSystemState ambient fibers) = True ->
  {tag : RuleTag} ->
  {afterState : SystemState name key value world error} ->
  applyAction @{nameEq} @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error} (LAdvance actor)
    (MkSystemState ambient fibers) = Just (tag, afterState) ->
  RawActionResult name key world error value nameEq keyEq
    (the (Action name key value world error) (LAdvance actor))
    (MkSystemState ambient (deleteBinding @{nameEq} removed fibers))
advanceApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
  nameEq keyEq actor removed distinct ambient fibers removedComponent
  removedParent removedRetired removedTable removedOutcome removedFound wellFormed
  raw with (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} actor fibers) proof actorFound
  advanceApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
    nameEq keyEq actor removed distinct ambient fibers removedComponent
    removedParent removedRetired removedTable removedOutcome removedFound wellFormed
    raw | Nothing = void (nothingNotJust raw)
  advanceApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
    nameEq keyEq actor removed distinct ambient fibers removedComponent
    removedParent removedRetired removedTable removedOutcome removedFound wellFormed
    raw | Just actorFiber with (fiberLifecycle actorFiber) proof actorLife
    advanceApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound
      wellFormed raw | Just actorFiber | Inactive outcome =
        void (nothingNotJust raw)
    advanceApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound
      wellFormed raw | Just actorFiber | Reloading [] accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error} actorFiber fibers) view) proof matches
      advanceApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
        nameEq keyEq actor removed distinct ambient fibers removedComponent
        removedParent removedRetired removedTable removedOutcome removedFound
        wellFormed raw | Just actorFiber | Reloading [] accumulator view | True =
          let replayFound = trans
                (lookupDeleteOther actor removed distinct fibers) actorFound
              replayTarget = targetFiberInactiveDelete nameEq keyEq actorFiber
                removed removedComponent removedParent removedRetired removedTable
                removedOutcome fibers removedFound
          in MkRawActionResult LFinishTag
            (MkSystemState ambient
              (replaceBinding @{nameEq} actor
                (setFiberLifecycle actorFiber (Active accumulator view))
                (deleteBinding @{nameEq} removed fibers)))
            (rewrite replayFound in rewrite actorLife in rewrite replayTarget in
              rewrite matches in Refl)
      advanceApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
        nameEq keyEq actor removed distinct ambient fibers removedComponent
        removedParent removedRetired removedTable removedOutcome removedFound
        wellFormed raw | Just actorFiber | Reloading [] accumulator view | False =
          let replayFound = trans
                (lookupDeleteOther actor removed distinct fibers) actorFound
              replayTarget = targetFiberInactiveDelete nameEq keyEq actorFiber
                removed removedComponent removedParent removedRetired removedTable
                removedOutcome fibers removedFound
          in MkRawActionResult LDivertTag
            (MkSystemState ambient
              (replaceBinding @{nameEq} actor
                (setFiberLifecycle actorFiber
                  (Unloading accumulator view Nothing))
                (deleteBinding @{nameEq} removed fibers)))
            (rewrite replayFound in rewrite actorLife in rewrite replayTarget in
              rewrite matches in Refl)
    advanceApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound
      wellFormed raw | Just actorFiber |
      Reloading (step :: rest) accumulator view
      with (resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error}
        (dependencies (componentDependencies (fiberComponent actorFiber))) view
        fibers) proof resolved
      advanceApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
        nameEq keyEq actor removed distinct ambient fibers removedComponent
        removedParent removedRetired removedTable removedOutcome removedFound
        wellFormed raw | Just actorFiber |
        Reloading (step :: rest) accumulator view | Nothing =
          void (nothingNotJust raw)
      advanceApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
        nameEq keyEq actor removed distinct ambient fibers removedComponent
        removedParent removedRetired removedTable removedOutcome removedFound
        wellFormed raw | Just actorFiber |
        Reloading (step :: rest) accumulator view | Just capability =
          let actorView = wellFormedFiberView nameEq keyEq actor
                (MkSystemState ambient fibers) actorFiber actorFound wellFormed
              providersValid = reloadingProvidersValid nameEq keyEq actorFiber
                (step :: rest) accumulator view fibers actorLife actorView
              replayResolved = trans
                (resolveCommittedValuesInactiveDelete nameEq keyEq
                  (dependencies
                    (componentDependencies (fiberComponent actorFiber))) view
                  removed removedComponent removedParent removedRetired
                  removedTable removedOutcome fibers removedFound providersValid)
                resolved
              replayFound = trans
                (lookupDeleteOther actor removed distinct fibers) actorFound
              replayTarget = targetFiberInactiveDelete nameEq keyEq actorFiber
                removed removedComponent removedParent removedRetired removedTable
                removedOutcome fibers removedFound
          in advanceAfterRun nameEq keyEq actor removed ambient fibers actorFiber
            step rest accumulator view capability actorLife replayFound
            replayResolved replayTarget
    advanceApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound
      wellFormed raw | Just actorFiber | Active accumulator view =
        void (nothingNotJust raw)
    advanceApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound
      wellFormed raw | Just actorFiber | Unloading accumulator view outcome =
        void (nothingNotJust raw)
