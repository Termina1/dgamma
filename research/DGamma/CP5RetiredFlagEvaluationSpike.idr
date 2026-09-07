module DGamma.CP5RetiredFlagEvaluationSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4Support
import Decidable.Equality

%default total
%unbound_implicits off

||| Operational result predicate for the precise retirement flag. Failure is
||| Unit, success owns actual lookup plus flag equality; not a success axiom.
0 RetiredResultOwner :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (actor : name) -> (flag : Bool) -> Maybe (RuleTag, SystemState name key value world error) -> Type
RetiredResultOwner name key world error value nameEq actor flag Nothing = ()
RetiredResultOwner name key world error value nameEq actor flag (Just (tag, state)) =
  (fiber : Fiber name key value world error **
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} actor (registry state) = Just fiber, retired fiber = flag))

0 retiredResultOwnerReplace :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (actor : name) -> (flag : Bool) -> (source : Registry name key value world error) ->
  (old, next : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} actor source = Just old) -> (ambient : world) -> (tag : RuleTag) -> (retired next = flag) ->
  RetiredResultOwner name key world error value nameEq actor flag
    (Just (tag, MkSystemState ambient (replaceBinding @{nameEq} actor next source)))
retiredResultOwnerReplace name key world error value nameEq actor flag source old next found ambient tag exact =
  (next ** (lookupReplacedFiber @{nameEq} actor old next source found, exact))


0 retiredBeginOwner :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (before : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} actor (registry before) = Just fiber) ->
  (observed : Maybe (View name (dependencies (componentDependencies (fiberComponent fiber))))) ->
  (targetFiber @{nameEq} @{keyEq} fiber (registry before) = observed) ->
  RetiredResultOwner name key world error value nameEq actor (retired fiber) (applyAction @{nameEq} @{keyEq} (LBegin actor) before)
retiredBeginOwner name key world error value nameEq keyEq actor before
  (MkFiber component parent retiredFlag table (Inactive Nothing)) found Nothing exact =
    rewrite found in rewrite exact in ()
retiredBeginOwner name key world error value nameEq keyEq actor before
  (MkFiber component parent retiredFlag table (Inactive Nothing)) found (Just view) exact =
    rewrite found in rewrite exact in retiredResultOwnerReplace name key world error value nameEq actor retiredFlag (registry before)
      (MkFiber component parent retiredFlag table (Inactive Nothing))
      (setFiberLifecycle (MkFiber component parent retiredFlag table (Inactive Nothing)) (Reloading (componentProgram component) id view))
      found (worldState before) LBeginTag Refl
retiredBeginOwner name key world error value nameEq keyEq actor before
  (MkFiber component parent retiredFlag table (Inactive (Just failure))) found observed exact = rewrite found in ()
retiredBeginOwner name key world error value nameEq keyEq actor before
  (MkFiber component parent retiredFlag table (Reloading remaining accumulator view)) found observed exact = rewrite found in ()
retiredBeginOwner name key world error value nameEq keyEq actor before
  (MkFiber component parent retiredFlag table (Active accumulator view)) found observed exact = rewrite found in ()
retiredBeginOwner name key world error value nameEq keyEq actor before
  (MkFiber component parent retiredFlag table (Unloading accumulator view outcome)) found observed exact = rewrite found in ()


0 retiredDivertOwner :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (before : SystemState name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (remaining : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} actor (registry before) =
    Just (MkFiber component parent retiredFlag table (Reloading remaining accumulator view))) ->
  (condition : Bool) ->
  (targetMatches @{nameEq} (targetFiber @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table (Reloading remaining accumulator view)) (registry before)) view = condition) ->
  RetiredResultOwner name key world error value nameEq actor retiredFlag (applyAction @{nameEq} @{keyEq} (LDivert actor) before)
retiredDivertOwner name key world error value nameEq keyEq actor before component parent retiredFlag table remaining accumulator view found True exact =
  rewrite found in rewrite exact in ()
retiredDivertOwner name key world error value nameEq keyEq actor before component parent retiredFlag table remaining accumulator view found False exact =
  rewrite found in rewrite exact in retiredResultOwnerReplace name key world error value nameEq actor retiredFlag (registry before)
    (MkFiber component parent retiredFlag table (Reloading remaining accumulator view))
    (setFiberLifecycle (MkFiber component parent retiredFlag table (Reloading remaining accumulator view)) (Unloading accumulator view Nothing))
    found (worldState before) LDivertTag Refl


0 retiredLeaveOwner :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (before : SystemState name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} actor (registry before) =
    Just (MkFiber component parent retiredFlag table (Active accumulator view))) ->
  (condition : Bool) ->
  (targetMatches @{nameEq} (targetFiber @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table (Active accumulator view)) (registry before)) view = condition) ->
  RetiredResultOwner name key world error value nameEq actor retiredFlag (applyAction @{nameEq} @{keyEq} (LLeave actor) before)
retiredLeaveOwner name key world error value nameEq keyEq actor before component parent retiredFlag table accumulator view found True exact =
  rewrite found in rewrite exact in ()
retiredLeaveOwner name key world error value nameEq keyEq actor before component parent retiredFlag table accumulator view found False exact =
  rewrite found in rewrite exact in retiredResultOwnerReplace name key world error value nameEq actor retiredFlag (registry before)
    (MkFiber component parent retiredFlag table (Active accumulator view))
    (setFiberLifecycle (MkFiber component parent retiredFlag table (Active accumulator view)) (Unloading accumulator view Nothing))
    found (worldState before) LLeaveTag Refl


0 retiredUnloadOwner :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (before : SystemState name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) -> (outcome : Maybe error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} actor (registry before) =
    Just (MkFiber component parent retiredFlag table (Unloading accumulator view outcome))) ->
  (condition : Bool) ->
  (relied {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} actor (registry before) = condition) ->
  RetiredResultOwner name key world error value nameEq actor retiredFlag (applyAction @{nameEq} @{keyEq} (LUnload actor) before)
retiredUnloadOwner name key world error value nameEq keyEq actor before component parent retiredFlag table accumulator view outcome found True exact =
  rewrite found in rewrite exact in ()
retiredUnloadOwner name key world error value nameEq keyEq actor before component parent retiredFlag table accumulator view outcome found False exact =
  rewrite found in rewrite exact in retiredResultOwnerReplace name key world error value nameEq actor retiredFlag (registry before)
    (MkFiber component parent retiredFlag table (Unloading accumulator view outcome))
    (setFiberRuntime (MkFiber component parent retiredFlag table (Unloading accumulator view outcome))
      (localTable (accumulator (MkLocalState (worldState before) (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component) (ownedValues table)))))
      (Inactive outcome)) found
    (localWorld (accumulator (MkLocalState (worldState before) (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component) (ownedValues table))))) LUnloadTag Refl


0 retiredAdvanceEmptyOwner :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (before : SystemState name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} actor (registry before) =
    Just (MkFiber component parent retiredFlag table (Reloading [] accumulator view))) ->
  (condition : Bool) ->
  (targetMatches @{nameEq} (targetFiber @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table (Reloading [] accumulator view)) (registry before)) view = condition) ->
  RetiredResultOwner name key world error value nameEq actor retiredFlag (applyAction @{nameEq} @{keyEq} (LAdvance actor) before)
retiredAdvanceEmptyOwner name key world error value nameEq keyEq actor before component parent retiredFlag table accumulator view found True exact =
  rewrite found in rewrite exact in retiredResultOwnerReplace name key world error value nameEq actor retiredFlag (registry before)
    (MkFiber component parent retiredFlag table (Reloading [] accumulator view))
    (setFiberLifecycle (MkFiber component parent retiredFlag table (Reloading [] accumulator view)) (Active accumulator view))
    found (worldState before) LFinishTag Refl
retiredAdvanceEmptyOwner name key world error value nameEq keyEq actor before component parent retiredFlag table accumulator view found False exact =
  rewrite found in rewrite exact in retiredResultOwnerReplace name key world error value nameEq actor retiredFlag (registry before)
    (MkFiber component parent retiredFlag table (Reloading [] accumulator view))
    (setFiberLifecycle (MkFiber component parent retiredFlag table (Reloading [] accumulator view)) (Unloading accumulator view Nothing))
    found (worldState before) LDivertTag Refl


0 retiredAdvanceOutcomeOwner :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (before : SystemState name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (rest : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} actor (registry before) =
    Just (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view))) ->
  (capability : DepValues key value (dependencies (componentDependencies component))) ->
  (resolveCommittedValues {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} (dependencies (componentDependencies component)) view (registry before) = Just capability) ->
  (outcome : Either error (LocalState key value world (componentProvisions component),
    LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component))) ->
  (runStepEffect step capability (MkLocalState (worldState before) (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component) (ownedValues table))) = outcome) ->
  (condition : Bool) ->
  (targetMatches @{nameEq} (targetFiber @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view)) (registry before)) view = condition) ->
  RetiredResultOwner name key world error value nameEq actor retiredFlag (applyAction @{nameEq} @{keyEq} (LAdvance actor) before)
retiredAdvanceOutcomeOwner name key world error value nameEq keyEq actor before component parent retiredFlag table step rest accumulator view found capability resolved (Left failure) ran condition exact =
  rewrite found in rewrite resolved in rewrite ran in retiredResultOwnerReplace name key world error value nameEq actor retiredFlag (registry before)
    (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view))
    (setFiberLifecycle (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view)) (Unloading accumulator view (Just failure)))
    found (worldState before) LRaiseTag Refl
retiredAdvanceOutcomeOwner name key world error value nameEq keyEq actor before component parent retiredFlag table step [] accumulator view found capability resolved (Right (localAfter, undo)) ran True exact =
  rewrite found in rewrite resolved in rewrite ran in rewrite exact in retiredResultOwnerReplace name key world error value nameEq actor retiredFlag (registry before)
    (MkFiber component parent retiredFlag table (Reloading [step] accumulator view))
    (setFiberRuntime (MkFiber component parent retiredFlag table (Reloading [step] accumulator view)) (localTable localAfter)
      (Active (pushLocalUndo @{keyEq} (componentProvisions component) accumulator undo) view)) found (localWorld localAfter) LFinishTag Refl
retiredAdvanceOutcomeOwner name key world error value nameEq keyEq actor before component parent retiredFlag table step (next :: later) accumulator view found capability resolved (Right (localAfter, undo)) ran True exact =
  rewrite found in rewrite resolved in rewrite ran in rewrite exact in retiredResultOwnerReplace name key world error value nameEq actor retiredFlag (registry before)
    (MkFiber component parent retiredFlag table (Reloading (step :: next :: later) accumulator view))
    (setFiberRuntime (MkFiber component parent retiredFlag table (Reloading (step :: next :: later) accumulator view)) (localTable localAfter)
      (Reloading (next :: later) (pushLocalUndo @{keyEq} (componentProvisions component) accumulator undo) view)) found (localWorld localAfter) LIterTag Refl
retiredAdvanceOutcomeOwner name key world error value nameEq keyEq actor before component parent retiredFlag table step rest accumulator view found capability resolved (Right (localAfter, undo)) ran False exact =
  rewrite found in rewrite resolved in rewrite ran in rewrite exact in retiredResultOwnerReplace name key world error value nameEq actor retiredFlag (registry before)
    (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view))
    (setFiberRuntime (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view)) (localTable localAfter)
      (Unloading (pushLocalUndo @{keyEq} (componentProvisions component) accumulator undo) view Nothing)) found (localWorld localAfter) LDivertTag Refl


0 retiredAdvanceResolvedOwner :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (before : SystemState name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (rest : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} actor (registry before) =
    Just (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view))) ->
  (observed : Maybe (DepValues key value (dependencies (componentDependencies component)))) ->
  (resolveCommittedValues {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies component)) view (registry before) = observed) ->
  RetiredResultOwner name key world error value nameEq actor retiredFlag (applyAction @{nameEq} @{keyEq} (LAdvance actor) before)
retiredAdvanceResolvedOwner name key world error value nameEq keyEq actor before component parent retiredFlag table step rest accumulator view found Nothing exact =
  rewrite found in rewrite exact in ()
retiredAdvanceResolvedOwner name key world error value nameEq keyEq actor before component parent retiredFlag table step rest accumulator view found (Just capability) exact =
  retiredAdvanceOutcomeOwner name key world error value nameEq keyEq actor before component parent retiredFlag table step rest accumulator view found capability exact
    (runStepEffect step capability (MkLocalState (worldState before) (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component) (ownedValues table)))) Refl
    (targetMatches @{nameEq} (targetFiber @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view)) (registry before)) view) Refl


0 retiredLifecycleResultOwner :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (isLifecycleAction action = True) ->
  (before : SystemState name key value world error) -> (fiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} (actionOwner action) (registry before) = Just fiber) ->
  RetiredResultOwner name key world error value nameEq (actionOwner action) (retired fiber) (applyAction @{nameEq} @{keyEq} action before)
retiredLifecycleResultOwner name key world error value nameEq keyEq (OInsert actor parent component) lifecycle before fiber found = case lifecycle of Refl impossible
retiredLifecycleResultOwner name key world error value nameEq keyEq (ORetire actor) lifecycle before fiber found = case lifecycle of Refl impossible
retiredLifecycleResultOwner name key world error value nameEq keyEq (ORemove actor) lifecycle before fiber found = case lifecycle of Refl impossible
retiredLifecycleResultOwner name key world error value nameEq keyEq (LBegin actor) lifecycle before fiber found =
  retiredBeginOwner name key world error value nameEq keyEq actor before fiber found
    (targetFiber @{nameEq} @{keyEq} fiber (registry before)) Refl
retiredLifecycleResultOwner name key world error value nameEq keyEq (LAdvance actor) lifecycle before
  (MkFiber component parent retiredFlag table (Inactive outcome)) found = rewrite found in ()
retiredLifecycleResultOwner name key world error value nameEq keyEq (LAdvance actor) lifecycle before
  (MkFiber component parent retiredFlag table (Active accumulator view)) found = rewrite found in ()
retiredLifecycleResultOwner name key world error value nameEq keyEq (LAdvance actor) lifecycle before
  (MkFiber component parent retiredFlag table (Unloading accumulator view outcome)) found = rewrite found in ()
retiredLifecycleResultOwner name key world error value nameEq keyEq (LDivert actor) lifecycle before
  (MkFiber component parent retiredFlag table (Inactive outcome)) found = rewrite found in ()
retiredLifecycleResultOwner name key world error value nameEq keyEq (LDivert actor) lifecycle before
  (MkFiber component parent retiredFlag table (Active accumulator view)) found = rewrite found in ()
retiredLifecycleResultOwner name key world error value nameEq keyEq (LDivert actor) lifecycle before
  (MkFiber component parent retiredFlag table (Unloading accumulator view outcome)) found = rewrite found in ()
retiredLifecycleResultOwner name key world error value nameEq keyEq (LLeave actor) lifecycle before
  (MkFiber component parent retiredFlag table (Inactive outcome)) found = rewrite found in ()
retiredLifecycleResultOwner name key world error value nameEq keyEq (LLeave actor) lifecycle before
  (MkFiber component parent retiredFlag table (Reloading remaining accumulator view)) found = rewrite found in ()
retiredLifecycleResultOwner name key world error value nameEq keyEq (LLeave actor) lifecycle before
  (MkFiber component parent retiredFlag table (Unloading accumulator view outcome)) found = rewrite found in ()
retiredLifecycleResultOwner name key world error value nameEq keyEq (LUnload actor) lifecycle before
  (MkFiber component parent retiredFlag table (Inactive outcome)) found = rewrite found in ()
retiredLifecycleResultOwner name key world error value nameEq keyEq (LUnload actor) lifecycle before
  (MkFiber component parent retiredFlag table (Reloading remaining accumulator view)) found = rewrite found in ()
retiredLifecycleResultOwner name key world error value nameEq keyEq (LUnload actor) lifecycle before
  (MkFiber component parent retiredFlag table (Active accumulator view)) found = rewrite found in ()
retiredLifecycleResultOwner name key world error value nameEq keyEq (LAdvance actor) lifecycle before
  (MkFiber component parent retiredFlag table (Reloading [] accumulator view)) found =
    retiredAdvanceEmptyOwner name key world error value nameEq keyEq actor before component parent retiredFlag table accumulator view found
      (targetMatches @{nameEq} (targetFiber @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table (Reloading [] accumulator view)) (registry before)) view) Refl
retiredLifecycleResultOwner name key world error value nameEq keyEq (LAdvance actor) lifecycle before
  (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view)) found =
    retiredAdvanceResolvedOwner name key world error value nameEq keyEq actor before component parent retiredFlag table step rest accumulator view found
      (resolveCommittedValues {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq}
        (dependencies (componentDependencies component)) view (registry before)) Refl
retiredLifecycleResultOwner name key world error value nameEq keyEq (LDivert actor) lifecycle before
  (MkFiber component parent retiredFlag table (Reloading remaining accumulator view)) found =
    retiredDivertOwner name key world error value nameEq keyEq actor before component parent retiredFlag table remaining accumulator view found
      (targetMatches @{nameEq} (targetFiber @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table (Reloading remaining accumulator view)) (registry before)) view) Refl
retiredLifecycleResultOwner name key world error value nameEq keyEq (LLeave actor) lifecycle before
  (MkFiber component parent retiredFlag table (Active accumulator view)) found =
    retiredLeaveOwner name key world error value nameEq keyEq actor before component parent retiredFlag table accumulator view found
      (targetMatches @{nameEq} (targetFiber @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table (Active accumulator view)) (registry before)) view) Refl
retiredLifecycleResultOwner name key world error value nameEq keyEq (LUnload actor) lifecycle before
  (MkFiber component parent retiredFlag table (Unloading accumulator view outcome)) found =
    retiredUnloadOwner name key world error value nameEq keyEq actor before component parent retiredFlag table accumulator view outcome found
      (relied {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} actor (registry before)) Refl

||| Actual successful lifecycle target, with its flag equated to the actual
||| source fiber's. This is not inferred from the weaker RetirementUpdate type.
export
0 rawLifecycleRetiredFlags :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (isLifecycleAction action = True) ->
  (before, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (sourceFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} (actionOwner action) (registry before) = Just sourceFiber) ->
  (applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  (targetFiber : Fiber name key value world error **
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} (actionOwner action) (registry afterState) = Just targetFiber,
     retired targetFiber = retired sourceFiber))
rawLifecycleRetiredFlags name key world error value nameEq keyEq action lifecycle before afterState tag sourceFiber sourceFound raw =
  replace {p = RetiredResultOwner name key world error value nameEq (actionOwner action) (retired sourceFiber)} raw
    (retiredLifecycleResultOwner name key world error value nameEq keyEq action lifecycle before sourceFiber sourceFound)
