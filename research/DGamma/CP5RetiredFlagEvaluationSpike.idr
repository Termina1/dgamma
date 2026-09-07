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
