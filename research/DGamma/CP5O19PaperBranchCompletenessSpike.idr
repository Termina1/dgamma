module DGamma.CP5O19PaperBranchCompletenessSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Unloading is absorbing under an ACTUAL own action other than L-Unload.
||| The source lookup owns the exact callback/view/outcome. An insertion at
||| that already-present name contradicts the real insertion plan's absence;
||| all other lifecycle actions are inapplicable, and retirement keeps phase.
export
0 o19UnloadingOwnAction :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) -> (outcome : Maybe error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) fibers =
    Just (MkFiber component parent retiredFlag table (Unloading accumulator view outcome))) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  (applyAction @{nameEq} @{keyEq} action (MkSystemState ambient fibers) = Just (tag, afterState)) ->
  Not (action = LUnload (actionOwner action)) ->
  (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) afterState = True)
o19UnloadingOwnAction nameEq keyEq (OInsert actor newParent newComponent) ambient fibers component parent retiredFlag table accumulator view outcome found tag afterState raw notUnload =
  void (nothingIsNotJust (trans (sym (foreignInsertViewAbsent
    (foreignInsertPlanView nameEq keyEq actor newParent newComponent ambient fibers tag afterState raw))) found))
o19UnloadingOwnAction nameEq keyEq (ORetire actor) ambient fibers component parent retiredFlag table accumulator view outcome found tag afterState raw notUnload =
  replace {p = \state => unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} actor state = True}
    (cong Builtin.snd (justInjective (trans
      (sym (the (applyAction @{nameEq} @{keyEq} (ORetire actor) (MkSystemState ambient fibers) =
        Just (ORetireTag, MkSystemState ambient (replaceBinding @{nameEq} actor
          (MkFiber component parent True table (Unloading accumulator view outcome)) fibers)))
        (rewrite found in Refl))) raw)))
    (rewrite lookupReplacedFiber @{nameEq} actor
      (MkFiber component parent retiredFlag table (Unloading accumulator view outcome))
      (MkFiber component parent True table (Unloading accumulator view outcome)) fibers found in Refl)
o19UnloadingOwnAction nameEq keyEq (ORemove actor) ambient fibers component parent False table accumulator view outcome found tag afterState raw notUnload =
  void (nothingIsNotJust (trans (sym (the (applyAction @{nameEq} @{keyEq} (ORemove actor) (MkSystemState ambient fibers) = Nothing)
    (rewrite found in Refl))) raw))
o19UnloadingOwnAction nameEq keyEq (ORemove actor) ambient fibers component parent True table accumulator view outcome found tag afterState raw notUnload =
  void (nothingIsNotJust (trans (sym (the (applyAction @{nameEq} @{keyEq} (ORemove actor) (MkSystemState ambient fibers) = Nothing)
    (rewrite found in Refl))) raw))
o19UnloadingOwnAction nameEq keyEq (LBegin actor) ambient fibers component parent retiredFlag table accumulator view outcome found tag afterState raw notUnload =
  void (nothingIsNotJust (trans (sym (the (applyAction @{nameEq} @{keyEq} (LBegin actor) (MkSystemState ambient fibers) = Nothing)
    (rewrite found in Refl))) raw))
o19UnloadingOwnAction nameEq keyEq (LAdvance actor) ambient fibers component parent retiredFlag table accumulator view outcome found tag afterState raw notUnload =
  void (nothingIsNotJust (trans (sym (the (applyAction @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState ambient fibers) = Nothing)
    (rewrite found in Refl))) raw))
o19UnloadingOwnAction nameEq keyEq (LDivert actor) ambient fibers component parent retiredFlag table accumulator view outcome found tag afterState raw notUnload =
  void (nothingIsNotJust (trans (sym (the (applyAction @{nameEq} @{keyEq} (LDivert actor) (MkSystemState ambient fibers) = Nothing)
    (rewrite found in Refl))) raw))
o19UnloadingOwnAction nameEq keyEq (LLeave actor) ambient fibers component parent retiredFlag table accumulator view outcome found tag afterState raw notUnload =
  void (nothingIsNotJust (trans (sym (the (applyAction @{nameEq} @{keyEq} (LLeave actor) (MkSystemState ambient fibers) = Nothing)
    (rewrite found in Refl))) raw))
o19UnloadingOwnAction nameEq keyEq (LUnload actor) ambient fibers component parent retiredFlag table accumulator view outcome found tag afterState raw notUnload =
  void (notUnload Refl)

||| Source observation plus real checked local update extends absorption to
||| arbitrary actions. Foreign actions preserve the selected lookup exactly;
||| the own branch uses A1, never an installed-to-paper cast.
export
0 o19UnloadingStepObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (afterState : SystemState name key value world error) ->
  (raw : applyAction @{nameEq} @{keyEq} action (MkSystemState ambient fibers) = Just (tag, afterState)) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected fibers = observed) ->
  (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} selected (MkSystemState ambient fibers) = True) ->
  Not (action = LUnload selected) ->
  (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} selected afterState = True)
o19UnloadingStepObserved nameEq keyEq selected action tag ambient fibers afterState raw Nothing found unloading notUnload =
  void (uninhabited (trans (sym (the (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} selected (MkSystemState ambient fibers) = False)
    (rewrite found in Refl))) unloading))
o19UnloadingStepObserved nameEq keyEq selected action tag ambient fibers afterState raw
  (Just (MkFiber component parent retiredFlag table (Inactive outcome))) found unloading notUnload =
  void (uninhabited (trans (sym (the (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} selected (MkSystemState ambient fibers) = False)
    (rewrite found in Refl))) unloading))
o19UnloadingStepObserved nameEq keyEq selected action tag ambient fibers afterState raw
  (Just (MkFiber component parent retiredFlag table (Reloading remaining accumulator view))) found unloading notUnload =
  void (uninhabited (trans (sym (the (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} selected (MkSystemState ambient fibers) = False)
    (rewrite found in Refl))) unloading))
o19UnloadingStepObserved nameEq keyEq selected action tag ambient fibers afterState raw
  (Just (MkFiber component parent retiredFlag table (Active accumulator view))) found unloading notUnload =
  void (uninhabited (trans (sym (the (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} selected (MkSystemState ambient fibers) = False)
    (rewrite found in Refl))) unloading))
o19UnloadingStepObserved nameEq keyEq selected action tag ambient fibers afterState raw
  (Just (MkFiber component parent retiredFlag table (Unloading accumulator view outcome))) found unloading notUnload =
  case decEq @{nameEq} selected (actionOwner action) of
    Yes Refl => o19UnloadingOwnAction nameEq keyEq action ambient fibers component parent retiredFlag table accumulator view outcome found tag afterState raw notUnload
    No distinct => rewrite systemLocalUpdateForeign nameEq selected (actionOwner action) distinct
      (MkSystemState ambient fibers) afterState (applyActionLocalUpdate nameEq keyEq action (MkSystemState ambient fibers) afterState tag raw) in
        rewrite found in Refl

||| Actual aligned no-unload evolution: once Unloading, every remaining cut
||| including the endpoint is Unloading. No assumption about installed being
||| a paper activation is made anywhere in this induction.
export
0 o19UnloadingTrace :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  NoParentUnload selected trace ->
  (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} selected first = True) ->
  (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} selected finalState = True)
o19UnloadingTrace nameEq keyEq selected _ AlignedEnd NoParentUnloadEnd unloading = unloading
o19UnloadingTrace {first = MkSystemState ambient fibers} nameEq keyEq selected _
  (AlignedStep action tag checked rest alignedTail) (NoParentUnloadStep _ _ excluded tail) unloading =
    o19UnloadingTrace nameEq keyEq selected rest alignedTail tail
      (o19UnloadingStepObserved nameEq keyEq selected action tag ambient fibers _
        (checkedActionProjects nameEq keyEq action (MkSystemState ambient fibers) _ tag checked)
        (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected fibers) Refl unloading excluded)

||| An actual final-active observation excludes Unloading at that same cut.
||| Together with A3 this rules out recovery branches anywhere in a no-unload
||| suffix, rather than mistaking installation for paper-rule completeness.
export
0 o19ActiveNotUnloadingObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) -> (state : SystemState name key value world error) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry state) = observed) ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected state = True) ->
  (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} selected state = False)
o19ActiveNotUnloadingObserved nameEq selected state Nothing found active = rewrite found in Refl
o19ActiveNotUnloadingObserved nameEq selected state
  (Just (MkFiber component parent retiredFlag table (Inactive outcome))) found active = rewrite found in Refl
o19ActiveNotUnloadingObserved nameEq selected state
  (Just (MkFiber component parent retiredFlag table (Reloading remaining accumulator view))) found active = rewrite found in Refl
o19ActiveNotUnloadingObserved nameEq selected state
  (Just (MkFiber component parent retiredFlag table (Active accumulator view))) found active = rewrite found in Refl
o19ActiveNotUnloadingObserved nameEq selected state
  (Just (MkFiber component parent retiredFlag table (Unloading accumulator view outcome))) found active =
    void (uninhabited (trans (sym (the (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected state = False)
      (rewrite found in Refl))) active))
