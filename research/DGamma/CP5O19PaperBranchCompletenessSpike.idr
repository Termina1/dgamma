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
