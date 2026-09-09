module DGamma.CP5O20IndexedReloadingSourceSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20AllNameSynchronizationSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| Actual right source indexed by the ALREADY chosen component/program.
||| Unlike an unindexed shared-source existential, this type cannot forget
||| which left program the successor must execute. Only lookup proof is erased.
public export
record O20MatchingReloadingSource
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (actor : name)
  (state : SystemState name key value world error)
  (component : Component key value world error)
  (remaining : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) where
  constructor MkO20MatchingReloadingSource
  matchingParent : Parent name
  matchingRetired : Bool
  matchingTable : OwnedTable key value (componentProvisions component)
  matchingOlder : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)
  matchingView : View name (dependencies (componentDependencies component))
  0 matchingFound :
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry state) =
      Just (MkFiber component matchingParent matchingRetired matchingTable (Reloading remaining matchingOlder matchingView)))

||| The native Reloading relation supplies the exact already-indexed program.
||| Only this lifecycle relation is eliminated; no dependent observation-record
||| equality or independently chosen shared program is introduced.
export
0 o20MatchingSourceFromLifecycle :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {renaming : NameBijection name} -> {actor : name} ->
  {right : SystemState name key value world error} ->
  (component : Component key value world error) ->
  (remaining : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (leftOlder : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (leftView : View name (dependencies (componentDependencies component))) ->
  (rightParent : Parent name) -> (rightRetired : Bool) ->
  (rightTable : OwnedTable key value (componentProvisions component)) ->
  (rightLifecycle : Lifecycle key value world error name (dependencies (componentDependencies component)) (componentProvisions component)) ->
  LifecycleRelatedBy renaming (Reloading remaining leftOlder leftView) rightLifecycle ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) (registry right) = Just (MkFiber component rightParent rightRetired rightTable rightLifecycle)) ->
  O20MatchingReloadingSource name key world error value nameEq (renameForward renaming actor) right component remaining
o20MatchingSourceFromLifecycle component remaining leftOlder leftView rightParent rightRetired rightTable (Reloading _ rightOlder rightView)
  (RenamedReloading Refl older views) rightFound =
    MkO20MatchingReloadingSource rightParent rightRetired rightTable rightOlder rightView rightFound
