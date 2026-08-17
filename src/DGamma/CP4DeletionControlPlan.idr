module DGamma.CP4DeletionControlPlan

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Metatheory
import DGamma.CP4DeletionControl
import DGamma.CP4DeletionControlBegin
import Decidable.Equality

%default total

||| A constructive, ordered deletion of zero or more Inactive leaves. Each tail
||| is indexed by the registry produced by the preceding deletion, so lookup and
||| childlessness obligations cannot refer to a stale source.
public export
data InactiveLeafDeletionPlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  Registry name key value world error ->
  Registry name key value world error -> Type where
  NoInactiveLeafDeletion :
    InactiveLeafDeletionPlan nameEq fibers fibers
  DeleteInactiveLeaf :
    (removed : name) ->
    (component : Component key value world error) ->
    (parent : Parent name) -> (retiredFlag : Bool) ->
    (table : OwnedTable key value (componentProvisions component)) ->
    (outcome : Maybe error) ->
    (0 found : lookupFiber @{nameEq} {name = name} {key = key}
      {value = value} {world = world} {error = error} removed fibers = Just
      (MkFiber component parent retiredFlag table (Inactive outcome))) ->
    (0 noChild : hasChild @{nameEq} {name = name} {key = key}
      {value = value} {world = world} {error = error} removed fibers = False) ->
    InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
      {world = world} {error = error} nameEq
      (deleteBinding @{nameEq} removed fibers) target ->
    InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
      {world = world} {error = error} nameEq fibers target

||| The surviving actor is distinct from every leaf erased by the plan.
public export
data ActorOutsideDeletionPlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  (actor : name) ->
  {source, target : Registry name key value world error} ->
  InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target -> Type where
  ActorOutsideDeletionEnd :
    ActorOutsideDeletionPlan actor NoInactiveLeafDeletion
  ActorOutsideDeletionStep :
    {source, target : Registry name key value world error} ->
    {removed : name} ->
    {component : Component key value world error} ->
    {parent : Parent name} -> {retiredFlag : Bool} ->
    {table : OwnedTable key value (componentProvisions component)} ->
    {outcome : Maybe error} ->
    {0 found : lookupFiber @{nameEq} {name = name} {key = key}
      {value = value} {world = world} {error = error} removed source = Just
        (MkFiber component parent retiredFlag table (Inactive outcome))} ->
    {0 noChild : hasChild @{nameEq} {name = name} {key = key}
      {value = value} {world = world} {error = error} removed source = False} ->
    (0 rest : InactiveLeafDeletionPlan {name = name} {key = key}
      {value = value} {world = world} {error = error} nameEq
      (deleteBinding @{nameEq} removed source) target) ->
    (0 distinct : Not (actor = removed)) ->
    ActorOutsideDeletionPlan actor rest ->
    ActorOutsideDeletionPlan actor
      (DeleteInactiveLeaf {fibers = source} {target = target} removed component
        parent retiredFlag table outcome found noChild rest)

||| Iterated checked control applicability for the entire deleted set R.
||| Every lifecycle guard is revalidated at each smaller registry, rather than
||| being inferred from effect commutation.
public export
0 checkedLifecycleAfterInactivePlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (lifecycle : isLifecycleAction action = True) ->
  (ambient : world) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target) ->
  ActorOutsideDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} (actionOwner action) plan ->
  (sourceWellFormed : registryWellFormed @{nameEq} @{keyEq}
    {name = name} {key = key} {value = value} {world = world} {error = error}
    (MkSystemState ambient source) = True) ->
  {tag : RuleTag} ->
  {afterState : SystemState name key value world error} ->
  checkedApplyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} action
    (MkSystemState ambient source) = Just (tag, afterState) ->
  TransitionResult {name = name} {key = key} {value = value} {world = world}
    {error = error} (MkSystemState ambient target)
checkedLifecycleAfterInactivePlan {tag} {afterState} nameEq keyEq action lifecycle
  ambient source source NoInactiveLeafDeletion ActorOutsideDeletionEnd
  sourceWellFormed checked =
    MkTransitionResult afterState tag
      (Fired nameEq keyEq action tag checked)
checkedLifecycleAfterInactivePlan {name} {key} {world} {error} {value}
  nameEq keyEq action lifecycle ambient source target
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest)
  (ActorOutsideDeletionStep rest distinct outsideRest) sourceWellFormed checked =
    let raw = checkedActionProjects nameEq keyEq action
          (MkSystemState ambient source) _ _ checked
        replayRaw = lifecycleApplicableAfterInactiveDelete nameEq keyEq action
          lifecycle removed distinct ambient source component parent retiredFlag
          table outcome found sourceWellFormed raw
        nextWellFormed = registryWellFormedInactiveDelete nameEq keyEq ambient
          removed component parent retiredFlag table outcome source found noChild
          sourceWellFormed
    in case replayRaw of
      MkRawActionResult replayTag replayAfter replayEquation =>
        let replayTargetWellFormed = preservationTheoremProof nameEq keyEq action
              (MkSystemState ambient (deleteBinding @{nameEq} removed source))
              replayAfter replayTag nextWellFormed replayEquation
            replayChecked : (checkedApplyAction @{nameEq} @{keyEq} action
              (MkSystemState ambient (deleteBinding @{nameEq} removed source)) =
              Just (replayTag, replayAfter))
            replayChecked = rewrite replayEquation in
              rewrite replayTargetWellFormed in Refl
        in checkedLifecycleAfterInactivePlan nameEq keyEq action lifecycle ambient
          (deleteBinding @{nameEq} removed source) target rest outsideRest
          nextWellFormed replayChecked
