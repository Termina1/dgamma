module DGamma.CP4DeletionPlanEffects

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionFrameCore
import Decidable.Equality

%default total

||| Exact evidence that every current-R leaf erased by a plan has the empty
||| runtime table promised by Lemma 72's no-episode invariant.
public export
data EmptyTableInactivePlan :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  {source, target : Registry name key value world error} ->
  InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target -> Type where
  EmptyTablePlanEnd : EmptyTableInactivePlan name key world error value nameEq
    NoInactiveLeafDeletion
  EmptyTablePlanStep :
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
    {rest : InactiveLeafDeletionPlan {name = name} {key = key}
      {value = value} {world = world} {error = error} nameEq
      (deleteBinding @{nameEq} removed source) target} ->
    bindings (ownedValues table) = [] ->
    EmptyTableInactivePlan name key world error value nameEq rest ->
    EmptyTableInactivePlan name key world error value nameEq
      (DeleteInactiveLeaf {fibers = source} {target = target} removed component
        parent retiredFlag table outcome found noChild rest)

0 sourceToEmptyOverwrite :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (removed : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) ->
  lookupFiber @{nameEq} removed source =
    Just (MkFiber component parent retiredFlag table (Inactive outcome)) ->
  bindings (ownedValues table) = [] ->
  EffectStateRelated keyEq
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState ambient source)))
    (setEffectTable @{nameEq} removed
      (emptyContext {key = key} {value = value})
      (projectEffectState @{nameEq}
        (the (SystemState name key value world error)
          (MkSystemState ambient source))))
sourceToEmptyOverwrite nameEq keyEq removed ambient source component parent
  retiredFlag table outcome found tableEmpty =
    MkEffectStateRelated Refl tables
  where
  0 tables : (actor : name) ->
    bindings (effectTables
      (projectEffectState @{nameEq}
        (the (SystemState name key value world error)
          (MkSystemState ambient source))) actor) =
    bindings (effectTables
      (setEffectTable @{nameEq} removed
        (emptyContext {key = key} {value = value})
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState ambient source)))) actor)
  tables actor with (decEq @{nameEq} actor removed)
    tables _ | Yes Refl = trans
      (cong bindings (projectedActorTable nameEq removed
        (the (SystemState name key value world error)
          (MkSystemState ambient source))
        (MkFiber component parent retiredFlag table (Inactive outcome)) found))
      tableEmpty
    tables actor | No distinct = Refl

||| Deleting an ordered plan of empty Inactive leaves is invisible to the full
||| effect projection.  Equality is pointwise on complete ordered actor tables,
||| so no registry/function extensionality is used.
public export
0 emptyInactivePlanPreservesEffects :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (ambient : world) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target) ->
  EmptyTableInactivePlan name key world error value nameEq plan ->
  EffectStateRelated keyEq
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState ambient source)))
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState ambient target)))
emptyInactivePlanPreservesEffects nameEq keyEq ambient source source
  NoInactiveLeafDeletion EmptyTablePlanEnd =
    effectStateReflexive keyEq
      (projectEffectState @{nameEq}
        (the (SystemState name key value world error)
          (MkSystemState ambient source)))
emptyInactivePlanPreservesEffects nameEq keyEq ambient source target
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest)
  (EmptyTablePlanStep tableEmpty emptyRest) =
    let 0 sourceToEmpty = sourceToEmptyOverwrite nameEq keyEq removed ambient
          source component parent retiredFlag table outcome found tableEmpty
        0 emptyToDeleted = projectDeleteEffectFrame nameEq keyEq removed ambient
          source
        0 sourceToDeleted = transitive (EffectStateEquivalence keyEq)
          sourceToEmpty emptyToDeleted
        0 deletedToTarget = emptyInactivePlanPreservesEffects nameEq keyEq ambient
          (deleteBinding @{nameEq} removed source) target rest emptyRest
    in transitive (EffectStateEquivalence keyEq) sourceToDeleted deletedToTarget
