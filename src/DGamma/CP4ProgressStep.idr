module DGamma.CP4ProgressStep

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressStepCore
import DGamma.CP4ProgressStepBegin
import DGamma.CP4ProgressStepAdvance
import DGamma.CP4ProgressStepDivert
import DGamma.CP4ProgressStepLeave
import DGamma.CP4ProgressStepUnload
import Decidable.Equality

%default total

||| All five lifecycle action forms satisfy the potential-step interface.
||| The three orchestration forms contradict `LifecycleOnly` immediately.
public export
0 lifecycleActorPotentialStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (bound : Nat) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  isLifecycleAction action = True ->
  programsBoundedBy bound before = True ->
  ActorPotentialStep name key world error value nameEq keyEq bound
    (actionOwner action) before afterState
lifecycleActorPotentialStep nameEq keyEq bound
  (OInsert actor parent component) tag before afterState raw lifecycle programs =
    case lifecycle of Refl impossible
lifecycleActorPotentialStep nameEq keyEq bound (ORetire actor) tag before
  afterState raw lifecycle programs = case lifecycle of Refl impossible
lifecycleActorPotentialStep nameEq keyEq bound (ORemove actor) tag before
  afterState raw lifecycle programs = case lifecycle of Refl impossible
lifecycleActorPotentialStep nameEq keyEq bound (LBegin actor) tag before
  afterState raw lifecycle programs =
    beginActorPotentialStep nameEq keyEq bound actor before afterState tag raw
      programs
lifecycleActorPotentialStep nameEq keyEq bound (LAdvance actor) tag before
  afterState raw lifecycle programs =
    advanceActorPotentialStep nameEq keyEq bound actor before afterState tag raw
lifecycleActorPotentialStep nameEq keyEq bound (LDivert actor) tag before
  afterState raw lifecycle programs =
    divertActorPotentialStep nameEq keyEq bound actor before afterState tag raw
lifecycleActorPotentialStep nameEq keyEq bound (LLeave actor) tag before
  afterState raw lifecycle programs =
    leaveActorPotentialStep nameEq keyEq bound actor before afterState tag raw
lifecycleActorPotentialStep nameEq keyEq bound (LUnload actor) tag before
  afterState raw lifecycle programs =
    unloadActorPotentialStep nameEq keyEq bound actor before afterState tag raw
