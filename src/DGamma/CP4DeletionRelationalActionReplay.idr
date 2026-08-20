module DGamma.CP4DeletionRelationalActionReplay

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionRelationalActionOrchestration
import DGamma.CP4DeletionRelationalLifecycleAdvance
import DGamma.CP4DeletionRelationalLifecycleBegin
import DGamma.CP4DeletionRelationalLifecycleDivert
import DGamma.CP4DeletionRelationalLifecycleLeave
import DGamma.CP4DeletionRelationalLifecycleUnload
import DGamma.CP4DeletionRelationalSuffixFold
import Decidable.Equality

%default total

||| Complete local operational congruence used by the Lemma-72 relational
||| suffix fold.  Every constructor of `Action` is discharged by a checked
||| orchestration or lifecycle replay; there is no fallback premise.
public export
0 replayRelatedAction :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  RelationalActionReplayer name key world error value nameEq keyEq
replayRelatedAction nameEq keyEq (OInsert actor parent component) left right
  named raw leftWf effects controls rightWf =
    replayRelatedOrchestrationAction nameEq keyEq
      (OInsert actor parent component) Refl left right named raw leftWf effects
      controls rightWf
replayRelatedAction nameEq keyEq (ORetire actor) left right named raw leftWf
  effects controls rightWf =
    replayRelatedOrchestrationAction nameEq keyEq (ORetire actor) Refl left
      right named raw leftWf effects controls rightWf
replayRelatedAction nameEq keyEq (ORemove actor) left right named raw leftWf
  effects controls rightWf =
    replayRelatedOrchestrationAction nameEq keyEq (ORemove actor) Refl left
      right named raw leftWf effects controls rightWf
replayRelatedAction nameEq keyEq (LBegin actor) left right named raw leftWf
  effects controls rightWf =
    replayRelatedBegin nameEq keyEq actor left right named raw leftWf effects
      controls rightWf
replayRelatedAction nameEq keyEq (LAdvance actor) left right named raw leftWf
  effects controls rightWf =
    replayRelatedAdvance nameEq keyEq actor left right named raw leftWf effects
      controls rightWf
replayRelatedAction nameEq keyEq (LDivert actor) left right named raw leftWf
  effects controls rightWf =
    replayRelatedDivert nameEq keyEq actor left right named raw leftWf effects
      controls rightWf
replayRelatedAction nameEq keyEq (LLeave actor) left right named raw leftWf
  effects controls rightWf =
    replayRelatedLeave nameEq keyEq actor left right named raw leftWf effects
      controls rightWf
replayRelatedAction nameEq keyEq (LUnload actor) left right named raw leftWf
  effects controls rightWf =
    replayRelatedUnload nameEq keyEq actor left right named raw leftWf effects
      controls rightWf
