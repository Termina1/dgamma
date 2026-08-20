module DGamma.CP4DeletionPostCloseEffectReplay

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionFrames
import DGamma.CP4DeletionRelatedLifecycleEffectMap
import DGamma.CP4RecoveryEffectRespect
import DGamma.Unified
import Decidable.Equality

%default total

0 partialRelatedSymmetricPost :
  (eq : Equivalence state) ->
  PartialRelated state (relation eq) left right ->
  PartialRelated state (relation eq) right left
partialRelatedSymmetricPost eq PartialUndefined = PartialUndefined
partialRelatedSymmetricPost eq (PartialDefined related) =
  PartialDefined (symmetric eq related)

0 partialRelatedTransitivePost :
  (eq : Equivalence state) ->
  PartialRelated state (relation eq) first middle ->
  PartialRelated state (relation eq) middle last ->
  PartialRelated state (relation eq) first last
partialRelatedTransitivePost eq PartialUndefined PartialUndefined =
  PartialUndefined
partialRelatedTransitivePost eq (PartialDefined first) (PartialDefined second) =
  PartialDefined (transitive eq first second)

0 definedRelatedPost :
  PartialRelated state relation (Just left) (Just right) -> relation left right
definedRelatedPost (PartialDefined related) = related

0 partialRelatedReflexivePost :
  (eq : Equivalence state) -> (result : Maybe state) ->
  PartialRelated state (relation eq) result result
partialRelatedReflexivePost eq Nothing = PartialUndefined
partialRelatedReflexivePost eq (Just value) = PartialDefined (reflexive eq value)

0 orchestrationOriginsSame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  isLifecycleAction action = False -> (tag : RuleTag) ->
  (left, right : SystemState name key value world error) ->
  (state : EffectState name key value world) ->
  partialEffectMapFor nameEq keyEq action tag left state =
  partialEffectMapFor nameEq keyEq action tag right state
orchestrationOriginsSame nameEq keyEq (OInsert actor parent component) Refl tag
  left right state = Refl
orchestrationOriginsSame nameEq keyEq (ORetire actor) Refl tag left right state =
  Refl
orchestrationOriginsSame nameEq keyEq (ORemove actor) Refl tag left right state =
  Refl
orchestrationOriginsSame nameEq keyEq (LBegin actor) Refl tag left right state
  impossible
orchestrationOriginsSame nameEq keyEq (LAdvance actor) Refl tag left right state
  impossible
orchestrationOriginsSame nameEq keyEq (LDivert actor) Refl tag left right state
  impossible
orchestrationOriginsSame nameEq keyEq (LLeave actor) Refl tag left right state
  impossible
orchestrationOriginsSame nameEq keyEq (LUnload actor) Refl tag left right state
  impossible

0 actionFrame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState) ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (partialEffectMapFor nameEq keyEq action tag before
      (projectEffectState @{nameEq} before))
    (Just (projectEffectState @{nameEq} afterState))
actionFrame nameEq keyEq action tag before afterState checked =
  case actualTransitionEffectFrame nameEq keyEq action tag before afterState
    checked of
      MkActualEffectFrame frame => frame

||| Standard effect congruence for one orchestration head while controls remain
||| in the selected quotient. The evaluator map is origin-independent, so no
||| selected lifecycle equality is needed.
public export
0 postCloseOrchestrationEffects :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  isLifecycleAction action = False -> (tag : RuleTag) ->
  (leftBefore, leftAfter, rightBefore, rightAfter :
    SystemState name key value world error) ->
  checkedApplyAction @{nameEq} @{keyEq} action leftBefore =
    Just (tag, leftAfter) ->
  checkedApplyAction @{nameEq} @{keyEq} action rightBefore =
    Just (tag, rightAfter) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} leftBefore)
    (projectEffectState @{nameEq} rightBefore) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} leftAfter)
    (projectEffectState @{nameEq} rightAfter)
postCloseOrchestrationEffects nameEq keyEq action orchestration tag leftBefore
  leftAfter rightBefore rightAfter leftChecked rightChecked sourceRelated =
    let 0 leftFrame = actionFrame nameEq keyEq action tag leftBefore leftAfter
          leftChecked
        0 rightFrame = actionFrame nameEq keyEq action tag rightBefore rightAfter
          rightChecked
        0 inputRespect = partialEffectMapRespects nameEq keyEq action tag
          leftBefore leftAfter leftChecked (projectEffectState @{nameEq} leftBefore)
          (projectEffectState @{nameEq} rightBefore) sourceRelated
        0 originSame = orchestrationOriginsSame nameEq keyEq action orchestration
          tag leftBefore rightBefore (projectEffectState @{nameEq} rightBefore)
        0 atRightOrigin : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (partialEffectMapFor nameEq keyEq action tag leftBefore
            (projectEffectState @{nameEq} rightBefore))
          (partialEffectMapFor nameEq keyEq action tag rightBefore
            (projectEffectState @{nameEq} rightBefore))
        atRightOrigin = rewrite originSame in
          partialRelatedReflexivePost (EffectStateEquivalence keyEq)
            (partialEffectMapFor nameEq keyEq action tag rightBefore
            (projectEffectState @{nameEq} rightBefore))
    in definedRelatedPost
      (partialRelatedTransitivePost (EffectStateEquivalence keyEq)
        (partialRelatedSymmetricPost (EffectStateEquivalence keyEq) leftFrame)
        (partialRelatedTransitivePost (EffectStateEquivalence keyEq) inputRespect
          (partialRelatedTransitivePost (EffectStateEquivalence keyEq)
            atRightOrigin rightFrame)))

||| Lifecycle counterpart. Only the acting foreign owner needs full control
||| relatedness; the selected cell may retain the weaker static relation.
public export
0 postCloseLifecycleEffects :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (lifecycle : isLifecycleAction action = True) -> (tag : RuleTag) ->
  (leftBefore, leftAfter, rightBefore, rightAfter :
    SystemState name key value world error) ->
  checkedApplyAction @{nameEq} @{keyEq} action leftBefore =
    Just (tag, leftAfter) ->
  checkedApplyAction @{nameEq} @{keyEq} action rightBefore =
    Just (tag, rightAfter) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} leftBefore)
    (projectEffectState @{nameEq} rightBefore) ->
  (leftOwner, rightOwner : Fiber name key value world error) ->
  lookupFiber @{nameEq} (actionOwner action) (registry leftBefore) =
    Just leftOwner ->
  lookupFiber @{nameEq} (actionOwner action) (registry rightBefore) =
    Just rightOwner ->
  FiberControlRelated leftOwner rightOwner ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} leftAfter)
    (projectEffectState @{nameEq} rightAfter)
postCloseLifecycleEffects nameEq keyEq action lifecycle tag leftBefore leftAfter
  rightBefore rightAfter leftChecked rightChecked sourceRelated leftOwner
  rightOwner leftFound rightFound ownersRelated =
    let 0 leftFrame = actionFrame nameEq keyEq action tag leftBefore leftAfter
          leftChecked
        0 rightFrame = actionFrame nameEq keyEq action tag rightBefore rightAfter
          rightChecked
        0 inputRespect = partialEffectMapRespects nameEq keyEq action tag
          leftBefore leftAfter leftChecked (projectEffectState @{nameEq} leftBefore)
          (projectEffectState @{nameEq} rightBefore) sourceRelated
        0 originsRelated = relatedLifecyclePartialMapOutputsAtStates nameEq keyEq
          action lifecycle tag leftBefore rightBefore leftOwner rightOwner
          leftFound rightFound ownersRelated
          (projectEffectState @{nameEq} rightBefore)
    in definedRelatedPost
      (partialRelatedTransitivePost (EffectStateEquivalence keyEq)
        (partialRelatedSymmetricPost (EffectStateEquivalence keyEq) leftFrame)
        (partialRelatedTransitivePost (EffectStateEquivalence keyEq) inputRespect
          (partialRelatedTransitivePost (EffectStateEquivalence keyEq)
            originsRelated rightFrame)))
