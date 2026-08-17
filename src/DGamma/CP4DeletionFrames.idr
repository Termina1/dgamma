module DGamma.CP4DeletionFrames

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionFrameInsert
import DGamma.CP4DeletionFrameRetire
import DGamma.CP4DeletionFrameRemove
import DGamma.CP4DeletionFrameBegin
import DGamma.CP4DeletionFrameAdvanceDispatch
import DGamma.CP4DeletionFrameDivert
import DGamma.CP4DeletionFrameLeave
import DGamma.CP4DeletionFrameUnload
import Decidable.Equality

%default total

||| Exhaustive relational soundness of every actual-forward Definition-60
||| generator against its checked Table-1 LTS target.
public export
0 actualTransitionEffectFrame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  ActualEffectFrame nameEq keyEq action tag before afterState
actualTransitionEffectFrame nameEq keyEq action tag before afterState checked =
  let raw = checkedActionProjects nameEq keyEq action before afterState tag checked
  in case action of
    OInsert actor parent component =>
      insertActualEffectFrame nameEq keyEq actor parent component before afterState
        tag raw
    ORetire actor =>
      retireActualEffectFrame nameEq keyEq actor before afterState tag raw
    ORemove actor =>
      removeActualEffectFrame nameEq keyEq actor before afterState tag raw
    LBegin actor =>
      beginActualEffectFrame nameEq keyEq actor before afterState tag raw
    LAdvance actor =>
      advanceActualEffectFrame nameEq keyEq actor before afterState tag raw
    LDivert actor =>
      divertActualEffectFrame nameEq keyEq actor before afterState tag raw
    LLeave actor =>
      leaveActualEffectFrame nameEq keyEq actor before afterState tag raw
    LUnload actor =>
      unloadActualEffectFrame nameEq keyEq actor before afterState tag raw
