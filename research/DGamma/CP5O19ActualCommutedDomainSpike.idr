module DGamma.CP5O19ActualCommutedDomainSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import DGamma.CP4DeletionFrameCore
import DGamma.CP5O19CommutedDomainSpike
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Primitive ACTUAL-forward constructor projection, pointwise rather than
||| an equality of functions. No computed replay/diamond builder is observed.
export
0 o19ActualForwardMapAt :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, sourceFinal, before, afterState : SystemState name key value world error} ->
  {trace : Transitions initial sourceFinal} -> {actor : name} ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  (occurs : OccursIn (Fired {before} {afterState} nameEq keyEq action tag checked) trace) ->
  (ownerSame : actionOwner action = actor) -> (state : EffectState name key value world) ->
  (runTraceEffectTransformation
    (TraceGenerator (ActualForwardGenerator before afterState nameEq keyEq action tag checked occurs ownerSame)) state =
   partialEffectMapFor nameEq keyEq action tag before state)
o19ActualForwardMapAt nameEq keyEq action tag checked occurs ownerSame state = Refl
