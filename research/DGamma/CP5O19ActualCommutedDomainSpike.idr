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

||| Genuine actual-pair commutation capital, at the captured source maps.
||| This is ONLY the sublemma exposed by A25; it does not retry that failed
||| early-run consumer and does not assert checked right applicability.
export
0 o19ActualPairMapCommutes :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (leftAction, rightAction : Action name key value world error) ->
  (leftTag, rightTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first = Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq} rightAction middle = Just (rightTag, finalState)) ->
  Not (actionOwner leftAction = actionOwner rightAction) ->
  TraceIndependent name key world error value keyEq
    (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq leftAction leftTag leftChecked)
      (MoreTransitions (Fired {before = middle} {afterState = finalState} nameEq keyEq rightAction rightTag rightChecked) NoTransitions)) ->
  PartialCommute (EffectStateEquivalence keyEq)
    (partialEffectMapFor nameEq keyEq leftAction leftTag first)
    (partialEffectMapFor nameEq keyEq rightAction rightTag middle)
o19ActualPairMapCommutes {name} {key} {world} {error} {value} {first} {middle} {finalState}
  nameEq keyEq leftAction rightAction leftTag rightTag leftChecked rightChecked distinct independent =
    o19PartialCommuteMapsTransport (EffectState name key value world) (EffectStateEquivalence keyEq)
      (runTraceEffectTransformation
        (TraceGenerator (ActualForwardGenerator {trace = (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq leftAction leftTag leftChecked) (MoreTransitions (Fired {before = middle} {afterState = finalState} nameEq keyEq rightAction rightTag rightChecked) NoTransitions))} first middle nameEq keyEq leftAction leftTag leftChecked OccursHere Refl)))
      (partialEffectMapFor nameEq keyEq leftAction leftTag first)
      (runTraceEffectTransformation
        (TraceGenerator (ActualForwardGenerator {trace = (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq leftAction leftTag leftChecked) (MoreTransitions (Fired {before = middle} {afterState = finalState} nameEq keyEq rightAction rightTag rightChecked) NoTransitions))} middle finalState nameEq keyEq rightAction rightTag rightChecked (OccursLater OccursHere) Refl)))
      (partialEffectMapFor nameEq keyEq rightAction rightTag middle)
      (o19ActualForwardMapAt {trace = (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq leftAction leftTag leftChecked) (MoreTransitions (Fired {before = middle} {afterState = finalState} nameEq keyEq rightAction rightTag rightChecked) NoTransitions))} nameEq keyEq leftAction leftTag leftChecked OccursHere Refl)
      (o19ActualForwardMapAt {trace = (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq leftAction leftTag leftChecked) (MoreTransitions (Fired {before = middle} {afterState = finalState} nameEq keyEq rightAction rightTag rightChecked) NoTransitions))} nameEq keyEq rightAction rightTag rightChecked (OccursLater OccursHere) Refl)
      (generatedMonoidsCommute independent (actionOwner leftAction) (actionOwner rightAction) distinct
        (TraceGenerator (ActualForwardGenerator {trace = (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq leftAction leftTag leftChecked) (MoreTransitions (Fired {before = middle} {afterState = finalState} nameEq keyEq rightAction rightTag rightChecked) NoTransitions))} first middle nameEq keyEq leftAction leftTag leftChecked OccursHere Refl))
        (TraceGenerator (ActualForwardGenerator {trace = (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq leftAction leftTag leftChecked) (MoreTransitions (Fired {before = middle} {afterState = finalState} nameEq keyEq rightAction rightTag rightChecked) NoTransitions))} middle finalState nameEq keyEq rightAction rightTag rightChecked (OccursLater OccursHere) Refl)))

||| Explicit-argument elimination for an actual frame producer's result.
||| This exposes no new semantic assumption and does not instantiate the
||| exhausted A25 early-run theorem. Run rebasing remains future work.
export
0 o19ActualFrameRelated :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  ActualEffectFrame nameEq keyEq action tag before afterState ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (partialEffectMapFor nameEq keyEq action tag before (projectEffectState @{nameEq} before))
    (Just (projectEffectState @{nameEq} afterState))
o19ActualFrameRelated nameEq keyEq action tag before afterState (MkActualEffectFrame related) = related
