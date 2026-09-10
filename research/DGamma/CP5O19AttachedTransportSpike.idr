module DGamma.CP5O19AttachedTransportSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O19AttachedPairsSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| An aligned native edge preserves the ENTIRE foreign fiber, not merely
||| the parent field or action label. All dictionaries come from alignment.
export
0 o19AlignedForeignFiber :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (controlled : name) ->
  {before, afterState : SystemState name key value world error} ->
  (step : Transition before afterState) ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions step NoTransitions) ->
  Not (controlled = actionOwner (transitionAction step)) ->
  lookupFiber {name} {key} {value} {world} {error} @{nameEq} controlled (registry afterState) =
    lookupFiber {name} {key} {value} {world} {error} @{nameEq} controlled (registry before)
o19AlignedForeignFiber {before} {afterState} nameEq keyEq controlled _
  (AlignedStep action tag checked NoTransitions AlignedEnd) distinct =
    systemLocalUpdateForeign nameEq controlled (actionOwner action) distinct before afterState
      (applyActionLocalUpdate nameEq keyEq action before afterState tag
        (checkedActionProjects nameEq keyEq action before afterState tag checked))

||| A right-hand child/root control finds the EXACT same fiber before the
||| left edge. Its parent, component and provision key are consequently not
||| reconstructed from the replay action. The action/tag equations belong to
||| the actual diamond returned by an R207 adapter.
export
0 o19RightControlBeforeSwap :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (controlled : name) ->
  {first, middle, last : SystemState name key value world error} ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber {name} {key} {value} {world} {error} @{nameEq} controlled (registry middle) = Just fiber ->
  Not (controlled = actionOwner (transitionAction left)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} controlled (registry first) = Just fiber,
   transitionAction (movedRight diamond) = transitionAction right,
   transitionTag (movedRight diamond) = transitionTag right)
o19RightControlBeforeSwap nameEq keyEq controlled _ right
  (AlignedStep action tag checked _ alignedRest) diamond fiber found distinct =
    (trans (sym (o19AlignedForeignFiber nameEq keyEq controlled
      (Fired nameEq keyEq action tag checked)
      (AlignedStep action tag checked NoTransitions AlignedEnd) distinct)) found,
     movedRightAction diamond, movedRightTag diamond)
