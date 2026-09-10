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

||| The left control's original fiber survives the actual moved-right edge.
||| This consumes movedPairAligned from the real diamond, never an unchecked
||| early application. Exact fiber identity preserves parent AND provision.
export
0 o19LeftControlAfterSwap :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (controlled : name) ->
  {first, middle, last : SystemState name key value world error} ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber {name} {key} {value} {world} {error} @{nameEq} controlled (registry first) = Just fiber ->
  Not (controlled = actionOwner (transitionAction right)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} controlled (registry (swappedMiddle diamond)) = Just fiber,
   transitionAction (movedLeft diamond) = transitionAction left,
   transitionTag (movedLeft diamond) = transitionTag left)
o19LeftControlAfterSwap nameEq keyEq controlled left right
  (MkLocalRelationalDiamond movedMiddle movedEnd earlyRight lateLeft aligned rightAction rightTag
    leftAction leftTag rightActivation leftActivation rightOrchestration leftOrchestration safety effects controls wellFormed)
  fiber found distinct =
    case aligned of
      AlignedStep action tag checked _ tail =>
        (trans (o19AlignedForeignFiber nameEq keyEq controlled (Fired nameEq keyEq action tag checked)
          (AlignedStep action tag checked NoTransitions AlignedEnd)
          (\same => distinct (trans same (cong actionOwner rightAction)))) found,
         leftAction, leftTag)

||| Transfer ALL seven classes to an exact replay edge. Unlike action-word
||| relabelling, this consumes a genuine source-to-target lookup frame. The
||| ORIGINAL core is intentionally retained here; its change is separate.
export
0 o19AttachedEdgeAtReplay :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {actor : name} ->
  {coreFirst, coreLast, sourceBefore, sourceAfter, targetBefore, targetAfter : SystemState name key value world error} ->
  {core : Transitions coreFirst coreLast} ->
  (source : Transition sourceBefore sourceAfter) -> (target : Transition targetBefore targetAfter) ->
  transitionAction target = transitionAction source -> transitionActor target = transitionActor source ->
  ((controlled : name) -> (fiber : Fiber name key value world error) ->
    lookupFiber {name} {key} {value} {world} {error} @{nameEq} controlled (registry sourceBefore) = Just fiber ->
    lookupFiber {name} {key} {value} {world} {error} @{nameEq} controlled (registry targetBefore) = Just fiber) ->
  O19AttachedEdge name key world error value nameEq actor core source ->
  O19AttachedEdge name key world error value nameEq actor core target
o19AttachedEdgeAtReplay source target action owned frame (AttachedLifecycle lifecycle owner) =
  AttachedLifecycle (trans (cong isLifecycleAction action) lifecycle) (trans owned owner)
o19AttachedEdgeAtReplay source target action owned frame (AttachedChildInsert child component inserted) =
  AttachedChildInsert child component (trans action inserted)
o19AttachedEdgeAtReplay source target action owned frame (AttachedChildRetire child fiber found parent controlled) =
  AttachedChildRetire child fiber (frame child fiber found) parent (trans action controlled)
o19AttachedEdgeAtReplay source target action owned frame (AttachedChildRemove child fiber found parent controlled) =
  AttachedChildRemove child fiber (frame child fiber found) parent (trans action controlled)
o19AttachedEdgeAtReplay source target action owned frame (AttachedRootInsert root component priorRoots inserted forced) =
  AttachedRootInsert root component priorRoots (trans action inserted) forced
o19AttachedEdgeAtReplay source target action owned frame (AttachedRootRetire root fiber priorRoots bundled found parent controlled) =
  AttachedRootRetire root fiber priorRoots bundled (frame root fiber found) parent (trans action controlled)
o19AttachedEdgeAtReplay source target action owned frame (AttachedRootRemove root fiber priorRoots bundled found parent controlled) =
  AttachedRootRemove root fiber priorRoots bundled (frame root fiber found) parent (trans action controlled)

||| Relocate KeyReleased's REAL removal occurrence. The same released fiber
||| carries its parent, component and shared provision key to the new source;
||| a matching action without this exact lookup would not suffice.
export
0 o19AttachedReleaseAtReplay :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {actor : name} ->
  {first, last, replayFirst, replayLast : SystemState name key value world error} ->
  {core : Transitions first last} -> {replayCore : Transitions replayFirst replayLast} ->
  {component : Component key value world error} ->
  (release : AttachedRelease name key world error value nameEq actor core component) ->
  (replayOccurrence : LocatedActionOccurrence (ORemove (releasedChild release)) replayCore) ->
  lookupFiber {name} {key} {value} {world} {error} @{nameEq} (releasedChild release)
    (registry (actionBeforeState replayOccurrence)) = Just (releasedFiber release) ->
  AttachedRelease name key world error value nameEq actor replayCore component
o19AttachedReleaseAtReplay release replayOccurrence found =
  MkAttachedRelease (releasedChild release) (releasedFiber release) replayOccurrence found
    (releaseParent release) (sharedProvision release) (childDeclares release) (rootDeclares release)

||| Transport BOTH forcing reasons. KeyReleased consumes a located replay
||| occurrence and exact source fiber; EarlierForcedRoot keeps membership in
||| the SAME prior-root history. No guessed generation or final replay result.
export
0 o19AttachedReasonAtReplay :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {actor : name} ->
  {first, last, replayFirst, replayLast : SystemState name key value world error} ->
  {core : Transitions first last} -> {replayCore : Transitions replayFirst replayLast} ->
  {priorRoots : List name} -> {component : Component key value world error} ->
  ((release : AttachedRelease name key world error value nameEq actor core component) ->
    (replayOccurrence : LocatedActionOccurrence (ORemove (releasedChild release)) replayCore **
      lookupFiber {name} {key} {value} {world} {error} @{nameEq} (releasedChild release)
        (registry (actionBeforeState replayOccurrence)) = Just (releasedFiber release))) ->
  AttachedReason nameEq actor core priorRoots component ->
  AttachedReason nameEq actor replayCore priorRoots component
o19AttachedReasonAtReplay relocate (KeyReleased release) =
  case relocate release of
    (occurrence ** found) => KeyReleased (o19AttachedReleaseAtReplay release occurrence found)
o19AttachedReasonAtReplay relocate (EarlierForcedRoot earlier) = EarlierForcedRoot earlier

||| Reindex the seven edge classes by a genuinely replayed core. This is the
||| second half of transport, after o19AttachedEdgeAtReplay moved the edge.
||| Only the forcing-release occurrence map is consumed; prior-root histories
||| and every already-transported source lookup are kept unchanged.
export
0 o19AttachedEdgeChangeCore :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {actor : name} ->
  {first, last, replayFirst, replayLast, before, afterState : SystemState name key value world error} ->
  {core : Transitions first last} -> {replayCore : Transitions replayFirst replayLast} ->
  {step : Transition before afterState} ->
  ((component : Component key value world error) ->
    (release : AttachedRelease name key world error value nameEq actor core component) ->
    (replayOccurrence : LocatedActionOccurrence (ORemove (releasedChild release)) replayCore **
      lookupFiber {name} {key} {value} {world} {error} @{nameEq} (releasedChild release)
        (registry (actionBeforeState replayOccurrence)) = Just (releasedFiber release))) ->
  O19AttachedEdge name key world error value nameEq actor core step ->
  O19AttachedEdge name key world error value nameEq actor replayCore step
o19AttachedEdgeChangeCore relocate (AttachedLifecycle lifecycle owned) = AttachedLifecycle lifecycle owned
o19AttachedEdgeChangeCore relocate (AttachedChildInsert child component inserted) = AttachedChildInsert child component inserted
o19AttachedEdgeChangeCore relocate (AttachedChildRetire child fiber found parent controlled) =
  AttachedChildRetire child fiber found parent controlled
o19AttachedEdgeChangeCore relocate (AttachedChildRemove child fiber found parent controlled) =
  AttachedChildRemove child fiber found parent controlled
o19AttachedEdgeChangeCore relocate (AttachedRootInsert root component priorRoots inserted forced) =
  AttachedRootInsert root component priorRoots inserted (o19AttachedReasonAtReplay (relocate component) forced)
o19AttachedEdgeChangeCore relocate (AttachedRootRetire root fiber priorRoots bundled found parent controlled) =
  AttachedRootRetire root fiber priorRoots bundled found parent controlled
o19AttachedEdgeChangeCore relocate (AttachedRootRemove root fiber priorRoots bundled found parent controlled) =
  AttachedRootRemove root fiber priorRoots bundled found parent controlled
