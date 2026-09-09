module DGamma.L2R8ReleaseScan

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3Attached
import DGamma.L2R7ReleaseDecode
import DGamma.L2R8SharedKey
import Data.List
import Data.List.Elem
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Observed parent boundary over the isElem release scan; agreement with
||| scanReleaseOrdinals open. Every emitted release owns an actual located
||| native Remove and the child-source lookup, parent, and shared declaration.
public export
0 releaseAtParent : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (component : Component key value world error) ->
  (child : name) -> (fiber : Fiber name key value world error) ->
  (occurrence : LocatedActionOccurrence (ORemove child) trace) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq}
    child (registry (actionBeforeState occurrence)) = Just fiber) ->
  (parent : Parent name) -> (0 equation : fiberParent fiber = parent) ->
  List (actor : name ** AttachedRelease name key world error value nameEq actor trace component)
releaseAtParent nameEq keyEq component child fiber occurrence found Root equation = []
releaseAtParent nameEq keyEq component child fiber occurrence found (ChildOf actor) equation =
  map (\shared => (actor ** MkAttachedRelease child fiber occurrence found equation
    (sharedKey shared) (inLeft shared) (inRight shared)))
    (sharedKeysObserved keyEq
      (dependencies (componentProvisions (fiberComponent fiber)))
      (dependencies (componentProvisions component))
      (any (\item => isYes (isElem @{keyEq} item (dependencies (componentProvisions component))))
        (dependencies (componentProvisions (fiberComponent fiber)))) Refl)

||| Observed lookup boundary over the isElem release scan; agreement with
||| scanReleaseOrdinals open. No two-head lookup pattern or reconstructed view.
public export
0 releaseAtLookup : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (component : Component key value world error) -> (child : name) ->
  (occurrence : LocatedActionOccurrence (ORemove child) trace) ->
  (found : Maybe (Fiber name key value world error)) ->
  (0 equation : lookupFiber {name} {key} {value} {world} {error} @{nameEq}
    child (registry (actionBeforeState occurrence)) = found) ->
  List (actor : name ** AttachedRelease name key world error value nameEq actor trace component)
releaseAtLookup nameEq keyEq component child occurrence Nothing equation = []
releaseAtLookup nameEq keyEq component child occurrence (Just fiber) equation =
  releaseAtParent nameEq keyEq component child fiber occurrence equation (fiberParent fiber) Refl

||| Head-action classification over the isElem release scan; agreement with
||| scanReleaseOrdinals open. Only ORemove emits; every lookup is fully indexed.
public export
0 releaseAtAction : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (component : Component key value world error) ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (action : Action name key value world error) ->
  (0 equation : transitionAction step = action) ->
  List (actor : name ** AttachedRelease name key world error value nameEq actor
    (MoreTransitions step rest) component)
releaseAtAction nameEq keyEq component step rest (OInsert child parent inserted) equation = []
releaseAtAction nameEq keyEq component step rest (ORetire child) equation = []
releaseAtAction {name} {key} {world} {error} {value} {first} {middle}
  nameEq keyEq component step rest (ORemove child) equation =
  releaseAtLookup nameEq keyEq component child
    (MkLocatedActionOccurrence first middle NoTransitions step rest equation Refl)
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry first)) Refl
releaseAtAction nameEq keyEq component step rest (LBegin actor) equation = []
releaseAtAction nameEq keyEq component step rest (LAdvance actor) equation = []
releaseAtAction nameEq keyEq component step rest (LDivert actor) equation = []
releaseAtAction nameEq keyEq component step rest (LUnload actor) equation = []
releaseAtAction nameEq keyEq component step rest (LLeave actor) equation = []

||| Exact native occurrence embedding over the isElem release scan; agreement
||| with scanReleaseOrdinals open. Child/source/parent/key remain the SAME.
public export
0 releaseThroughHead : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {nameEq : DecEq name} -> {component : Component key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (actor : name ** AttachedRelease name key world error value nameEq actor rest component) ->
  (actor : name ** AttachedRelease name key world error value nameEq actor (MoreTransitions step rest) component)
releaseThroughHead step rest (actor ** release) = (actor ** MkAttachedRelease
  (releasedChild release) (releasedFiber release)
  (MkLocatedActionOccurrence
    (actionBeforeState (releaseOccurrence release)) (actionAfterState (releaseOccurrence release))
    (MoreTransitions step (beforeActionOccurrence (releaseOccurrence release)))
    (locatedTransition (releaseOccurrence release)) (afterActionOccurrence (releaseOccurrence release))
    (locatedAction (releaseOccurrence release))
    (cong (MoreTransitions step) (actionOccurrenceDecomposition (releaseOccurrence release))))
  (releaseFound release) (releaseParent release) (sharedProvision release)
  (childDeclares release) (rootDeclares release))

||| GENERAL proof-carrying release enumeration over the isElem release scan;
||| agreement with scanReleaseOrdinals open (releaseScanAgrees). Enumerates
||| the entire native trail; compare filtered ordinals below a cut to the old
||| bounded scan. Actual occurrences, own-child parents, and shared keys are
||| constructed by structural trail recursion, never supplied as a decoder.
||| Quantity zero: constructive proof extraction, not a runtime scan export.
public export
0 scanObservedReleases : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (component : Component key value world error) ->
  AvailabilityTrace name key world error value trace ->
  List (actor : name ** AttachedRelease name key world error value nameEq actor trace component)
scanObservedReleases nameEq keyEq component (AvailabilityEnd state) = []
scanObservedReleases nameEq keyEq component (AvailabilityStep source (Fired ne ke action tag checked) rest later) =
  releaseAtAction nameEq keyEq component (Fired ne ke action tag checked) rest action Refl ++
  map (releaseThroughHead (Fired ne ke action tag checked) rest)
    (scanObservedReleases nameEq keyEq component later)
