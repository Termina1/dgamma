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
