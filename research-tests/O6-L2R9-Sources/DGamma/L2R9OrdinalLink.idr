module DGamma.L2R9OrdinalLink

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3Attached
import DGamma.L2R7ReleaseDecode
import DGamma.L2R8SharedKey
import DGamma.L2R8ReleaseScan
import DGamma.L2R9OrdinalScan
import Data.List
import Data.List.Elem
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Erased head linkage at the actual observed isElem overlap. Each
||| successful shared-key packet corresponds to exactly one head ordinal.
export
0 overlapOrdinalLink : {key : Type} -> (keyEq : DecEq key) ->
  (left, right : List key) -> (seen : Bool) ->
  (0 equation : any (\item => isYes (isElem @{keyEq} item right)) left = seen) ->
  map (\shared => Z) (sharedKeysObserved keyEq left right seen equation) =
    overlapOrdinals keyEq left right seen equation
overlapOrdinalLink keyEq left right True equation = Refl
overlapOrdinalLink keyEq left right False equation = Refl

||| Head-parent linkage keeps the native occurrence and source proof. Only
||| the observed parent is eliminated; shared-key extraction is L2R8's own.
export
0 parentOrdinalLink : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (component : Component key value world error) ->
  (child : name) -> (fiber : Fiber name key value world error) ->
  (occurrence : LocatedActionOccurrence (ORemove child) trace) ->
  (0 atHead : locatedActionOrdinal occurrence = Z) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq}
    child (registry (actionBeforeState occurrence)) = Just fiber) ->
  (parent : Parent name) -> (0 equation : fiberParent fiber = parent) ->
  map (\release => locatedActionOrdinal (releaseOccurrence (snd release)))
    (releaseAtParent nameEq keyEq component child fiber occurrence found parent equation) =
  ordinalAtParent keyEq component fiber parent equation
parentOrdinalLink nameEq keyEq component child fiber occurrence atHead found Root equation = Refl
parentOrdinalLink {name} {key} {world} {error} {value} {trace}
  nameEq keyEq component child fiber occurrence atHead found (ChildOf actor) equation =
  trans (mapFusion
    {a = SharedKey (dependencies (componentProvisions (fiberComponent fiber)))
      (dependencies (componentProvisions component))}
    {b = (selected : name ** AttachedRelease name key world error value nameEq selected trace component)}
    {c = Nat}
    (\release => locatedActionOrdinal (releaseOccurrence (snd release)))
    (\shared => (actor ** MkAttachedRelease child fiber occurrence found equation
      (sharedKey shared) (inLeft shared) (inRight shared)))
    (sharedKeysObserved keyEq
      (dependencies (componentProvisions (fiberComponent fiber)))
      (dependencies (componentProvisions component))
      (any (\item => isYes (isElem @{keyEq} item (dependencies (componentProvisions component))))
        (dependencies (componentProvisions (fiberComponent fiber)))) Refl))
    (rewrite atHead in overlapOrdinalLink keyEq
      (dependencies (componentProvisions (fiberComponent fiber)))
      (dependencies (componentProvisions component))
      (any (\item => isYes (isElem @{keyEq} item (dependencies (componentProvisions component))))
        (dependencies (componentProvisions (fiberComponent fiber)))) Refl)

||| Lookup linkage eliminates the SAME observed source lookup exactly once.
export
0 lookupOrdinalLink : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (component : Component key value world error) -> (child : name) ->
  (occurrence : LocatedActionOccurrence (ORemove child) trace) ->
  (0 atHead : locatedActionOrdinal occurrence = Z) ->
  (found : Maybe (Fiber name key value world error)) ->
  (0 equation : lookupFiber {name} {key} {value} {world} {error} @{nameEq}
    child (registry (actionBeforeState occurrence)) = found) ->
  map (\release => locatedActionOrdinal (releaseOccurrence (snd release)))
    (releaseAtLookup nameEq keyEq component child occurrence found equation) =
  ordinalAtLookup nameEq keyEq component child (actionBeforeState occurrence) found equation
lookupOrdinalLink nameEq keyEq component child occurrence atHead Nothing equation = Refl
lookupOrdinalLink nameEq keyEq component child occurrence atHead (Just fiber) equation =
  parentOrdinalLink nameEq keyEq component child fiber occurrence atHead equation (fiberParent fiber) Refl
