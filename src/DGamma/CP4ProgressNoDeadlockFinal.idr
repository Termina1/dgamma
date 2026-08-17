module DGamma.CP4ProgressNoDeadlockFinal

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP4ProgressFinite
import DGamma.CP4ProgressReliance
import DGamma.CP4ProgressUnloadingShape
import DGamma.CP4ProgressUnloadingDescent
import Control.WellFounded
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

0 scanLifecycleProgress :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} state = True ->
  PrecedenceAcyclic {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq state ->
  (scan : List (Binding name (FiberAt name key value world error))) ->
  ((entry : Binding name (FiberAt name key value world error)) ->
    Elem entry scan -> Elem entry
      (registryFibers {value = value} {world = world} {error = error}
        (registry state))) ->
  Either
    (allRecursive
      (quietEntryFor @{nameEq} @{keyEq} {value = value} {world = world}
        {error = error} (registry state)) scan = True)
    (LifecycleMove {name = name} {key = key} {value = value} {world = world}
      {error = error} nameEq keyEq state)
scanLifecycleProgress nameEq keyEq (MkSystemState ambient fibers) wellFormed
  acyclic [] subset =
  Left Refl
scanLifecycleProgress nameEq keyEq
  (MkSystemState ambient (MkCoeffectContext full unique)) wellFormed acyclic
  (Bind actor
    (MkFiber component parent retiredFlag table (Inactive (Just err))) :: rest)
  subset =
    case scanLifecycleProgress nameEq keyEq
      (MkSystemState ambient (MkCoeffectContext full unique)) wellFormed acyclic
      rest (\entry, present => subset entry (There present)) of
        Left tailQuiet => Left (rewrite tailQuiet in Refl)
        Right move => Right move
scanLifecycleProgress nameEq keyEq
  (MkSystemState ambient (MkCoeffectContext full unique)) wellFormed acyclic
  (Bind actor
    (MkFiber component parent retiredFlag table (Inactive Nothing)) :: rest)
  subset
  with (targetFiber @{nameEq} @{keyEq}
    (MkFiber component parent retiredFlag table (Inactive Nothing))
    (MkCoeffectContext full unique)) proof targetResult
  scanLifecycleProgress nameEq keyEq
    (MkSystemState ambient (MkCoeffectContext full unique)) wellFormed acyclic
    (Bind actor
      (MkFiber component parent retiredFlag table (Inactive Nothing)) :: rest)
    subset | Nothing =
      case scanLifecycleProgress nameEq keyEq
        (MkSystemState ambient (MkCoeffectContext full unique)) wellFormed acyclic
        rest (\entry, present => subset entry (There present)) of
          Left tailQuiet => Left tailQuiet
          Right move => Right move
  scanLifecycleProgress nameEq keyEq
    (MkSystemState ambient (MkCoeffectContext full unique)) wellFormed acyclic
    (Bind actor
      (MkFiber component parent retiredFlag table (Inactive Nothing)) :: rest)
    subset | Just target =
      let 0 found : (lookupFiber @{nameEq} actor
            (MkCoeffectContext full unique) = Just
              (MkFiber component parent retiredFlag table (Inactive Nothing)))
          found = lookupEntryFromElem nameEq full unique
            (subset (Bind actor
              (MkFiber component parent retiredFlag table (Inactive Nothing)))
              Here)
      in Right (beginLifecycleMove nameEq keyEq
        (MkSystemState ambient (MkCoeffectContext full unique)) wellFormed actor
        component parent retiredFlag table found target targetResult)
scanLifecycleProgress nameEq keyEq
  (MkSystemState ambient (MkCoeffectContext full unique)) wellFormed acyclic
  (Bind actor
    (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator view)) :: rest) subset =
    let 0 found : (lookupFiber @{nameEq} actor
          (MkCoeffectContext full unique) = Just
            (MkFiber component parent retiredFlag table
              (Reloading remaining accumulator view)))
        found = lookupEntryFromElem nameEq full unique
          (subset (Bind actor
            (MkFiber component parent retiredFlag table
              (Reloading remaining accumulator view))) Here)
    in Right (reloadingLifecycleMove nameEq keyEq
      (MkSystemState ambient (MkCoeffectContext full unique)) wellFormed actor
      component parent retiredFlag table remaining accumulator view found)
scanLifecycleProgress nameEq keyEq
  (MkSystemState ambient (MkCoeffectContext full unique)) wellFormed acyclic
  (Bind actor
    (MkFiber component parent retiredFlag table
      (Active accumulator view)) :: rest) subset
  with (targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq}
      (MkFiber component parent retiredFlag table (Active accumulator view))
      (MkCoeffectContext full unique)) view) proof matches
  scanLifecycleProgress nameEq keyEq
    (MkSystemState ambient (MkCoeffectContext full unique)) wellFormed acyclic
    (Bind actor
      (MkFiber component parent retiredFlag table
        (Active accumulator view)) :: rest) subset | True =
      case scanLifecycleProgress nameEq keyEq
        (MkSystemState ambient (MkCoeffectContext full unique)) wellFormed acyclic
        rest (\entry, present => subset entry (There present)) of
          Left tailQuiet => Left tailQuiet
          Right move => Right move
  scanLifecycleProgress nameEq keyEq
    (MkSystemState ambient (MkCoeffectContext full unique)) wellFormed acyclic
    (Bind actor
      (MkFiber component parent retiredFlag table
        (Active accumulator view)) :: rest) subset | False =
      let 0 found : (lookupFiber @{nameEq} actor
            (MkCoeffectContext full unique) = Just
              (MkFiber component parent retiredFlag table
                (Active accumulator view)))
          found = lookupEntryFromElem nameEq full unique
            (subset (Bind actor
              (MkFiber component parent retiredFlag table
                (Active accumulator view))) Here)
      in Right (leaveLifecycleMove nameEq keyEq
        (MkSystemState ambient (MkCoeffectContext full unique)) wellFormed actor
        component parent retiredFlag table accumulator view found matches)
scanLifecycleProgress nameEq keyEq
  (MkSystemState ambient (MkCoeffectContext full unique)) wellFormed acyclic
  (Bind actor
    (MkFiber component parent retiredFlag table
      (Unloading accumulator view outcome)) :: rest) subset =
    let 0 found : (lookupFiber @{nameEq} actor
          (MkCoeffectContext full unique) = Just
            (MkFiber component parent retiredFlag table
              (Unloading accumulator view outcome)))
        found = lookupEntryFromElem nameEq full unique
          (subset (Bind actor
            (MkFiber component parent retiredFlag table
              (Unloading accumulator view outcome))) Here)
        0 accessible : Accessible
          (PrecedenceSuccessor {name = name} {key = key} {value = value}
            {world = world} {error = error} nameEq
            (MkSystemState ambient (MkCoeffectContext full unique))) actor
        accessible = precedenceSuccessorAccessible nameEq
          (MkSystemState ambient (MkCoeffectContext full unique)) acyclic actor
          (MkFiber component parent retiredFlag table
            (Unloading accumulator view outcome)) found
    in Right (unloadingLifecycleMoveAccessible nameEq keyEq ambient
      (MkCoeffectContext full unique) wellFormed actor
      (MkFiber component parent retiredFlag table
        (Unloading accumulator view outcome)) found UnloadingNow accessible)

||| Constructive no-deadlock core of paper Theorem 66. A blocked Unloading
||| fiber follows an actual reliance/precedence edge; finite acyclicity supplies
||| accessibility, so the descent reaches an unloadable or otherwise movable
||| consumer.
public export
0 progressNoDeadlockAt :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} state = True ->
  PrecedenceAcyclic {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq state ->
  quiet @{nameEq} @{keyEq} state = False ->
  LifecycleMove {name = name} {key = key} {value = value} {world = world}
    {error = error} nameEq keyEq state
progressNoDeadlockAt nameEq keyEq
  state@(MkSystemState ambient fibers) wellFormed acyclic notQuiet =
    case scanLifecycleProgress nameEq keyEq (MkSystemState ambient fibers)
      wellFormed acyclic (registryFibers fibers) (\entry, present => present) of
      Left allQuiet => case trans (sym notQuiet) allQuiet of Refl impossible
      Right move => move
