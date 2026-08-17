module DGamma.CP4ProgressBound

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

0 andLeftP : (left, right : Bool) -> left && right = True -> left = True
andLeftP False right valid = case valid of Refl impossible
andLeftP True right valid = Refl

0 andRightP : (left, right : Bool) -> left && right = True -> right = True
andRightP False right valid = case valid of Refl impossible
andRightP True False valid = case valid of Refl impossible
andRightP True True valid = Refl

0 andBothP : (left, right : Bool) -> left = True -> right = True ->
  left && right = True
andBothP False right leftTrue rightTrue = case leftTrue of Refl impossible
andBothP True right leftTrue rightTrue = rightTrue

0 allListLookupP :
  (nameEq : DecEq name) ->
  (predicate : Binding name (FiberAt name key value world error) -> Bool) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  allList predicate entries = True ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupEntries @{nameEq} selected entries = Just fiber ->
  predicate (Bind selected fiber) = True
allListLookupP nameEq predicate [] valid selected fiber found =
  case found of Refl impossible
allListLookupP nameEq predicate (Bind current observed :: rest) valid selected
  fiber found with (decEq @{nameEq} selected current)
  allListLookupP nameEq predicate (Bind selected observed :: rest) valid selected
    fiber found | Yes Refl =
      case justInjective found of
        Refl => andLeftP _ _ valid
  allListLookupP nameEq predicate (Bind current observed :: rest) valid selected
    fiber found | No distinct =
      allListLookupP nameEq predicate rest (andRightP _ _ valid) selected fiber
        found

public export
0 continuationBoundedAtLookup :
  (nameEq : DecEq name) -> (bound : Nat) ->
  (state : SystemState name key value world error) ->
  continuationsBoundedBy bound state = True ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry state) = Just fiber ->
  fiberContinuationBoundedBy bound fiber = True
continuationBoundedAtLookup nameEq bound
  (MkSystemState ambient (MkCoeffectContext entries unique)) bounded selected
  fiber found = allListLookupP nameEq (continuationBoundedEntry bound) entries
    bounded selected fiber found

0 allReplaceContinuation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (bound : Nat) -> (selected : name) ->
  (next : Fiber name key value world error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  allList (continuationBoundedEntry {name = name} {key = key} {value = value} {world = world} {error = error} bound) entries = True ->
  fiberContinuationBoundedBy bound next = True ->
  allList (continuationBoundedEntry {name = name} {key = key} {value = value} {world = world} {error = error} bound)
    (replaceEntries @{nameEq} selected next entries) = True
allReplaceContinuation nameEq bound selected next [] source nextBound = source
allReplaceContinuation nameEq bound selected next
  (Bind current observed :: rest) source nextBound
  with (decEq @{nameEq} selected current)
  allReplaceContinuation nameEq bound current next
    (Bind current observed :: rest) source nextBound | Yes Refl =
      andBothP _ _ nextBound (andRightP _ _ source)
  allReplaceContinuation nameEq bound selected next
    (Bind current observed :: rest) source nextBound | No distinct =
      andBothP _ _ (andLeftP _ _ source)
        (allReplaceContinuation nameEq bound selected next rest
          (andRightP _ _ source) nextBound)

0 allDeleteContinuation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (bound : Nat) -> (selected : name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  allList (continuationBoundedEntry {name = name} {key = key} {value = value} {world = world} {error = error} bound) entries = True ->
  allList (continuationBoundedEntry {name = name} {key = key} {value = value} {world = world} {error = error} bound)
    (deleteEntries @{nameEq} selected entries) = True
allDeleteContinuation nameEq bound selected [] source = source
allDeleteContinuation nameEq bound selected (Bind current observed :: rest)
  source with (decEq @{nameEq} selected current)
  allDeleteContinuation nameEq bound current (Bind current observed :: rest)
    source | Yes Refl = andRightP _ _ source
  allDeleteContinuation nameEq bound selected (Bind current observed :: rest)
    source | No distinct = andBothP _ _ (andLeftP _ _ source)
      (allDeleteContinuation nameEq bound selected rest (andRightP _ _ source))

0 allInsertContinuation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (bound : Nat) -> (selected : name) ->
  (next : Fiber name key value world error) ->
  (context : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} selected context = Nothing) ->
  allList (continuationBoundedEntry {name = name} {key = key} {value = value} {world = world} {error = error} bound)
    (registryFibers {value = value} {world = world} {error = error}
      context) = True ->
  fiberContinuationBoundedBy bound next = True ->
  allList (continuationBoundedEntry {name = name} {key = key} {value = value} {world = world} {error = error} bound)
    (registryFibers {value = value} {world = world} {error = error}
      (insertBinding @{nameEq} {key = name}
        {value = FiberAt name key value world error}
        selected next context absent)) = True
allInsertContinuation nameEq bound selected next
  (MkCoeffectContext entries unique) absent source nextBound =
    andBothP _ _ nextBound source

0 natLEDropLeft : (n, bound : Nat) -> S n <= bound = True -> n <= bound = True
natLEDropLeft n Z valid = case valid of Refl impossible
natLEDropLeft Z (S bound) valid = Refl
natLEDropLeft (S n) (S bound) valid = natLEDropLeft n bound valid

0 continuationUpdateBounded :
  (bound : Nat) -> (old, updated : Fiber name key value world error) ->
  length (componentProgram (fiberComponent old)) <= bound = True ->
  fiberContinuationBoundedBy bound old = True ->
  ContinuationUpdate old updated ->
  fiberContinuationBoundedBy bound updated = True
continuationUpdateBounded bound old updated programBound oldBound update =
  let 0 oldCheck :
        (continuationLengthCheck bound (fiberContinuationLength old) = True)
      oldCheck = trans (sym (fiberContinuationBoundedByEquation bound old))
        oldBound
  in trans (fiberContinuationBoundedByEquation bound updated)
    (case update of
      ContinuationPreserved same =>
        trans (cong (continuationLengthCheck bound) same) oldCheck
      ContinuationStopped stopped =>
        trans (cong (continuationLengthCheck bound) stopped) Refl
      ContinuationAdvanced remainingLength oldLength updatedLength =>
        let 0 sourceNat : (S remainingLength <= bound = True)
            sourceNat = trans
              (sym (cong (continuationLengthCheck bound) oldLength)) oldCheck
            0 targetNat : (remainingLength <= bound = True)
            targetNat = natLEDropLeft remainingLength bound sourceNat
        in trans (cong (continuationLengthCheck bound) updatedLength)
          targetNat
      ContinuationRestarted restarted =>
        trans (cong (continuationLengthCheck bound) restarted) programBound)

0 registryFibersReplaceP :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (next : Fiber name key value world error) ->
  (context : Registry name key value world error) ->
  registryFibers {value = value} {world = world} {error = error}
    (replaceBinding @{nameEq} {key = name}
      {value = FiberAt name key value world error} selected next context) =
    replaceEntries @{nameEq} {key = name}
      {value = FiberAt name key value world error} selected next
      (registryFibers {value = value} {world = world} {error = error} context)
registryFibersReplaceP nameEq selected next (MkCoeffectContext entries unique) =
  Refl

0 registryFibersDeleteP :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (context : Registry name key value world error) ->
  registryFibers {value = value} {world = world} {error = error}
    (deleteBinding @{nameEq} {key = name}
      {value = FiberAt name key value world error} selected context) =
    deleteEntries @{nameEq} {key = name}
      {value = FiberAt name key value world error} selected
      (registryFibers {value = value} {world = world} {error = error} context)
registryFibersDeleteP nameEq selected (MkCoeffectContext entries unique) = Refl

0 registryUpdatePreservesContinuationBound :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (bound : Nat) -> (actor : name) ->
  (source, target : Registry name key value world error) ->
  (update : RegistryLocalUpdate name key world error value nameEq actor source
    target) ->
  allList (programBoundedEntry {name = name} {key = key} {value = value}
    {world = world} {error = error} bound)
    (registryFibers {value = value} {world = world} {error = error} source) =
      True ->
  allList (continuationBoundedEntry {name = name} {key = key} {value = value}
    {world = world} {error = error} bound)
    (registryFibers {value = value} {world = world} {error = error} source) =
      True ->
  allList (continuationBoundedEntry {name = name} {key = key} {value = value}
    {world = world} {error = error} bound)
    (registryFibers {value = value} {world = world} {error = error} target) =
      True
registryUpdatePreservesContinuationBound nameEq bound actor source _
  (LocalInsert inserted absent {insertedContinuationEmpty}) programs
  continuations =
    let 0 insertedBound = trans
          (fiberContinuationBoundedByEquation bound inserted)
          (trans (cong (continuationLengthCheck bound)
            insertedContinuationEmpty) Refl)
    in allInsertContinuation nameEq bound actor inserted source absent
      continuations insertedBound
registryUpdatePreservesContinuationBound nameEq bound actor source _
  (LocalReplace next {oldFiber} {oldFound} {staticComponent}
    {continuationUpdate}) programs continuations =
      let 0 oldProgram = allListLookupP nameEq (programBoundedEntry bound)
            (registryFibers source) programs actor oldFiber
            (lookupFiberEntries nameEq actor oldFiber source oldFound)
          0 oldContinuation = allListLookupP nameEq
            (continuationBoundedEntry bound) (registryFibers source)
            continuations actor oldFiber
            (lookupFiberEntries nameEq actor oldFiber source oldFound)
          0 nextBound = continuationUpdateBounded bound oldFiber next oldProgram
            oldContinuation continuationUpdate
      in replace
        {p = \entries => allList
          (continuationBoundedEntry bound) entries = True}
        (sym (registryFibersReplaceP nameEq actor next source))
        (allReplaceContinuation nameEq bound actor next
          (registryFibers source) continuations nextBound)
registryUpdatePreservesContinuationBound nameEq bound actor source _
  (LocalDelete {oldFiber} {oldFound}) programs continuations =
    replace
      {p = \entries => allList (continuationBoundedEntry bound) entries = True}
      (sym (registryFibersDeleteP nameEq actor source))
      (allDeleteContinuation nameEq bound actor (registryFibers source)
        continuations)

0 selectedProgramBounded :
  (nameEq : DecEq name) -> (bound : Nat) ->
  (state : SystemState name key value world error) ->
  programsBoundedBy bound state = True ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry state) = Just fiber ->
  length (componentProgram (fiberComponent fiber)) <= bound = True
selectedProgramBounded nameEq bound
  (MkSystemState ambient (MkCoeffectContext entries unique)) bounded selected
  fiber found = allListLookupP nameEq (programBoundedEntry bound)
    entries bounded selected fiber found

||| Approved CP4 Finding-5 repair invariant. Every successful evaluator rule
||| preserves the current continuation bound, provided every declared program
||| in its source is bounded. `applyActionLocalUpdate` exhausts all ten rules;
||| its continuation metadata distinguishes preserve/stop/advance/restart.
public export
0 transitionPreservesContinuationsBoundedBy :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (bound : Nat) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState) ->
  programsBoundedBy bound before = True ->
  continuationsBoundedBy bound before = True ->
  continuationsBoundedBy bound afterState = True
transitionPreservesContinuationsBoundedBy nameEq keyEq bound action tag
  before@(MkSystemState sourceWorld source)
  afterState@(MkSystemState targetWorld target) checked programs continuations =
    let 0 raw = checkedActionProjects nameEq keyEq action before afterState tag
          checked
        0 update = applyActionLocalUpdate nameEq keyEq action before afterState
          tag raw
        0 programEntries = trans
          (sym (programsBoundedByEquation bound before)) programs
        0 continuationEntries = trans
          (sym (continuationsBoundedByEquation bound before)) continuations
        0 targetEntries = registryUpdatePreservesContinuationBound nameEq bound
          (actionOwner action) source target (systemRegistryUpdate update)
          programEntries continuationEntries
    in trans (continuationsBoundedByEquation bound afterState) targetEntries
