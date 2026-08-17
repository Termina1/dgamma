module DGamma.CP4ProgressProgramBound

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Data.List
import Decidable.Equality

%default total

programEntry :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  Nat -> Binding name (FiberAt name key value world error) -> Bool
programEntry bound entry = programBoundedEntry bound entry

entriesOf :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  Registry name key value world error ->
  List (Binding name (FiberAt name key value world error))
entriesOf context = registryFibers context

0 andLeft : (left, right : Bool) -> left && right = True -> left = True
andLeft False right valid = case valid of Refl impossible
andLeft True right valid = Refl

0 andRight : (left, right : Bool) -> left && right = True -> right = True
andRight False right valid = case valid of Refl impossible
andRight True False valid = case valid of Refl impossible
andRight True True valid = Refl

0 andBoth : (left, right : Bool) -> left = True -> right = True ->
  left && right = True
andBoth False right leftTrue rightTrue = case leftTrue of Refl impossible
andBoth True right leftTrue rightTrue = rightTrue

0 allLookup :
  (nameEq : DecEq name) ->
  (predicate : Binding name (FiberAt name key value world error) -> Bool) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  allList predicate entries = True ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupEntries @{nameEq} selected entries = Just fiber ->
  predicate (Bind selected fiber) = True
allLookup nameEq predicate [] valid selected fiber found =
  case found of Refl impossible
allLookup nameEq predicate (Bind current observed :: rest) valid selected fiber
  found with (decEq @{nameEq} selected current)
  allLookup nameEq predicate (Bind selected observed :: rest) valid selected fiber
    found | Yes Refl = case justInjective found of Refl => andLeft _ _ valid
  allLookup nameEq predicate (Bind current observed :: rest) valid selected fiber
    found | No distinct = allLookup nameEq predicate rest (andRight _ _ valid)
      selected fiber found

0 allReplacePrograms :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (bound : Nat) -> (selected : name) ->
  (next : Fiber name key value world error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  allList (programBoundedEntry {name = name} {key = key} {value = value} {world = world} {error = error} bound) entries = True ->
  programBoundedEntry {name = name} {key = key} {value = value} {world = world} {error = error} bound (Bind selected next) = True ->
  allList (programBoundedEntry {name = name} {key = key} {value = value} {world = world} {error = error} bound)
    (replaceEntries @{nameEq} selected next entries) = True
allReplacePrograms nameEq bound selected next [] source nextBound = source
allReplacePrograms nameEq bound selected next (Bind current observed :: rest)
  source nextBound with (decEq @{nameEq} selected current)
  allReplacePrograms nameEq bound current next (Bind current observed :: rest)
    source nextBound | Yes Refl = andBoth _ _ nextBound (andRight _ _ source)
  allReplacePrograms nameEq bound selected next (Bind current observed :: rest)
    source nextBound | No distinct = andBoth _ _ (andLeft _ _ source)
      (allReplacePrograms nameEq bound selected next rest
        (andRight _ _ source) nextBound)

0 allDeletePrograms :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (bound : Nat) -> (selected : name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  allList (programBoundedEntry {name = name} {key = key} {value = value} {world = world} {error = error} bound) entries = True ->
  allList (programBoundedEntry {name = name} {key = key} {value = value} {world = world} {error = error} bound)
    (deleteEntries @{nameEq} selected entries) = True
allDeletePrograms nameEq bound selected [] source = source
allDeletePrograms nameEq bound selected (Bind current observed :: rest) source
  with (decEq @{nameEq} selected current)
  allDeletePrograms nameEq bound current (Bind current observed :: rest) source |
    Yes Refl = andRight _ _ source
  allDeletePrograms nameEq bound selected (Bind current observed :: rest) source |
    No distinct = andBoth _ _ (andLeft _ _ source)
      (allDeletePrograms nameEq bound selected rest (andRight _ _ source))

0 replaceRegistryEntries :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (next : Fiber name key value world error) ->
  (context : Registry name key value world error) ->
  entriesOf {name = name} {key = key} {value = value} {world = world} {error = error} (replaceBinding @{nameEq} selected next context) =
    replaceEntries @{nameEq} selected next (entriesOf {name = name} {key = key} {value = value} {world = world} {error = error} context)
replaceRegistryEntries nameEq selected next (MkCoeffectContext entries unique) =
  Refl

0 deleteRegistryEntries :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (context : Registry name key value world error) ->
  entriesOf {name = name} {key = key} {value = value} {world = world} {error = error} (deleteBinding @{nameEq} selected context) =
    deleteEntries @{nameEq} selected (entriesOf {name = name} {key = key} {value = value} {world = world} {error = error} context)
deleteRegistryEntries nameEq selected (MkCoeffectContext entries unique) = Refl

0 registryUpdatePreservesPrograms :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (bound : Nat) -> (actor : name) ->
  (source, target : Registry name key value world error) ->
  RegistryLocalUpdate name key world error value nameEq actor source target ->
  (presentFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor source = Just presentFiber ->
  allList (programBoundedEntry {name = name} {key = key} {value = value} {world = world} {error = error} bound) (entriesOf {name = name} {key = key} {value = value} {world = world} {error = error} source) = True ->
  allList (programBoundedEntry {name = name} {key = key} {value = value} {world = world} {error = error} bound) (entriesOf {name = name} {key = key} {value = value} {world = world} {error = error} target) = True
registryUpdatePreservesPrograms nameEq bound actor source _
  (LocalInsert inserted absent) presentFiber present programs =
    void (nothingIsNotJust (trans (sym absent) present))
registryUpdatePreservesPrograms nameEq bound actor source _
  (LocalReplace next {oldFiber} {oldFound} {staticComponent}) presentFiber
  present programs =
    let oldBound = allLookup nameEq (programBoundedEntry {name = name} {key = key} {value = value} {world = world} {error = error} bound)
          (entriesOf {name = name} {key = key} {value = value} {world = world} {error = error} source) programs actor oldFiber
          (lookupFiberEntries nameEq actor oldFiber source oldFound)
        nextBound : (programEntry {name = name} {key = key} {value = value}
          {world = world} {error = error} bound (Bind actor next) = True)
        nextBound = rewrite staticComponent in oldBound
    in replace
      {p = \entries => allList (programBoundedEntry {name = name} {key = key} {value = value} {world = world} {error = error} bound) entries = True}
      (sym (replaceRegistryEntries nameEq actor next source))
      (allReplacePrograms nameEq bound actor next (entriesOf {name = name} {key = key} {value = value} {world = world} {error = error} source)
        programs nextBound)
registryUpdatePreservesPrograms nameEq bound actor source _ LocalDelete
  presentFiber present programs =
    replace
      {p = \entries => allList (programBoundedEntry {name = name} {key = key} {value = value} {world = world} {error = error} bound) entries = True}
      (sym (deleteRegistryEntries nameEq actor source))
      (allDeletePrograms nameEq bound actor (entriesOf {name = name} {key = key} {value = value} {world = world} {error = error} source) programs)

0 lifecycleActorPresent :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  isLifecycleAction action = True ->
  (fiber : Fiber name key value world error **
    lookupFiber @{nameEq} (actionOwner action) (registry before) = Just fiber)
lifecycleActorPresent nameEq keyEq (OInsert actor parent component) before
  afterState tag raw lifecycle = case lifecycle of Refl impossible
lifecycleActorPresent nameEq keyEq (ORetire actor) before afterState tag raw
  lifecycle = case lifecycle of Refl impossible
lifecycleActorPresent nameEq keyEq (ORemove actor) before afterState tag raw
  lifecycle = case lifecycle of Refl impossible
lifecycleActorPresent nameEq keyEq (LBegin actor)
  (MkSystemState ambient fibers) afterState tag raw lifecycle
  with (lookupFiber @{nameEq} actor fibers) proof found
  lifecycleActorPresent nameEq keyEq (LBegin actor)
    (MkSystemState ambient fibers) afterState tag raw lifecycle | Nothing =
      void (nothingIsNotJust raw)
  lifecycleActorPresent nameEq keyEq (LBegin actor)
    (MkSystemState ambient fibers) afterState tag raw lifecycle | Just fiber =
      (fiber ** Refl)
lifecycleActorPresent nameEq keyEq (LAdvance actor)
  (MkSystemState ambient fibers) afterState tag raw lifecycle
  with (lookupFiber @{nameEq} actor fibers) proof found
  lifecycleActorPresent nameEq keyEq (LAdvance actor)
    (MkSystemState ambient fibers) afterState tag raw lifecycle | Nothing =
      void (nothingIsNotJust raw)
  lifecycleActorPresent nameEq keyEq (LAdvance actor)
    (MkSystemState ambient fibers) afterState tag raw lifecycle | Just fiber =
      (fiber ** Refl)
lifecycleActorPresent nameEq keyEq (LDivert actor)
  (MkSystemState ambient fibers) afterState tag raw lifecycle
  with (lookupFiber @{nameEq} actor fibers) proof found
  lifecycleActorPresent nameEq keyEq (LDivert actor)
    (MkSystemState ambient fibers) afterState tag raw lifecycle | Nothing =
      void (nothingIsNotJust raw)
  lifecycleActorPresent nameEq keyEq (LDivert actor)
    (MkSystemState ambient fibers) afterState tag raw lifecycle | Just fiber =
      (fiber ** Refl)
lifecycleActorPresent nameEq keyEq (LLeave actor)
  (MkSystemState ambient fibers) afterState tag raw lifecycle
  with (lookupFiber @{nameEq} actor fibers) proof found
  lifecycleActorPresent nameEq keyEq (LLeave actor)
    (MkSystemState ambient fibers) afterState tag raw lifecycle | Nothing =
      void (nothingIsNotJust raw)
  lifecycleActorPresent nameEq keyEq (LLeave actor)
    (MkSystemState ambient fibers) afterState tag raw lifecycle | Just fiber =
      (fiber ** Refl)
lifecycleActorPresent nameEq keyEq (LUnload actor)
  (MkSystemState ambient fibers) afterState tag raw lifecycle
  with (lookupFiber @{nameEq} actor fibers) proof found
  lifecycleActorPresent nameEq keyEq (LUnload actor)
    (MkSystemState ambient fibers) afterState tag raw lifecycle | Nothing =
      void (nothingIsNotJust raw)
  lifecycleActorPresent nameEq keyEq (LUnload actor)
    (MkSystemState ambient fibers) afterState tag raw lifecycle | Just fiber =
      (fiber ** Refl)

||| Lifecycle actions never introduce a new component, so the declared-program
||| bound needed by later L-Begin steps is invariant along a lifecycle trace.
public export
0 lifecycleTransitionPreservesProgramsBoundedBy :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (bound : Nat) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  isLifecycleAction action = True ->
  programsBoundedBy bound before = True ->
  programsBoundedBy bound afterState = True
lifecycleTransitionPreservesProgramsBoundedBy nameEq keyEq bound action tag
  (MkSystemState sourceWorld source) (MkSystemState targetWorld target)
  checked lifecycle programs =
    let raw = checkedActionProjects nameEq keyEq action
          (MkSystemState sourceWorld source) (MkSystemState targetWorld target) tag checked
        (presentFiber ** present) = lifecycleActorPresent nameEq keyEq action
          (MkSystemState sourceWorld source) (MkSystemState targetWorld target)
          tag raw lifecycle
        update = applyActionLocalUpdate nameEq keyEq action
          (MkSystemState sourceWorld source) (MkSystemState targetWorld target) tag raw
        sourcePrograms = trans
          (sym (programsBoundedByEquation bound (MkSystemState sourceWorld source)))
          programs
        targetPrograms = registryUpdatePreservesPrograms nameEq bound
          (actionOwner action) source target (systemRegistryUpdate update)
          presentFiber present sourcePrograms
    in trans (programsBoundedByEquation bound
      (MkSystemState targetWorld target)) targetPrograms
