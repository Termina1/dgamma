module DGamma.Calculus

import DGamma.Core
import DGamma.Effects
import DGamma.Coeffects
import DGamma.Unified
import Decidable.Equality
import Data.List
import Data.List.Elem
import Data.Maybe

%default total

||| Definition 51/49: one partial, failing, witnessed iterator step.
public export
record StepEffect (world, error : Type) where
  constructor MkStepEffect
  runStepEffect : world -> Either error (world, world -> world)
  0 stepWitness : (before, after : world) -> (undo : world -> world) ->
    runStepEffect before = Right (after, undo) -> undo after = before

||| Definitions 43/51: a component's declarations and finite effect iterator.
public export
record Component (key : Type) (value : key -> Type)
                 (world, error : Type) where
  constructor MkComponent
  componentDependencies : CoeffectSpec key
  componentProvisions : CoeffectSpec key
  providedValues : CoeffectContext key value
  componentProgram : List (StepEffect world error)
  0 provisionSound : (k : key) ->
    Elem k (bindingKeys (bindings providedValues)) ->
    Elem k (dependencies componentProvisions)

||| A committed view is intrinsically total on exactly the dependency list.
public export
data View : (name : Type) -> List key -> Type where
  EmptyView : View name []
  ProviderView : name -> View name rest -> View name (k :: rest)

public export
viewProviders : View name deps -> List name
viewProviders EmptyView = []
viewProviders (ProviderView provider rest) = provider :: viewProviders rest

public export
viewEq : DecEq name => View name deps -> View name deps -> Bool
viewEq EmptyView EmptyView = True
viewEq (ProviderView left ls) (ProviderView right rs) =
  case decEq left right of
    Yes Refl => viewEq ls rs
    No _ => False

public export
viewContains : DecEq name => name -> View name deps -> Bool
viewContains wanted EmptyView = False
viewContains wanted (ProviderView provider rest) =
  case decEq wanted provider of
    Yes Refl => True
    No _ => viewContains wanted rest

public export
viewLookup : DecEq key => (wanted : key) -> (deps : List key) ->
  View name deps -> Maybe name
viewLookup wanted [] EmptyView = Nothing
viewLookup wanted (k :: ks) (ProviderView provider rest) with (decEq wanted k)
  viewLookup k (k :: ks) (ProviderView provider rest) | (Yes Refl) = Just provider
  viewLookup wanted (k :: ks) (ProviderView provider rest) | (No _) =
    viewLookup wanted ks rest

||| Definition 49: full lifecycle with transition states and failure outcome.
public export
data Lifecycle : (world, error, name : Type) -> List key -> Type where
  Inactive : Maybe error -> Lifecycle world error name deps
  Reloading : List (StepEffect world error) -> (world -> world) ->
              View name deps -> Lifecycle world error name deps
  Active : (world -> world) -> View name deps ->
           Lifecycle world error name deps
  Unloading : (world -> world) -> View name deps -> Maybe error ->
              Lifecycle world error name deps

public export
installed : Lifecycle world error name deps -> Bool
installed (Inactive _) = False
installed _ = True

public export
isActive : Lifecycle world error name deps -> Bool
isActive (Active _ _) = True
isActive _ = False

public export
committed : Lifecycle world error name deps -> Maybe (View name deps)
committed (Inactive _) = Nothing
committed (Reloading _ _ view) = Just view
committed (Active _ view) = Just view
committed (Unloading _ view _) = Just view

public export
data Parent name = Root | ChildOf name

||| Definition 44: fiber. The lifecycle view is indexed by the component's
||| exact dependency list.
public export
data Fiber : (name, key : Type) -> (value : key -> Type) ->
             (world, error : Type) -> Type where
  MkFiber : (component : Component key value world error) ->
            (parent : Parent name) -> (isRetired : Bool) ->
            Lifecycle world error name
              (dependencies (componentDependencies component)) ->
            Fiber name key value world error

public export
fiberComponent : Fiber name key value world error -> Component key value world error
fiberComponent (MkFiber component _ _ _) = component

public export
fiberParent : Fiber name key value world error -> Parent name
fiberParent (MkFiber _ parent _ _) = parent

public export
retired : Fiber name key value world error -> Bool
retired (MkFiber _ _ isRetired _) = isRetired

public export
fiberLifecycle : (fiber : Fiber name key value world error) ->
  Lifecycle world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
fiberLifecycle (MkFiber component parent isRetired lifecycle) = lifecycle

public export
freshFiber : Component key value world error -> Parent name ->
  Fiber name key value world error
freshFiber component parent = MkFiber component parent False (Inactive Nothing)

public export
setFiberLifecycle : (fiber : Fiber name key value world error) ->
  Lifecycle world error name
    (dependencies (componentDependencies (fiberComponent fiber))) ->
  Fiber name key value world error
setFiberLifecycle (MkFiber component parent retired old) lifecycle =
  MkFiber component parent retired lifecycle

public export
retireFiber : Fiber name key value world error -> Fiber name key value world error
retireFiber (MkFiber component parent retired lifecycle) =
  MkFiber component parent True lifecycle

public export
FiberAt : (name, key : Type) -> (value : key -> Type) ->
  (world, error : Type) -> name -> Type
FiberAt name key value world error _ = Fiber name key value world error

||| Definition 45: finite, name-unique registry.
public export
Registry : (name, key : Type) -> (value : key -> Type) ->
  (world, error : Type) -> Type
Registry name key value world error =
  CoeffectContext name (FiberAt name key value world error)

public export
record SystemState (name, key : Type) (value : key -> Type)
                   (world, error : Type) where
  constructor MkSystemState
  worldState : world
  registry : Registry name key value world error

public export
lookupFiber : DecEq name => (n : name) ->
  Registry name key value world error -> Maybe (Fiber name key value world error)
lookupFiber = lookupBinding

public export
registryFibers : Registry name key value world error ->
  List (Binding name (FiberAt name key value world error))
registryFibers = bindings

public export
updateFiber : DecEq name => name ->
  (Fiber name key value world error -> Fiber name key value world error) ->
  Registry name key value world error -> Registry name key value world error
updateFiber n update fibers = case lookupFiber n fibers of
  Nothing => fibers
  Just fiber => replaceBinding n (update fiber) fibers

public export
parentPresent : DecEq name => Parent name -> Registry name key value world error -> Bool
parentPresent Root fibers = True
parentPresent (ChildOf parent) fibers = isJust (lookupFiber parent fibers)

public export
hasChild : DecEq name => name -> Registry name key value world error -> Bool
hasChild parent fibers = any isChild (registryFibers fibers)
  where
  isChild : Binding name (FiberAt name key value world error) -> Bool
  isChild (Bind child fiber) = case fiberParent fiber of
    Root => False
    ChildOf candidate => case decEq parent candidate of
      Yes Refl => True
      No _ => False

public export
providerIn : DecEq name => DecEq key => key ->
  List (Binding name (FiberAt name key value world error)) -> Maybe name
providerIn k [] = Nothing
providerIn k (Bind n fiber :: rest) =
  if isActive (fiberLifecycle fiber) &&
     memberKey k (providedValues (fiberComponent fiber))
    then Just n
    else providerIn k rest

public export
providerOf : DecEq name => DecEq key => key ->
  Registry name key value world error -> Maybe name
providerOf k fibers = providerIn k (registryFibers fibers)

||| Definition 45's derived coeffect context, retaining the provider identity
||| separately through target views.
public export
activeCoeffectsFrom : DecEq name => DecEq key =>
  List (Binding name (FiberAt name key value world error)) ->
  CoeffectContext key value
activeCoeffectsFrom [] = emptyContext
activeCoeffectsFrom (Bind n fiber :: rest) =
  if isActive (fiberLifecycle fiber)
    then mergeProvided (providedValues (fiberComponent fiber))
                       (activeCoeffectsFrom rest)
    else activeCoeffectsFrom rest
  where
  mergeProvided : CoeffectContext key value -> CoeffectContext key value ->
                  CoeffectContext key value
  mergeProvided left right = foldr insertIfFresh right (bindings left)
    where
    insertIfFresh : Binding key value -> CoeffectContext key value ->
                    CoeffectContext key value
    insertIfFresh (Bind k v) table = case setFresh k v table of
      Nothing => table
      Just applied => coeffectAfter applied

public export
activeCoeffects : DecEq name => DecEq key =>
  Registry name key value world error -> CoeffectContext key value
activeCoeffects fibers = activeCoeffectsFrom (registryFibers fibers)

public export
resolveView : DecEq name => DecEq key => (deps : List key) ->
  Registry name key value world error -> Maybe (View name deps)
resolveView [] fibers = Just EmptyView
resolveView (k :: ks) fibers = case providerOf k fibers of
  Nothing => Nothing
  Just provider => map (ProviderView provider) (resolveView ks fibers)

||| Definition 46: target view.
public export
targetFiber : DecEq name => DecEq key =>
  (fiber : Fiber name key value world error) ->
  Registry name key value world error ->
  Maybe (View name (dependencies
    (componentDependencies (fiberComponent fiber))))
targetFiber fiber fibers =
  if retired fiber
    then Nothing
    else resolveView (dependencies (componentDependencies (fiberComponent fiber))) fibers

public export
data SomeView : Type -> Type where
  MkSomeView : View name deps -> SomeView name

public export
targetAt : DecEq name => DecEq key => name ->
  SystemState name key value world error -> Maybe (SomeView name)
targetAt name state = case lookupFiber name (registry state) of
  Nothing => Nothing
  Just fiber => map MkSomeView (targetFiber fiber (registry state))

public export
targetMatches : DecEq name => Maybe (View name deps) -> View name deps -> Bool
targetMatches Nothing view = False
targetMatches (Just target) view = viewEq target view

||| Definition 50: relied upon by another installed fiber.
public export
reliedOnBy : DecEq name => name -> name ->
  List (Binding name (FiberAt name key value world error)) -> Bool
reliedOnBy provider self [] = False
reliedOnBy provider self (Bind n fiber :: rest) =
  let different = case decEq n self of Yes Refl => False; No _ => True
      sees = case committed (fiberLifecycle fiber) of
        Nothing => False
        Just view => viewContains provider view
   in (different && installed (fiberLifecycle fiber) && sees) ||
      reliedOnBy provider self rest

public export
relied : DecEq name => name -> Registry name key value world error -> Bool
relied n fibers = reliedOnBy n n (registryFibers fibers)

public export
quietFiber : DecEq name => DecEq key =>
  (fiber : Fiber name key value world error) ->
  Registry name key value world error -> Bool
quietFiber fiber fibers = case fiberLifecycle fiber of
  Inactive (Just _) => True
  Inactive Nothing => isNothing (targetFiber fiber fibers)
  Active accumulator view => targetMatches (targetFiber fiber fibers) view
  _ => False

public export
quiet : DecEq name => DecEq key => SystemState name key value world error -> Bool
quiet state = all quietEntry (registryFibers (registry state))
  where
  quietEntry : Binding name (FiberAt name key value world error) -> Bool
  quietEntry (Bind _ fiber) = quietFiber fiber (registry state)

public export
elemDec : DecEq a => a -> List a -> Bool
elemDec wanted [] = False
elemDec wanted (x :: xs) = case decEq wanted x of
  Yes Refl => True
  No _ => elemDec wanted xs

public export
provisionOverlap : DecEq key => CoeffectSpec key -> CoeffectSpec key -> Bool
provisionOverlap left right = any (\k => elemDec k (dependencies right))
                                  (dependencies left)

public export
provisionsDisjointFrom : DecEq key => CoeffectSpec key ->
  List (Binding name (FiberAt name key value world error)) -> Bool
provisionsDisjointFrom provision [] = True
provisionsDisjointFrom provision (Bind _ fiber :: rest) =
  not (provisionOverlap provision
    (componentProvisions (fiberComponent fiber))) &&
  provisionsDisjointFrom provision rest

||| The ten rule names in Table 1.
public export
data RuleTag = OInsertTag | ORetireTag | ORemoveTag |
               LBeginTag | LIterTag | LFinishTag | LDivertTag |
               LRaiseTag | LLeaveTag | LUnloadTag

public export
data Action : (name, key : Type) -> (value : key -> Type) ->
              (world, error : Type) -> Type where
  OInsert : name -> Parent name -> Component key value world error ->
            Action name key value world error
  ORetire : name -> Action name key value world error
  ORemove : name -> Action name key value world error
  LBegin : name -> Action name key value world error
  LAdvance : name -> Action name key value world error
  LDivert : name -> Action name key value world error
  LLeave : name -> Action name key value world error
  LUnload : name -> Action name key value world error

||| Definition 47's registration primitive, exposed through the same checked
||| O-Insert/O-Retire actions as external orchestration. A registering iterator
||| may submit the first action and retain the second as its inverse.
public export
record Registration (name, key : Type) (value : key -> Type)
                    (world, error : Type) where
  constructor MkRegistration
  registrationForward : Action name key value world error
  registrationInverse : Action name key value world error

public export
registration : name -> Parent name -> Component key value world error ->
  Registration name key value world error
registration n parent component =
  MkRegistration (OInsert n parent component) (ORetire n)

||| Definition 48 is enforced structurally in this runtime model: an iterator
||| step receives only `world`, never the registry or another fiber. The paper's
||| permitted own-table mutation is represented by the component's immutable
||| `providedValues`, which becomes observable only in `Active`.
public export
ConfinedStep : Type -> Type -> Type
ConfinedStep = StepEffect

public export
isInactive : Lifecycle world error name deps -> Bool
isInactive (Inactive _) = True
isInactive _ = False

||| Executable operational semantics for Sections 4.2–4.3.
public export
applyAction : DecEq name => DecEq key =>
  Action name key value world error ->
  SystemState name key value world error ->
  Maybe (RuleTag, SystemState name key value world error)
applyAction (OInsert n parent component) state =
  if parentPresent parent (registry state) &&
     provisionsDisjointFrom (componentProvisions component)
       (registryFibers (registry state))
    then case setFresh n (freshFiber component parent) (registry state) of
      Nothing => Nothing
      Just applied => Just (OInsertTag,
        MkSystemState (worldState state) (coeffectAfter applied))
    else Nothing
applyAction (ORetire n) state = case lookupFiber n (registry state) of
  Nothing => Nothing
  Just fiber => Just (ORetireTag,
    MkSystemState (worldState state) (updateFiber n retireFiber (registry state)))
applyAction (ORemove n) state = case lookupFiber n (registry state) of
  Nothing => Nothing
  Just fiber =>
    if retired fiber && isInactive (fiberLifecycle fiber) &&
       not (hasChild n (registry state))
      then Just (ORemoveTag,
        MkSystemState (worldState state) (deleteBinding n (registry state)))
      else Nothing
applyAction (LBegin n) state = case lookupFiber n (registry state) of
  Nothing => Nothing
  Just fiber => case fiberLifecycle fiber of
    Inactive Nothing => case targetFiber fiber (registry state) of
      Nothing => Nothing
      Just view => Just (LBeginTag,
        MkSystemState (worldState state)
          (replaceBinding n
            (setFiberLifecycle fiber
              (Reloading (componentProgram (fiberComponent fiber)) id view))
            (registry state)))
    _ => Nothing
applyAction (LAdvance n) state = case lookupFiber n (registry state) of
  Nothing => Nothing
  Just fiber => case fiberLifecycle fiber of
    Reloading [] accumulator view => Just (LFinishTag,
      MkSystemState (worldState state)
        (replaceBinding n (setFiberLifecycle fiber (Active accumulator view))
          (registry state)))
    Reloading (step :: rest) accumulator view =>
      case runStepEffect step (worldState state) of
        Left err => Just (LRaiseTag,
          MkSystemState (worldState state)
            (replaceBinding n
              (setFiberLifecycle fiber (Unloading accumulator view (Just err)))
              (registry state)))
        Right (nextWorld, undo) =>
          let nextAccumulator = accumulator . undo in
          if targetMatches (targetFiber fiber (registry state)) view
            then case rest of
              [] => Just (LFinishTag,
                MkSystemState nextWorld
                  (replaceBinding n
                    (setFiberLifecycle fiber (Active nextAccumulator view))
                    (registry state)))
              _ => Just (LIterTag,
                MkSystemState nextWorld
                  (replaceBinding n
                    (setFiberLifecycle fiber
                      (Reloading rest nextAccumulator view))
                    (registry state)))
            else Just (LDivertTag,
              MkSystemState nextWorld
                (replaceBinding n
                  (setFiberLifecycle fiber
                    (Unloading nextAccumulator view Nothing))
                  (registry state)))
    _ => Nothing
applyAction (LDivert n) state = case lookupFiber n (registry state) of
  Nothing => Nothing
  Just fiber => case fiberLifecycle fiber of
    Reloading remaining accumulator view =>
      if targetMatches (targetFiber fiber (registry state)) view
        then Nothing
        else Just (LDivertTag,
          MkSystemState (worldState state)
            (replaceBinding n
              (setFiberLifecycle fiber (Unloading accumulator view Nothing))
              (registry state)))
    _ => Nothing
applyAction (LLeave n) state = case lookupFiber n (registry state) of
  Nothing => Nothing
  Just fiber => case fiberLifecycle fiber of
    Active accumulator view =>
      if targetMatches (targetFiber fiber (registry state)) view
        then Nothing
        else Just (LLeaveTag,
          MkSystemState (worldState state)
            (replaceBinding n
              (setFiberLifecycle fiber (Unloading accumulator view Nothing))
              (registry state)))
    _ => Nothing
applyAction (LUnload n) state = case lookupFiber n (registry state) of
  Nothing => Nothing
  Just fiber => case fiberLifecycle fiber of
    Unloading accumulator view outcome =>
      if relied n (registry state)
        then Nothing
        else Just (LUnloadTag,
          MkSystemState (accumulator (worldState state))
            (replaceBinding n (setFiberLifecycle fiber (Inactive outcome))
              (registry state)))
    _ => Nothing

||| Definition 53: transition as an indexed inductive family. Its constructor
||| carries the executable rule equation; no unvalidated transition exists.
public export
data Transition : SystemState name key value world error ->
                  SystemState name key value world error -> Type where
  Fired : (nameEq : DecEq name) -> (keyEq : DecEq key) ->
          (action : Action name key value world error) -> (tag : RuleTag) ->
          applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
          Transition before afterState

public export
data Transitions : SystemState name key value world error ->
                   SystemState name key value world error -> Type where
  NoTransitions : Transitions state state
  MoreTransitions : Transition first middle -> Transitions middle finalState ->
                    Transitions first finalState

public export
transitionAction : {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> Action name key value world error
transitionAction (Fired nameEq keyEq action tag equation) = action

public export
transitionTag : {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> RuleTag
transitionTag (Fired nameEq keyEq action tag equation) = tag

||| An executable trace snapshot used by episode extraction.
public export
record Snapshot (name, key : Type) (value : key -> Type)
                (world, error : Type) where
  constructor MkSnapshot
  snapshotState : SystemState name key value world error

public export
installedAt : DecEq name => name ->
  SystemState name key value world error -> Bool
installedAt n state = case lookupFiber n (registry state) of
  Nothing => False
  Just fiber => installed (fiberLifecycle fiber)

||| Definition 53: maximal installed intervals, represented as nonempty lists of
||| consecutive states. This function is directly executable on logged states.
public export
episodes : DecEq name => name ->
  List (SystemState name key value world error) ->
  List (List (SystemState name key value world error))
episodes n states = go states []
  where
  flush : List (SystemState name key value world error) ->
          List (List (SystemState name key value world error)) ->
          List (List (SystemState name key value world error))
  flush [] done = done
  flush current done = reverse current :: done

  go : List (SystemState name key value world error) ->
       List (SystemState name key value world error) ->
       List (List (SystemState name key value world error))
  go [] current = reverse (flush current [])
  go (state :: rest) current =
    if installedAt n state
      then go rest (state :: current)
      else case current of
        [] => go rest []
        _ => reverse current :: go rest []
