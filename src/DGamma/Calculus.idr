module DGamma.Calculus

import DGamma.Core
import DGamma.Coeffects
import Decidable.Equality
import Data.List
import Data.List.Elem
import Data.Maybe

%default total

||| A fiber-owned dynamic table whose domain is confined to its declaration.
public export
record OwnedTable (key : Type) (value : key -> Type)
                  (provision : CoeffectSpec key) where
  constructor MkOwnedTable
  ownedValues : CoeffectContext key value
  0 ownedSound : (k : key) ->
    Elem k (bindingKeys (bindings ownedValues)) ->
    Elem k (dependencies provision)

public export
emptyOwned : OwnedTable key value provision
emptyOwned = MkOwnedTable emptyContext (\k, present => absurd present)

||| The only state a component step may mutate: ambient state and its own table.
public export
record LocalState (key : Type) (value : key -> Type) (world : Type)
                  (provision : CoeffectSpec key) where
  constructor MkLocalState
  localWorld : world
  localTable : OwnedTable key value provision

||| A total, ordered capability for exactly the declared dependency keys.
public export
data DepValues : (key : Type) -> (value : key -> Type) -> List key -> Type where
  NoDepValues : DepValues key value []
  OneDepValue : value k -> DepValues key value rest ->
                DepValues key value (k :: rest)

public export
depValueAt : DecEq key => (wanted : key) -> (deps : List key) ->
  DepValues key value deps -> Maybe (value wanted)
depValueAt wanted [] NoDepValues = Nothing
depValueAt wanted (k :: ks) (OneDepValue v rest) with (decEq wanted k)
  depValueAt k (k :: ks) (OneDepValue v rest) | (Yes Refl) = Just v
  depValueAt wanted (k :: ks) (OneDepValue v rest) | (No _) =
    depValueAt wanted ks rest

||| Definitions 48/51: one capability-confined, partial, failing iterator step.
||| Its inverse is witnessed at the exact local application state.
public export
record StepEffect (key : Type) (value : key -> Type) (world, error : Type)
                  (deps : List key) (provision : CoeffectSpec key) where
  constructor MkStepEffect
  runStepEffect : DepValues key value deps ->
                  LocalState key value world provision ->
                  Either error
                    (LocalState key value world provision,
                     LocalState key value world provision ->
                       LocalState key value world provision)
  0 stepWitness : (capability : DepValues key value deps) ->
    (before, after : LocalState key value world provision) ->
    (undo : LocalState key value world provision ->
            LocalState key value world provision) ->
    runStepEffect capability before = Right (after, undo) ->
    undo after = before

||| Definition 43: declarations plus a finite failing effect iterator.
public export
record Component (key : Type) (value : key -> Type)
                 (world, error : Type) where
  constructor MkComponent
  componentDependencies : CoeffectSpec key
  componentProvisions : CoeffectSpec key
  componentProgram : List (StepEffect key value world error
    (dependencies componentDependencies) componentProvisions)

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

||| Definition 49. Accumulators restore both ambient state and the acting
||| fiber's dynamic table, while no other registry field is in their capability.
public export
data Lifecycle : (key : Type) -> (value : key -> Type) ->
  (world, error, name : Type) -> (deps : List key) ->
  (provision : CoeffectSpec key) -> Type where
  Inactive : Maybe error ->
    Lifecycle key value world error name deps provision
  Reloading : List (StepEffect key value world error deps provision) ->
              (LocalState key value world provision ->
               LocalState key value world provision) ->
              View name deps ->
              Lifecycle key value world error name deps provision
  Active : (LocalState key value world provision ->
            LocalState key value world provision) ->
           View name deps ->
           Lifecycle key value world error name deps provision
  Unloading : (LocalState key value world provision ->
               LocalState key value world provision) ->
              View name deps -> Maybe error ->
              Lifecycle key value world error name deps provision

public export
installed : Lifecycle key value world error name deps provision -> Bool
installed (Inactive _) = False
installed _ = True

public export
isActive : Lifecycle key value world error name deps provision -> Bool
isActive (Active _ _) = True
isActive _ = False

public export
committed : Lifecycle key value world error name deps provision ->
  Maybe (View name deps)
committed (Inactive _) = Nothing
committed (Reloading _ _ view) = Just view
committed (Active _ view) = Just view
committed (Unloading _ view _) = Just view

public export
data Parent name = Root | ChildOf name

||| Definition 44: a fiber owns its changing table. Lifecycle indices are tied
||| to the declarations of the immutable component.
public export
data Fiber : (name, key : Type) -> (value : key -> Type) ->
             (world, error : Type) -> Type where
  MkFiber : (component : Component key value world error) ->
            (parent : Parent name) -> (isRetired : Bool) ->
            (table : OwnedTable key value (componentProvisions component)) ->
            Lifecycle key value world error name
              (dependencies (componentDependencies component))
              (componentProvisions component) ->
            Fiber name key value world error

public export
fiberComponent : Fiber name key value world error -> Component key value world error
fiberComponent (MkFiber component _ _ _ _) = component

public export
fiberParent : Fiber name key value world error -> Parent name
fiberParent (MkFiber _ parent _ _ _) = parent

public export
retired : Fiber name key value world error -> Bool
retired (MkFiber _ _ flag _ _) = flag

public export
fiberTable : (fiber : Fiber name key value world error) ->
  OwnedTable key value (componentProvisions (fiberComponent fiber))
fiberTable (MkFiber _ _ _ table _) = table

public export
fiberLifecycle : (fiber : Fiber name key value world error) ->
  Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))
fiberLifecycle (MkFiber _ _ _ _ lifecycle) = lifecycle

public export
freshFiber : Component key value world error -> Parent name ->
  Fiber name key value world error
freshFiber component parent =
  MkFiber component parent False emptyOwned (Inactive Nothing)

public export
setFiberRuntime : (fiber : Fiber name key value world error) ->
  (table : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)) ->
  Fiber name key value world error
setFiberRuntime (MkFiber component parent retired oldTable oldLife) table life =
  MkFiber component parent retired table life

public export
setFiberLifecycle : (fiber : Fiber name key value world error) ->
  Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)) ->
  Fiber name key value world error
setFiberLifecycle fiber lifecycle = setFiberRuntime fiber (fiberTable fiber) lifecycle

public export
retireFiber : Fiber name key value world error -> Fiber name key value world error
retireFiber (MkFiber component parent retired table lifecycle) =
  MkFiber component parent True table lifecycle

public export
FiberAt : (name, key : Type) -> (value : key -> Type) ->
  (world, error : Type) -> name -> Type
FiberAt name key value world error _ = Fiber name key value world error

||| Definition 45: finite name-unique registry.
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
lookupFiber : DecEq name => name -> Registry name key value world error ->
  Maybe (Fiber name key value world error)
lookupFiber = lookupBinding

public export
registryFibers : Registry name key value world error ->
  List (Binding name (FiberAt name key value world error))
registryFibers = bindings

public export
parentPresent : DecEq name => Parent name -> Registry name key value world error -> Bool
parentPresent Root fibers = True
parentPresent (ChildOf parent) fibers = isJust (lookupFiber parent fibers)

public export
hasChild : DecEq name => name -> Registry name key value world error -> Bool
hasChild parent fibers = any isChild (registryFibers fibers)
  where
  isChild : Binding name (FiberAt name key value world error) -> Bool
  isChild (Bind _ fiber) = case fiberParent fiber of
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
     memberKey k (ownedValues (fiberTable fiber))
    then Just n
    else providerIn k rest

public export
providerOf : DecEq name => DecEq key => key ->
  Registry name key value world error -> Maybe name
providerOf k fibers = providerIn k (registryFibers fibers)

public export
resolveView : DecEq name => DecEq key => (deps : List key) ->
  Registry name key value world error -> Maybe (View name deps)
resolveView [] fibers = Just EmptyView
resolveView (k :: ks) fibers = case providerOf k fibers of
  Nothing => Nothing
  Just provider => map (ProviderView provider) (resolveView ks fibers)

public export
valueFromProvider : DecEq name => DecEq key => (provider : name) ->
  (k : key) -> Registry name key value world error -> Maybe (value k)
valueFromProvider provider k fibers = case lookupFiber provider fibers of
  Nothing => Nothing
  Just fiber => lookupBinding k (ownedValues (fiberTable fiber))

||| Resolve a committed capability directly through provider-owned tables.
||| Providers need only remain installed; they intentionally need not be Active
||| during a dependent's withdrawal interval.
public export
resolveCommittedValues : DecEq name => DecEq key =>
  (deps : List key) -> View name deps ->
  Registry name key value world error -> Maybe (DepValues key value deps)
resolveCommittedValues [] EmptyView fibers = Just NoDepValues
resolveCommittedValues (k :: ks) (ProviderView provider rest) fibers =
  case valueFromProvider provider k fibers of
    Nothing => Nothing
    Just v => map (OneDepValue v) (resolveCommittedValues ks rest fibers)

public export
activeCoeffectsFrom : DecEq name => DecEq key =>
  List (Binding name (FiberAt name key value world error)) ->
  CoeffectContext key value
activeCoeffectsFrom [] = emptyContext
activeCoeffectsFrom (Bind n fiber :: rest) =
  if isActive (fiberLifecycle fiber)
    then mergeOwned (ownedValues (fiberTable fiber))
                    (activeCoeffectsFrom rest)
    else activeCoeffectsFrom rest
  where
  mergeOwned : CoeffectContext key value -> CoeffectContext key value ->
               CoeffectContext key value
  mergeOwned left right = foldr insertIfFresh right (bindings left)
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

||| Definition 46: target view.
public export
targetFiber : DecEq name => DecEq key =>
  (fiber : Fiber name key value world error) ->
  Registry name key value world error ->
  Maybe (View name (dependencies
    (componentDependencies (fiberComponent fiber))))
targetFiber fiber fibers = if retired fiber
  then Nothing
  else resolveView (dependencies (componentDependencies (fiberComponent fiber))) fibers

public export
data SomeView : Type -> Type where
  MkSomeView : View name deps -> SomeView name

public export
targetAt : DecEq name => DecEq key => name ->
  SystemState name key value world error -> Maybe (SomeView name)
targetAt n state = case lookupFiber n (registry state) of
  Nothing => Nothing
  Just fiber => map MkSomeView (targetFiber fiber (registry state))

public export
targetMatches : DecEq name => Maybe (View name deps) -> View name deps -> Bool
targetMatches Nothing view = False
targetMatches (Just target) view = viewEq target view

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

||| The ten Table-1 rule tags.
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

||| Definition 47's host-visible checked forward/inverse pair.
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

public export
isInactive : Lifecycle key value world error name deps provision -> Bool
isInactive (Inactive _) = True
isInactive _ = False

||| Executable semantics for the ten rules. The empty-program terminal marker
||| obeys the same target equality as a non-empty L-Finish; stale targets divert.
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
    MkSystemState (worldState state)
      (replaceBinding n (retireFiber fiber) (registry state)))
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
    Reloading [] accumulator view =>
      if targetMatches (targetFiber fiber (registry state)) view
        then Just (LFinishTag,
          MkSystemState (worldState state)
            (replaceBinding n
              (setFiberLifecycle fiber (Active accumulator view))
              (registry state)))
        else Just (LDivertTag,
          MkSystemState (worldState state)
            (replaceBinding n
              (setFiberLifecycle fiber (Unloading accumulator view Nothing))
              (registry state)))
    Reloading (step :: rest) accumulator view =>
      case resolveCommittedValues
        (dependencies (componentDependencies (fiberComponent fiber)))
        view (registry state) of
        Nothing => Nothing
        Just capability =>
          let localBefore = MkLocalState (worldState state) (fiberTable fiber) in
          case runStepEffect step capability localBefore of
            Left err => Just (LRaiseTag,
              MkSystemState (worldState state)
                (replaceBinding n
                  (setFiberLifecycle fiber
                    (Unloading accumulator view (Just err)))
                  (registry state)))
            Right (localAfter, undo) =>
              let nextAccumulator = accumulator . undo
                  nextWorld = localWorld localAfter
                  nextTable = localTable localAfter in
              if targetMatches (targetFiber fiber (registry state)) view
                then case rest of
                  [] => Just (LFinishTag,
                    MkSystemState nextWorld
                      (replaceBinding n
                        (setFiberRuntime fiber nextTable
                          (Active nextAccumulator view))
                        (registry state)))
                  _ => Just (LIterTag,
                    MkSystemState nextWorld
                      (replaceBinding n
                        (setFiberRuntime fiber nextTable
                          (Reloading rest nextAccumulator view))
                        (registry state)))
                else Just (LDivertTag,
                  MkSystemState nextWorld
                    (replaceBinding n
                      (setFiberRuntime fiber nextTable
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
        else let restored = accumulator
                   (MkLocalState (worldState state) (fiberTable fiber)) in
          Just (LUnloadTag,
            MkSystemState (localWorld restored)
              (replaceBinding n
                (setFiberRuntime fiber (localTable restored) (Inactive outcome))
                (registry state)))
    _ => Nothing

public export
parentInvariant : DecEq name => Parent name -> Registry name key value world error -> Bool
parentInvariant Root fibers = True
parentInvariant (ChildOf parent) fibers = isJust (lookupFiber parent fibers)

public export
parentChainInvariant : DecEq name => Nat -> List name -> name ->
  Registry name key value world error -> Bool
parentChainInvariant Z seen current fibers = False
parentChainInvariant (S fuel) seen current fibers = case lookupFiber current fibers of
  Nothing => False
  Just fiber => case fiberParent fiber of
    Root => True
    ChildOf parent => if elemDec parent seen
      then False
      else parentChainInvariant fuel (parent :: seen) parent fibers

public export
viewProvidersInvariant : DecEq name => Registry name key value world error ->
  View name deps -> Bool
viewProvidersInvariant fibers EmptyView = True
viewProvidersInvariant fibers (ProviderView provider rest) =
  case lookupFiber provider fibers of
    Nothing => False
    Just fiber => installed (fiberLifecycle fiber) &&
                  viewProvidersInvariant fibers rest

public export
viewBindingsInvariant : DecEq name => DecEq key => (deps : List key) ->
  View name deps -> Registry name key value world error -> Bool
viewBindingsInvariant deps view fibers = viewProvidersInvariant fibers view &&
  isJust (resolveCommittedValues deps view fibers)

public export
fiberViewInvariant : DecEq name => DecEq key =>
  Fiber name key value world error -> Registry name key value world error -> Bool
fiberViewInvariant (MkFiber component parent retired table lifecycle) fibers =
  case lifecycle of
    Inactive _ => True
    Reloading _ _ view => viewBindingsInvariant
      (dependencies (componentDependencies component)) view fibers
    Active _ view => viewBindingsInvariant
      (dependencies (componentDependencies component)) view fibers
    Unloading _ view _ => viewBindingsInvariant
      (dependencies (componentDependencies component)) view fibers

public export
pairwiseProvisionInvariant : DecEq key =>
  List (Binding name (FiberAt name key value world error)) -> Bool
pairwiseProvisionInvariant [] = True
pairwiseProvisionInvariant (Bind _ fiber :: rest) =
  provisionsDisjointFrom (componentProvisions (fiberComponent fiber)) rest &&
  pairwiseProvisionInvariant rest

||| Definition 58's executable registry invariant. It lives beside Transition so
||| the indexed LTS can carry erased preservation certificates intrinsically.
public export
registryWellFormed : DecEq name => DecEq key =>
  SystemState name key value world error -> Bool
registryWellFormed state =
  let fibers = registry state
      entries = registryFibers fibers
      fuel = S (length entries)
   in all (\(Bind _ fiber) => parentInvariant (fiberParent fiber) fibers) entries &&
      all (\(Bind n _) => parentChainInvariant fuel [n] n fibers) entries &&
      pairwiseProvisionInvariant entries &&
      all (\(Bind _ fiber) => fiberViewInvariant fiber fibers) entries

||| Runtime-checked rule application used by the proof-indexed LTS. `applyAction`
||| remains the raw ten-rule evaluator; this wrapper rejects a malformed target
||| rather than admitting it into a proof trace.
public export
checkedApplyAction : DecEq name => DecEq key =>
  Action name key value world error ->
  SystemState name key value world error ->
  Maybe (RuleTag, SystemState name key value world error)
checkedApplyAction action before = case applyAction action before of
  Nothing => Nothing
  Just (tag, afterState) =>
    if registryWellFormed afterState then Just (tag, afterState) else Nothing

||| An indexed transition exists only when the executable checked evaluator
||| produced its exact endpoint.
public export
data Transition : SystemState name key value world error ->
                  SystemState name key value world error -> Type where
  Fired : (nameEq : DecEq name) -> (keyEq : DecEq key) ->
          (action : Action name key value world error) -> (tag : RuleTag) ->
          checkedApplyAction @{nameEq} @{keyEq} action before =
            Just (tag, afterState) ->
          Transition before afterState

public export
record TransitionResult (before : SystemState name key value world error) where
  constructor MkTransitionResult
  transitionAfter : SystemState name key value world error
  transitionRule : RuleTag
  checkedTransition : Transition before transitionAfter

||| Execute and package a proof-indexed transition when the checked evaluator
||| accepts the rule.
public export
fire : (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  Action name key value world error ->
  (before : SystemState name key value world error) ->
  Maybe (TransitionResult before)
fire nameEq keyEq action before
  with (checkedApplyAction @{nameEq} @{keyEq} action before) proof fired
  fire nameEq keyEq action before | Nothing = Nothing
  fire nameEq keyEq action before | Just (tag, afterState) =
    Just (MkTransitionResult afterState tag
      (Fired nameEq keyEq action tag fired))

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
transitionAction (Fired _ _ action _ _) = action

public export
transitionTag : {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> RuleTag
transitionTag (Fired _ _ _ tag _) = tag

public export
transitionActor : {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> name
transitionActor transition = case transitionAction transition of
  OInsert n _ _ => n
  ORetire n => n
  ORemove n => n
  LBegin n => n
  LAdvance n => n
  LDivert n => n
  LLeave n => n
  LUnload n => n

public export
appendTransitions : Transitions first middle -> Transitions middle finalState ->
  Transitions first finalState
appendTransitions NoTransitions suffix = suffix
appendTransitions (MoreTransitions step rest) suffix =
  MoreTransitions step (appendTransitions rest suffix)

public export
installedAt : DecEq name => name ->
  SystemState name key value world error -> Bool
installedAt n state = case lookupFiber n (registry state) of
  Nothing => False
  Just fiber => installed (fiberLifecycle fiber)

||| Executable grouping of maximal installed intervals in a snapshot log.
public export
episodes : DecEq name => name ->
  List (SystemState name key value world error) ->
  List (List (SystemState name key value world error))
episodes n states = go states []
  where
  go : List (SystemState name key value world error) ->
       List (SystemState name key value world error) ->
       List (List (SystemState name key value world error))
  go [] [] = []
  go [] current = [reverse current]
  go (state :: rest) current =
    if installedAt n state
      then go rest (state :: current)
      else case current of
        [] => go rest []
        _ => reverse current :: go rest []
