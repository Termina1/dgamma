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
resolveView @{nameEq} @{keyEq} (k :: ks) fibers =
  case providerOf @{nameEq} @{keyEq} k fibers of
    Nothing => Nothing
    Just provider => map (ProviderView provider)
      (resolveView @{nameEq} @{keyEq} ks fibers)

public export
valueFromProvider : DecEq name => DecEq key => (provider : name) ->
  (k : key) -> Registry name key value world error -> Maybe (value k)
valueFromProvider provider k fibers = case lookupFiber provider fibers of
  Nothing => Nothing
  Just fiber => lookupBinding k (ownedValues (fiberTable fiber))

||| Inserting an empty Inactive fiber preserves every provider-table lookup.
public export
0 valueFromProviderInactiveInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider : name) -> (k : key) -> (n : name) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  valueFromProvider @{nameEq} @{keyEq} {value = value} {world = world} {error = error} provider k
    (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) =
  valueFromProvider @{nameEq} @{keyEq} {value = value} {world = world} {error = error} provider k fibers
valueFromProviderInactiveInsert {key} {world} {error} {value} nameEq keyEq provider k n component parent fibers absent
  with (decEq @{nameEq} provider n)
  valueFromProviderInactiveInsert {key} {world} {error} {value} nameEq keyEq n k n component parent fibers absent |
    (Yes Refl) =
      rewrite lookupInserted n (freshFiber component parent) fibers absent in
        rewrite absent in Refl
  valueFromProviderInactiveInsert {key} {world} {error} {value} nameEq keyEq provider k n component parent fibers absent |
    (No distinct) with (lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} provider fibers) proof present
    valueFromProviderInactiveInsert {key} {world} {error} {value} nameEq keyEq provider k n component parent fibers absent |
      (No distinct) | Nothing =
        rewrite lookupInsertOther provider n distinct (freshFiber component parent)
          fibers absent in rewrite present in Refl
    valueFromProviderInactiveInsert {key} {world} {error} {value} nameEq keyEq provider k n component parent fibers absent |
      (No distinct) | Just providerFiber =
        rewrite lookupInsertOther provider n distinct (freshFiber component parent)
          fibers absent in rewrite present in Refl

||| Resolve a committed capability directly through provider-owned tables.
||| Providers need only remain installed; they intentionally need not be Active
||| during a dependent's withdrawal interval.
public export
resolveCommittedValues : DecEq name => DecEq key =>
  (deps : List key) -> View name deps ->
  Registry name key value world error -> Maybe (DepValues key value deps)
resolveCommittedValues [] EmptyView fibers = Just NoDepValues
resolveCommittedValues @{nameEq} @{keyEq} (k :: ks) (ProviderView provider rest) fibers =
  case valueFromProvider @{nameEq} @{keyEq} provider k fibers of
    Nothing => Nothing
    Just v => map (OneDepValue v)
      (resolveCommittedValues @{nameEq} @{keyEq} ks rest fibers)

||| Inserting an empty Inactive fiber preserves every committed capability.
public export
0 resolveCommittedValuesInactiveInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  resolveCommittedValues @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps view
    (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) =
  resolveCommittedValues @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps view fibers
resolveCommittedValuesInactiveInsert {key} {world} {error} {value} nameEq keyEq [] EmptyView
  n component parent fibers absent = Refl
resolveCommittedValuesInactiveInsert {name} {key} {world} {error} {value}
  nameEq keyEq (k :: ks) (ProviderView provider rest)
  n component parent fibers absent
  with (valueFromProvider @{nameEq} @{keyEq} provider k fibers) proof original
  resolveCommittedValuesInactiveInsert {name} {key} {world} {error} {value}
    nameEq keyEq (k :: ks) (ProviderView provider rest)
    n component parent fibers absent | Nothing =
      let inserted = trans
            (valueFromProviderInactiveInsert {name = name} {key = key}
              {world = world} {error = error} {value = value}
              nameEq keyEq provider k n component parent fibers absent)
            original in rewrite inserted in Refl
  resolveCommittedValuesInactiveInsert {name} {key} {world} {error} {value}
    nameEq keyEq (k :: ks) (ProviderView provider rest)
    n component parent fibers absent | Just v =
      let inserted = trans
            (valueFromProviderInactiveInsert {name = name} {key = key}
              {world = world} {error = error} {value = value}
              nameEq keyEq provider k n component parent fibers absent)
            original in
      rewrite inserted in cong (map (OneDepValue v))
        (resolveCommittedValuesInactiveInsert {name = name} {key = key}
          {world = world} {error = error} {value = value}
          nameEq keyEq ks rest n component parent fibers absent)

||| Inserting a fresh Inactive fiber cannot become a provider or change any
||| existing target resolution.
public export
0 providerOfInactiveInsert : {name, key, world, error : Type} ->
  {value : key -> Type} -> (nameEq : DecEq name) -> (keyEq : DecEq key) -> (k : key) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  providerOf @{nameEq} @{keyEq} {value = value} {world = world} {error = error} k (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) =
    providerOf @{nameEq} @{keyEq} {value = value} {world = world} {error = error} k fibers
providerOfInactiveInsert nameEq keyEq k n component parent (MkCoeffectContext entries unique) absent =
  Refl

public export
0 resolveViewInactiveInsert : {name, key, world, error : Type} ->
  {value : key -> Type} -> (nameEq : DecEq name) -> (keyEq : DecEq key) -> (deps : List key) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  resolveView @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) =
    resolveView @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps fibers
resolveViewInactiveInsert nameEq keyEq [] n component parent fibers absent = Refl
resolveViewInactiveInsert {name} {key} {world} {error} {value} nameEq keyEq (k :: ks)
  n component parent fibers absent
  with (providerOf @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} k fibers) proof originalProvider
  resolveViewInactiveInsert {name} {key} {world} {error} {value}
    nameEq keyEq (k :: ks) n component parent fibers absent | Nothing =
      let insertedNone = trans
            (providerOfInactiveInsert {name = name} {key = key} {world = world}
              {error = error} {value = value} nameEq keyEq k n component parent fibers absent)
            originalProvider in
        rewrite insertedNone in Refl
  resolveViewInactiveInsert {name} {key} {world} {error} {value}
    nameEq keyEq (k :: ks) n component parent fibers absent | Just provider =
      let insertedJust = trans
            (providerOfInactiveInsert {name = name} {key = key} {world = world}
              {error = error} {value = value} nameEq keyEq k n component parent fibers absent)
            originalProvider in
      rewrite insertedJust in cong (map (ProviderView provider))
        (resolveViewInactiveInsert {name = name} {key = key}
          {world = world} {error = error} {value = value}
          nameEq keyEq ks n component parent fibers absent)

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

||| Appending a distinct fresh name does not change a failed membership test.
public export
0 elemDecAppendFresh : DecEq a => (wanted, fresh : a) -> (seen : List a) ->
  elemDec wanted seen = False -> Not (wanted = fresh) ->
  elemDec wanted (seen ++ [fresh]) = False
elemDecAppendFresh wanted fresh [] absent distinct with (decEq wanted fresh)
  elemDecAppendFresh fresh fresh [] absent distinct | (Yes Refl) = void (distinct Refl)
  elemDecAppendFresh wanted fresh [] absent distinct | (No _) = Refl
elemDecAppendFresh wanted fresh (x :: xs) absent distinct with (decEq wanted x)
  elemDecAppendFresh x fresh (x :: xs) absent distinct | (Yes Refl) =
    case absent of Refl impossible
  elemDecAppendFresh wanted fresh (x :: xs) absent distinct | (No _) =
    elemDecAppendFresh wanted fresh xs absent distinct

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

||| A committed provider may be Active or withdrawing, but never Inactive or
||| Reloading. In particular a Reloading fiber may mutate its table without
||| invalidating any already-committed consumer view.
public export
stableProvider : Lifecycle key value world error name deps provision -> Bool
stableProvider (Active _ _) = True
stableProvider (Unloading _ _ _) = True
stableProvider _ = False

0 falseCannotBeTrue : False = True -> Void
falseCannotBeTrue Refl impossible

0 parentChainAbsentImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (fuel : Nat) -> (seen : List name) ->
  (current : name) -> (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} current fibers = Nothing ->
  parentChainInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fuel seen current fibers = True -> Void
parentChainAbsentImpossible {key} {world} {error} {value} nameEq Z seen current fibers absent valid =
  falseCannotBeTrue valid
parentChainAbsentImpossible {key} {world} {error} {value}
  nameEq (S fuel) seen current fibers absent valid
  with (lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} current fibers)
  parentChainAbsentImpossible {key} {world} {error} {value}
    nameEq (S fuel) seen current fibers absent valid | Nothing =
      falseCannotBeTrue valid
  parentChainAbsentImpossible {key} {world} {error} {value}
    nameEq (S fuel) seen current fibers absent valid | Just fiber =
      case absent of Refl impossible

||| Adding a globally absent name to the seen set cannot truncate a valid chain.
public export
0 parentChainAppendFresh :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (fuel : Nat) -> (seen : List name) ->
  (current, fresh : name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} fresh fibers = Nothing) ->
  Not (Elem fresh seen) -> Elem current seen ->
  parentChainInvariant @{nameEq} {key = key} {value = value}
    {world = world} {error = error} fuel seen current fibers = True ->
  parentChainInvariant @{nameEq} {key = key} {value = value}
    {world = world} {error = error} fuel (seen ++ [fresh]) current fibers = True
parentChainAppendFresh nameEq Z seen current fresh fibers absent notSeen currentSeen valid =
  void (falseCannotBeTrue valid)
parentChainAppendFresh {name} {key} {world} {error} {value}
  nameEq (S fuel) seen current fresh fibers absent notSeen currentSeen valid
  with (lookupFiber @{nameEq} current fibers) proof currentLookup
  parentChainAppendFresh {name} {key} {world} {error} {value}
    nameEq (S fuel) seen current fresh fibers absent notSeen currentSeen valid |
    Nothing = void (falseCannotBeTrue valid)
  parentChainAppendFresh {name} {key} {world} {error} {value}
    nameEq (S fuel) seen current fresh fibers absent notSeen currentSeen valid |
    Just currentFiber with (fiberParent currentFiber) proof parentShape
    parentChainAppendFresh {name} {key} {world} {error} {value}
      nameEq (S fuel) seen current fresh fibers absent notSeen currentSeen valid |
      Just currentFiber | Root =
        Refl
    parentChainAppendFresh {name} {key} {world} {error} {value}
      nameEq (S fuel) seen current fresh fibers absent notSeen currentSeen valid |
      Just currentFiber | ChildOf next
      with (elemDec @{nameEq} next seen) proof sourceSeen
      parentChainAppendFresh {name} {key} {world} {error} {value}
        nameEq (S fuel) seen current fresh fibers absent notSeen currentSeen valid |
        Just currentFiber | ChildOf next | True = void (falseCannotBeTrue valid)
      parentChainAppendFresh {name} {key} {world} {error} {value}
        nameEq (S fuel) seen current fresh fibers absent notSeen currentSeen valid |
        Just currentFiber | ChildOf next | False =
          case decEq @{nameEq} next fresh of
            Yes Refl => void (parentChainAbsentImpossible {key = key} {value = value}
              {world = world} {error = error} nameEq fuel (fresh :: seen) fresh
              fibers absent valid)
            No distinct =>
              let targetSeen = elemDecAppendFresh next fresh seen sourceSeen distinct
                  freshNotLater : Not (Elem fresh (next :: seen))
                  freshNotLater occurrence = case occurrence of
                    Here => distinct Refl
                    There later => notSeen later
              in rewrite targetSeen in
                parentChainAppendFresh {name = name} {key = key} {world = world}
                  {error = error} {value = value} nameEq fuel (next :: seen)
                  next fresh fibers absent freshNotLater Here valid

||| A fresh Inactive insertion preserves an existing parent chain. The `seen`
||| premise records that the fresh name cannot be an ancestor already visited.
public export
0 parentChainInactiveInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (fuel : Nat) -> (seen : List name) ->
  (current, n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  Not (Elem n seen) -> Elem current seen ->
  parentChainInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fuel seen current fibers = True ->
  parentChainInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fuel seen current
    (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) = True
parentChainInactiveInsert {key} {world} {error} {value} nameEq Z seen current n component parent fibers
  absent freshNotSeen currentSeen valid = void (falseCannotBeTrue valid)
parentChainInactiveInsert {name} {key} {world} {error} {value}
  nameEq (S fuel) seen current n component parent fibers
  absent freshNotSeen currentSeen valid
  with (lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} current fibers) proof currentLookup
  parentChainInactiveInsert {name} {key} {world} {error} {value}
    nameEq (S fuel) seen current n component parent fibers
    absent freshNotSeen currentSeen valid | Nothing = void (falseCannotBeTrue valid)
  parentChainInactiveInsert {name} {key} {world} {error} {value}
    nameEq (S fuel) seen current n component parent fibers
    absent freshNotSeen currentSeen valid | Just currentFiber
    with (fiberParent currentFiber) proof parentShape
    parentChainInactiveInsert {name} {key} {world} {error} {value}
      nameEq (S fuel) seen current n component parent fibers
      absent freshNotSeen currentSeen valid | Just currentFiber | Root =
        let distinct = \same => freshNotSeen (replace {p = \x => Elem x seen}
              same currentSeen)
            framed = lookupInsertOther current n distinct (freshFiber component parent)
              fibers absent
            inserted = trans framed currentLookup in
          rewrite inserted in rewrite parentShape in Refl
    parentChainInactiveInsert {name} {key} {world} {error} {value}
      nameEq (S fuel) seen current n component parent fibers
      absent freshNotSeen currentSeen valid | Just currentFiber | ChildOf next
      with (elemDec @{nameEq} next seen) proof seenNext
      parentChainInactiveInsert {name} {key} {world} {error} {value}
        nameEq (S fuel) seen current n component parent fibers
        absent freshNotSeen currentSeen valid | Just currentFiber | ChildOf next |
        True = void (falseCannotBeTrue valid)
      parentChainInactiveInsert {name} {key} {world} {error} {value}
        nameEq (S fuel) seen current n component parent fibers
        absent freshNotSeen currentSeen valid | Just currentFiber | ChildOf next |
        False =
          let currentDistinct = \same => freshNotSeen (replace {p = \x => Elem x seen}
                same currentSeen)
              currentFramed = lookupInsertOther current n currentDistinct
                (freshFiber component parent) fibers absent
              insertedCurrent = trans currentFramed currentLookup in
          case decEq @{nameEq} next n of
            Yes Refl =>
              rewrite insertedCurrent in rewrite parentShape in rewrite seenNext in
                void (parentChainAbsentImpossible {key = key} {value = value} {world = world} {error = error} nameEq fuel (n :: seen) n
                  fibers absent valid)
            No nextDistinct =>
              let nextNotSeen : Not (Elem n (next :: seen))
                  nextNotSeen occurrence = case occurrence of
                    Here => nextDistinct Refl
                    There later => freshNotSeen later
                  in rewrite insertedCurrent in rewrite parentShape in
                    rewrite seenNext in
                      parentChainInactiveInsert {name = name} {key = key}
                        {world = world} {error = error} {value = value}
                        nameEq fuel (next :: seen) next n component parent fibers absent
                        nextNotSeen Here valid

||| Parent-chain validity is monotone in fuel. Insertion raises the global fuel
||| by one, so existing chains remain certified.
public export
0 parentChainFuelMonotone : {name, key, world, error : Type} ->
  {value : key -> Type} -> (nameEq : DecEq name) -> (fuel : Nat) ->
  (seen : List name) -> (current : name) ->
  (fibers : Registry name key value world error) ->
  parentChainInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error}
    fuel seen current fibers = True ->
  parentChainInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error}
    (S fuel) seen current fibers = True
parentChainFuelMonotone nameEq Z seen current fibers valid =
  void (falseCannotBeTrue valid)
parentChainFuelMonotone nameEq (S fuel) seen current fibers valid
  with (lookupFiber @{nameEq} current fibers)
  parentChainFuelMonotone nameEq (S fuel) seen current fibers valid | Nothing =
    void (falseCannotBeTrue valid)
  parentChainFuelMonotone nameEq (S fuel) seen current fibers valid | Just fiber
    with (fiberParent fiber)
    parentChainFuelMonotone nameEq (S fuel) seen current fibers valid | Just fiber |
      Root = Refl
    parentChainFuelMonotone nameEq (S fuel) seen current fibers valid | Just fiber |
      ChildOf parent with (elemDec @{nameEq} parent seen)
      parentChainFuelMonotone nameEq (S fuel) seen current fibers valid | Just fiber |
        ChildOf parent | True = void (falseCannotBeTrue valid)
      parentChainFuelMonotone nameEq (S fuel) seen current fibers valid | Just fiber |
        ChildOf parent | False =
          parentChainFuelMonotone nameEq fuel (parent :: seen) parent fibers valid

public export
viewProvidersInvariant : DecEq name => Registry name key value world error ->
  View name deps -> Bool
viewProvidersInvariant fibers EmptyView = True
viewProvidersInvariant @{nameEq} fibers (ProviderView provider rest) =
  case lookupFiber @{nameEq} provider fibers of
    Nothing => False
    Just fiber => stableProvider (fiberLifecycle fiber) &&
                  viewProvidersInvariant @{nameEq} fibers rest

public export
0 viewProvidersInactiveInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (deps : List key) -> (view : View name deps) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  viewProvidersInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error}
    (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) view =
  viewProvidersInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fibers view
viewProvidersInactiveInsert {key} {world} {error} {value} nameEq [] EmptyView n component parent fibers absent = Refl
viewProvidersInactiveInsert {name} {key} {world} {error} {value}
  nameEq (k :: ks) (ProviderView provider rest) n component parent fibers absent
  with (decEq @{nameEq} provider n)
  viewProvidersInactiveInsert {name} {key} {world} {error} {value}
    nameEq (k :: ks) (ProviderView n rest) n component parent fibers absent |
    (Yes Refl) =
      rewrite lookupInserted n (freshFiber component parent) fibers absent in
        rewrite absent in Refl
  viewProvidersInactiveInsert {name} {key} {world} {error} {value}
    nameEq (k :: ks) (ProviderView provider rest) n component parent fibers absent |
    (No distinct) with (lookupFiber @{nameEq} {key = key} {value = value}
      {world = world} {error = error} provider fibers) proof original
    viewProvidersInactiveInsert {name} {key} {world} {error} {value}
      nameEq (k :: ks) (ProviderView provider rest) n component parent fibers absent |
      (No distinct) | Nothing =
        let inserted = trans
              (lookupInsertOther provider n distinct (freshFiber component parent)
                fibers absent) original in rewrite inserted in Refl
    viewProvidersInactiveInsert {name} {key} {world} {error} {value}
      nameEq (k :: ks) (ProviderView provider rest) n component parent fibers absent |
      (No distinct) | Just providerFiber =
        let inserted = trans
              (lookupInsertOther provider n distinct (freshFiber component parent)
                fibers absent) original in
        rewrite inserted in cong (stableProvider (fiberLifecycle providerFiber) &&)
          (viewProvidersInactiveInsert {name = name} {key = key}
            {world = world} {error = error} {value = value}
            nameEq ks rest n component parent fibers absent)

public export
viewBindingsInvariant : DecEq name => DecEq key => (deps : List key) ->
  View name deps -> Registry name key value world error -> Bool
viewBindingsInvariant @{nameEq} @{keyEq} deps view fibers =
  viewProvidersInvariant @{nameEq} fibers view &&
  isJust (resolveCommittedValues @{nameEq} @{keyEq} deps view fibers)

public export
0 viewBindingsInactiveInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} n fibers = Nothing) ->
  viewBindingsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps view
    (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) =
  viewBindingsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps view fibers
viewBindingsInactiveInsert {name} {key} {world} {error} {value}
  nameEq keyEq deps view n component parent fibers absent =
  rewrite viewProvidersInactiveInsert {name = name} {key = key}
    {world = world} {error = error} {value = value}
    nameEq deps view n component parent fibers absent in
  rewrite resolveCommittedValuesInactiveInsert {name = name} {key = key}
    {world = world} {error = error} {value = value}
    nameEq keyEq deps view n component parent fibers absent in Refl

public export
fiberViewInvariant : DecEq name => DecEq key =>
  Fiber name key value world error -> Registry name key value world error -> Bool
fiberViewInvariant @{nameEq} @{keyEq}
  (MkFiber component parent retired table lifecycle) fibers =
  case lifecycle of
    Inactive _ => True
    Reloading _ _ view => viewBindingsInvariant @{nameEq} @{keyEq}
      (dependencies (componentDependencies component)) view fibers
    Active _ view => viewBindingsInvariant @{nameEq} @{keyEq}
      (dependencies (componentDependencies component)) view fibers
    Unloading _ view _ => viewBindingsInvariant @{nameEq} @{keyEq}
      (dependencies (componentDependencies component)) view fibers

public export
0 fiberViewInactiveInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (fiber : Fiber name key value world error) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} n fibers = Nothing) ->
  fiberViewInvariant @{nameEq} @{keyEq} fiber
    (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) =
  fiberViewInvariant @{nameEq} @{keyEq} fiber fibers
fiberViewInactiveInsert {name} {key} {world} {error} {value}
  nameEq keyEq (MkFiber ownComponent ownParent retired table lifecycle)
  n component parent fibers absent = case lifecycle of
    Inactive outcome => Refl
    Reloading remaining accumulator view =>
      viewBindingsInactiveInsert {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq keyEq
        (dependencies (componentDependencies ownComponent)) view
        n component parent fibers absent
    Active accumulator view =>
      viewBindingsInactiveInsert {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq keyEq
        (dependencies (componentDependencies ownComponent)) view
        n component parent fibers absent
    Unloading accumulator view outcome =>
      viewBindingsInactiveInsert {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq keyEq
        (dependencies (componentDependencies ownComponent)) view
        n component parent fibers absent

public export
pairwiseProvisionInvariant : DecEq key =>
  List (Binding name (FiberAt name key value world error)) -> Bool
pairwiseProvisionInvariant [] = True
pairwiseProvisionInvariant @{keyEq} {value} {world} {error}
  (Bind _ fiber :: rest) =
  provisionsDisjointFrom @{keyEq} {value = value} {world = world} {error = error}
    (componentProvisions (fiberComponent fiber)) rest &&
  pairwiseProvisionInvariant @{keyEq}
    {value = value} {world = world} {error = error} rest

0 andTrueLeft : (left, right : Bool) -> left && right = True -> left = True
andTrueLeft False right equation = void (falseCannotBeTrue equation)
andTrueLeft True right equation = Refl

0 andTrueRight : (left, right : Bool) -> left && right = True -> right = True
andTrueRight False right equation = void (falseCannotBeTrue equation)
andTrueRight True False equation = void (falseCannotBeTrue equation)
andTrueRight True True equation = Refl

0 andBothTrue : (left, right : Bool) -> left = True -> right = True ->
  left && right = True
andBothTrue True True Refl Refl = Refl

0 freshFiberProvision : (component : Component key value world error) ->
  (parent : Parent name) ->
  componentProvisions (fiberComponent (freshFiber component parent)) =
    componentProvisions component
freshFiberProvision (MkComponent deps provision program) parent = Refl

0 pairwiseFreshConsEquation : {name, key, world, error : Type} ->
  {value : key -> Type} -> (keyEq : DecEq key) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  pairwiseProvisionInvariant @{keyEq} {value = value} {world = world} {error = error}
    (Bind n (freshFiber component parent) :: entries) =
  (provisionsDisjointFrom @{keyEq} {value = value} {world = world} {error = error} (componentProvisions component) entries &&
   pairwiseProvisionInvariant @{keyEq} {value = value} {world = world} {error = error} entries)
pairwiseFreshConsEquation {value} {world} {error} keyEq n (MkComponent deps provision program)
  parent entries = Refl

||| The O-Insert provision premise is exactly the new head clause.
public export
0 pairwiseProvisionInsert : {name, key, world, error : Type} ->
  {value : key -> Type} -> (keyEq : DecEq key) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  provisionsDisjointFrom @{keyEq} {value = value} {world = world} {error = error} (componentProvisions component) entries = True ->
  pairwiseProvisionInvariant @{keyEq} {value = value} {world = world} {error = error} entries = True ->
  pairwiseProvisionInvariant @{keyEq} {value = value} {world = world} {error = error} (Bind n (freshFiber component parent) :: entries) = True
pairwiseProvisionInsert {value} {world} {error} keyEq n
  component parent entries disjoint oldValid =
  trans
    (pairwiseFreshConsEquation {value = value} {world = world}
      {error = error} keyEq n component parent entries)
    (andBothTrue
      (provisionsDisjointFrom @{keyEq} {value = value} {world = world}
        {error = error} (componentProvisions component) entries)
      (pairwiseProvisionInvariant @{keyEq} {value = value} {world = world}
        {error = error} entries) disjoint oldValid)

public export
parentsInvariant : DecEq name =>
  List (Binding name (FiberAt name key value world error)) ->
  Registry name key value world error -> Bool
parentsInvariant [] fibers = True
parentsInvariant (Bind _ fiber :: rest) fibers =
  parentInvariant (fiberParent fiber) fibers && parentsInvariant rest fibers

||| Inserting an Inactive fresh fiber preserves every existing parent lookup.
public export
0 parentInvariantInactiveInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (parent : Parent name) ->
  (n : name) -> (component : Component key value world error) ->
  (newParent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} parent fibers = True ->
  parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} parent
    (insertBinding @{nameEq} n (freshFiber component newParent) fibers absent) = True
parentInvariantInactiveInsert {key} {world} {error} {value} nameEq Root n component newParent fibers absent valid = Refl
parentInvariantInactiveInsert {key} {world} {error} {value} nameEq (ChildOf parent) n component newParent fibers absent valid
  with (lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} parent fibers) proof present
  parentInvariantInactiveInsert {key} {world} {error} {value} nameEq (ChildOf parent) n component newParent fibers absent valid |
    Nothing = void (falseCannotBeTrue valid)
  parentInvariantInactiveInsert {key} {world} {error} {value} nameEq (ChildOf parent) n component newParent fibers absent valid |
    Just parentFiber =
      let distinct = presentAbsentDistinct parent n fibers parentFiber present absent
          framed = lookupInsertOther parent n distinct (freshFiber component newParent)
            fibers absent in
        rewrite framed in rewrite present in Refl

public export
0 parentsInvariantInactiveInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (component : Component key value world error) ->
  (newParent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} entries fibers = True ->
  parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} entries
    (insertBinding @{nameEq} n (freshFiber component newParent) fibers absent) = True
parentsInvariantInactiveInsert {key} {world} {error} {value} nameEq [] n component newParent fibers absent valid = Refl
parentsInvariantInactiveInsert {key} {world} {error} {value} nameEq (Bind current fiber :: rest)
  n component newParent fibers absent valid =
  andBothTrue
    (parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (fiberParent fiber)
      (insertBinding @{nameEq} n (freshFiber component newParent) fibers absent))
    (parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} rest
      (insertBinding @{nameEq} n (freshFiber component newParent) fibers absent))
    (parentInvariantInactiveInsert nameEq (fiberParent fiber) n component
      newParent fibers absent
      (andTrueLeft (parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (fiberParent fiber) fibers)
        (parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} rest fibers) valid))
    (parentsInvariantInactiveInsert nameEq rest n component newParent fibers absent
      (andTrueRight (parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (fiberParent fiber) fibers)
        (parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} rest fibers) valid))

public export
chainsInvariant : DecEq name => Nat ->
  List (Binding name (FiberAt name key value world error)) ->
  Registry name key value world error -> Bool
chainsInvariant fuel [] fibers = True
chainsInvariant {key} {value} {world} {error} fuel (Bind n _ :: rest) fibers =
  parentChainInvariant {key = key} {value = value} {world = world} {error = error}
    fuel [n] n fibers &&
  chainsInvariant {key = key} {value = value} {world = world} {error = error}
    fuel rest fibers

||| Lift fuel monotonicity pointwise over every registry entry.
public export
0 chainsFuelMonotone : {name, key, world, error : Type} ->
  {value : key -> Type} -> (nameEq : DecEq name) -> (fuel : Nat) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (fibers : Registry name key value world error) ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error}
    fuel entries fibers = True ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error}
    (S fuel) entries fibers = True
chainsFuelMonotone nameEq fuel [] fibers valid = Refl
chainsFuelMonotone {key} {world} {error} {value} nameEq fuel
  (Bind n fiber :: rest) fibers valid =
  let headValid = andTrueLeft
        (parentChainInvariant @{nameEq} {key = key} {value = value} {world = world}
          {error = error} fuel [n] n fibers)
        (chainsInvariant @{nameEq} {key = key} {value = value} {world = world}
          {error = error} fuel rest fibers) valid
      tailValid = andTrueRight
        (parentChainInvariant @{nameEq} {key = key} {value = value} {world = world}
          {error = error} fuel [n] n fibers)
        (chainsInvariant @{nameEq} {key = key} {value = value} {world = world}
          {error = error} fuel rest fibers) valid in
    andBothTrue
      (parentChainInvariant @{nameEq} {key = key} {value = value} {world = world}
        {error = error} (S fuel) [n] n fibers)
      (chainsInvariant @{nameEq} {key = key} {value = value} {world = world}
        {error = error} (S fuel) rest fibers)
      (parentChainFuelMonotone {key = key} {value = value}
        {world = world} {error = error} nameEq fuel [n] n fibers headValid)
      (chainsFuelMonotone {key = key} {value = value}
        {world = world} {error = error} nameEq fuel rest fibers tailValid)

public export
viewsInvariant : DecEq name => DecEq key =>
  List (Binding name (FiberAt name key value world error)) ->
  Registry name key value world error -> Bool
viewsInvariant [] fibers = True
viewsInvariant @{nameEq} @{keyEq} (Bind _ fiber :: rest) fibers =
  fiberViewInvariant @{nameEq} @{keyEq} fiber fibers &&
  viewsInvariant @{nameEq} @{keyEq} rest fibers

public export
0 viewsInactiveInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries fibers = True ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries
    (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) = True
viewsInactiveInsert {key} {world} {error} {value} nameEq keyEq [] n component parent fibers absent valid = Refl
viewsInactiveInsert {name} {key} {world} {error} {value}
  nameEq keyEq (Bind current fiber :: rest) n component parent fibers absent valid =
  let oldHead = andTrueLeft
        (fiberViewInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} fiber fibers)
        (viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} rest fibers) valid
      oldTail = andTrueRight
        (fiberViewInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} fiber fibers)
        (viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} rest fibers) valid
      newHead = trans
        (fiberViewInactiveInsert {name = name} {key = key} {world = world}
          {error = error} {value = value} nameEq keyEq fiber n component parent
          fibers absent) oldHead
      newTail = viewsInactiveInsert {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq keyEq rest n component parent
        fibers absent oldTail in
    andBothTrue _ _ newHead newTail

||| Definition 58's executable registry invariant. Explicit recursive folds make
||| preservation frame proofs reusable and transparent.
public export
registryWellFormed : DecEq name => DecEq key =>
  SystemState name key value world error -> Bool
registryWellFormed state =
  let fibers = registry state
      entries = registryFibers fibers
      fuel = S (length entries)
   in parentsInvariant entries fibers &&
      chainsInvariant fuel entries fibers &&
      pairwiseProvisionInvariant entries && viewsInvariant entries fibers

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
