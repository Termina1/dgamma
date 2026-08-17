module DGamma.CP4DeletionControlCore

import DGamma.Calculus
import DGamma.Coeffects
import Data.List.Elem
import Decidable.Equality

%default total

0 justInjectiveLocal : Just left = Just right -> left = right
justInjectiveLocal Refl = Refl

||| Removing an Inactive registry entry cannot change active-provider lookup.
||| This is the executable control half of paper Lemma 57(1).
public export
0 providerInInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) ->
  (removed : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  lookupEntries @{nameEq} removed entries =
    Just (MkFiber component parent retiredFlag table (Inactive outcome)) ->
  providerIn @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} wanted
    (deleteEntries @{nameEq} removed entries) =
  providerIn @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} wanted entries
providerInInactiveDelete nameEq keyEq wanted removed component parent retiredFlag
  table outcome [] present = case present of Refl impossible
providerInInactiveDelete {name} {key} {world} {error} {value}
  nameEq keyEq wanted removed component parent retiredFlag table outcome
  (Bind current observed :: rest) present with (decEq @{nameEq} removed current)
  providerInInactiveDelete {name} {key} {world} {error} {value}
    nameEq keyEq wanted current component parent retiredFlag table outcome
    (Bind current observed :: rest) present | Yes Refl =
      case justInjectiveLocal present of Refl => Refl
  providerInInactiveDelete {name} {key} {world} {error} {value}
    nameEq keyEq wanted removed component parent retiredFlag table outcome
    (Bind current observed :: rest) present | No distinct
    with (isActive (fiberLifecycle observed) &&
      memberKey @{keyEq} wanted (ownedValues (fiberTable observed)))
    providerInInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq wanted removed component parent retiredFlag table outcome
      (Bind current observed :: rest) present | No distinct | False =
        providerInInactiveDelete {name = name} {key = key} {world = world}
          {error = error} {value = value} nameEq keyEq wanted removed component
          parent retiredFlag table outcome rest present
    providerInInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq wanted removed component parent retiredFlag table outcome
      (Bind current observed :: rest) present | No distinct | True = Refl

public export
0 providerOfInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) ->
  (removed : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} removed fibers =
    Just (MkFiber component parent retiredFlag table (Inactive outcome)) ->
  providerOf @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} wanted
    (deleteBinding @{nameEq} removed fibers) =
  providerOf @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} wanted fibers
providerOfInactiveDelete nameEq keyEq wanted removed component parent retiredFlag
  table outcome (MkCoeffectContext entries unique) present =
    providerInInactiveDelete nameEq keyEq wanted removed component parent
      retiredFlag table outcome entries present

||| Consequently every target resolution is unchanged by deleting an Inactive
||| entry, regardless of its declared provision.
public export
0 resolveViewInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (deps : List key) ->
  (removed : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} removed fibers =
    Just (MkFiber component parent retiredFlag table (Inactive outcome)) ->
  resolveView @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} deps (deleteBinding @{nameEq} removed fibers) =
  resolveView @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} deps fibers
resolveViewInactiveDelete nameEq keyEq [] removed component parent retiredFlag
  table outcome fibers present = Refl
resolveViewInactiveDelete {name} {key} {world} {error} {value}
  nameEq keyEq (wanted :: rest) removed component parent retiredFlag table outcome
  fibers present with (providerOf @{nameEq} @{keyEq} wanted fibers) proof original
  resolveViewInactiveDelete {name} {key} {world} {error} {value}
    nameEq keyEq (wanted :: rest) removed component parent retiredFlag table outcome
    fibers present | Nothing =
      let targetProvider = trans
            (providerOfInactiveDelete nameEq keyEq wanted removed component parent
              retiredFlag table outcome fibers present) original
      in rewrite targetProvider in Refl
  resolveViewInactiveDelete {name} {key} {world} {error} {value}
    nameEq keyEq (wanted :: rest) removed component parent retiredFlag table outcome
    fibers present | Just provider =
      let targetProvider = trans
            (providerOfInactiveDelete nameEq keyEq wanted removed component parent
              retiredFlag table outcome fibers present) original
      in rewrite targetProvider in cong (map (ProviderView provider))
        (resolveViewInactiveDelete {name = name} {key = key} {world = world}
          {error = error} {value = value} nameEq keyEq rest removed component
          parent retiredFlag table outcome fibers present)

public export
0 targetFiberInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (observed : Fiber name key value world error) ->
  (removed : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} removed fibers =
    Just (MkFiber component parent retiredFlag table (Inactive outcome)) ->
  targetFiber @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} observed
    (deleteBinding @{nameEq} removed fibers) =
  targetFiber @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} observed fibers
targetFiberInactiveDelete nameEq keyEq
  observed@(MkFiber observedComponent observedParent False observedTable observedLife)
  removed component parent retiredFlag table outcome fibers present =
    resolveViewInactiveDelete nameEq keyEq
      (dependencies (componentDependencies observedComponent)) removed component
      parent retiredFlag table outcome fibers present
targetFiberInactiveDelete nameEq keyEq
  (MkFiber observedComponent observedParent True observedTable observedLife)
  removed component parent retiredFlag table outcome fibers present = Refl

0 reliedHeadInactive :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (provider, self, current : name) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) ->
  reliedHead @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provider self
    (Bind current (MkFiber component parent retiredFlag table (Inactive outcome))) =
    False
reliedHeadInactive nameEq provider self current component parent retiredFlag table
  outcome with (decEq @{nameEq} current self)
  reliedHeadInactive nameEq provider current current component parent retiredFlag
    table outcome | Yes Refl = Refl
  reliedHeadInactive nameEq provider self current component parent retiredFlag
    table outcome | No distinct = Refl

0 reliedOnByInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (provider, self, removed : name) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  lookupEntries @{nameEq} removed entries =
    Just (MkFiber component parent retiredFlag table (Inactive outcome)) ->
  reliedOnBy @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provider self
    (deleteEntries @{nameEq} removed entries) =
  reliedOnBy @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provider self entries
reliedOnByInactiveDelete nameEq provider self removed component parent retiredFlag
  table outcome [] present = case present of Refl impossible
reliedOnByInactiveDelete {name} {key} {world} {error} {value}
  nameEq provider self removed component parent retiredFlag table outcome
  (Bind current observed :: rest) present with (decEq @{nameEq} removed current)
  reliedOnByInactiveDelete {name} {key} {world} {error} {value}
    nameEq provider self current component parent retiredFlag table outcome
    (Bind current observed :: rest) present | Yes Refl =
      case justInjectiveLocal present of
        Refl => rewrite reliedHeadInactive nameEq provider self current component
          parent retiredFlag table outcome in Refl
  reliedOnByInactiveDelete {name} {key} {world} {error} {value}
    nameEq provider self removed component parent retiredFlag table outcome
    (Bind current observed :: rest) present | No distinct
    with (reliedHead @{nameEq} provider self (Bind current observed))
    reliedOnByInactiveDelete {name} {key} {world} {error} {value}
      nameEq provider self removed component parent retiredFlag table outcome
      (Bind current observed :: rest) present | No distinct | False =
        reliedOnByInactiveDelete {name = name} {key = key} {world = world}
          {error = error} {value = value} nameEq provider self removed component
          parent retiredFlag table outcome rest present
    reliedOnByInactiveDelete {name} {key} {world} {error} {value}
      nameEq provider self removed component parent retiredFlag table outcome
      (Bind current observed :: rest) present | No distinct | True = Refl

||| Deleting an Inactive consumer cannot strengthen or weaken the L-Unload
||| reliance test: its installed bit is false, so its committed view is ignored.
public export
0 reliedInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (provider, removed : name) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} removed fibers =
    Just (MkFiber component parent retiredFlag table (Inactive outcome)) ->
  relied @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provider
    (deleteBinding @{nameEq} removed fibers) =
  relied @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provider fibers
reliedInactiveDelete nameEq provider removed component parent retiredFlag table
  outcome (MkCoeffectContext entries unique) present =
    reliedOnByInactiveDelete nameEq provider provider removed component parent
      retiredFlag table outcome entries present

||| Extract the selected per-fiber view certificate from Definition 58.
public export
0 wellFormedFiberView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry state) = Just fiber ->
  registryWellFormed @{nameEq} @{keyEq} state = True ->
  fiberViewInvariant @{nameEq} @{keyEq} fiber (registry state) = True
wellFormedFiberView {name} {key} {world} {error} {value}
  nameEq keyEq selected (MkSystemState ambient fibers@(MkCoeffectContext entries unique))
  fiber found valid =
    let allViews = andFourFourth
          (parentsInvariant @{nameEq} entries fibers)
          (chainsInvariant @{nameEq} (S (length entries)) entries fibers)
          (pairwiseProvisionInvariant @{keyEq} entries)
          (viewsInvariant @{nameEq} @{keyEq} entries fibers) valid
    in viewsInvariantLookup {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq keyEq selected fiber entries fibers
      found allViews
