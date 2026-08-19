module DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceSnapshot

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import Data.List.Elem
import Decidable.Equality

%default total

0 falseNotTrueRelianceAnchor : False = True -> Void
falseNotTrueRelianceAnchor Refl impossible

0 boolAndRightTrueRelianceAnchor :
  (left, right : Bool) -> left && right = True -> right = True
boolAndRightTrueRelianceAnchor False right same = case same of Refl impossible
boolAndRightTrueRelianceAnchor True False same = case same of Refl impossible
boolAndRightTrueRelianceAnchor True True same = Refl

public export
0 viewLookupFromElemRelianceAnchor :
  (keyEq : DecEq key) -> (wanted : key) ->
  (deps : List key) -> (view : View name deps) ->
  Elem wanted deps ->
  (provider : name ** viewLookup @{keyEq} wanted deps view = Just provider)
viewLookupFromElemRelianceAnchor keyEq wanted (wanted :: rest)
  (ProviderView provider tail) Here
  with (decEq @{keyEq} wanted wanted)
  viewLookupFromElemRelianceAnchor keyEq wanted (wanted :: rest)
    (ProviderView provider tail) Here | Yes Refl = (provider ** Refl)
  viewLookupFromElemRelianceAnchor keyEq wanted (wanted :: rest)
    (ProviderView provider tail) Here | No contra = void (contra Refl)
viewLookupFromElemRelianceAnchor keyEq wanted (current :: rest)
  (ProviderView provider tail) (There later)
  with (decEq @{keyEq} wanted current)
  viewLookupFromElemRelianceAnchor keyEq current (current :: rest)
    (ProviderView provider tail) (There later) | Yes Refl = (provider ** Refl)
  viewLookupFromElemRelianceAnchor keyEq wanted (current :: rest)
    (ProviderView provider tail) (There later) | No distinct =
      viewLookupFromElemRelianceAnchor keyEq wanted rest tail later

0 installedAtFoundRelianceSnapshot :
  (nameEq : DecEq name) -> (actor : name) ->
  (state : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor (registry state) = Just fiber ->
  installedAt @{nameEq} actor state = installed (fiberLifecycle fiber)
installedAtFoundRelianceSnapshot nameEq actor state fiber found =
  rewrite found in Refl

public export
record InstalledCommittedSnapshot
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (actor : name)
  (state : SystemState name key value world error)
  (owner : Fiber name key value world error) where
  constructor MkInstalledCommittedSnapshot
  committedSnapshotProviders : List name
  installedOwnerSnapshot : CommittedSnapshot name key world error value nameEq
    actor committedSnapshotProviders state
  0 installedSnapshotOwner : committedFiber installedOwnerSnapshot = owner

public export
0 installedOwnerCommittedSnapshot :
  (nameEq : DecEq name) -> (actor : name) ->
  (state : SystemState name key value world error) ->
  (owner : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor (registry state) = Just owner ->
  installedAt @{nameEq} actor state = True ->
  InstalledCommittedSnapshot name key world error value nameEq actor state owner
installedOwnerCommittedSnapshot nameEq actor state
  owner@(MkFiber component parent retiredFlag table lifecycle) ownerFound installed
  with (lifecycle)
  installedOwnerCommittedSnapshot nameEq actor state
    owner@(MkFiber component parent retiredFlag table lifecycle) ownerFound installed |
    Inactive outcome = case trans
      (sym (installedAtFoundRelianceSnapshot nameEq actor state
        (MkFiber component parent retiredFlag table (Inactive outcome))
        ownerFound)) installed of
          Refl impossible
  installedOwnerCommittedSnapshot nameEq actor state
    owner@(MkFiber component parent retiredFlag table lifecycle) ownerFound installed |
    Reloading remaining accumulator view =
      MkInstalledCommittedSnapshot (viewProviders view)
        (MkCommittedSnapshot
          (MkFiber component parent retiredFlag table
            (Reloading remaining accumulator view))
          ownerFound view Refl Refl) Refl
  installedOwnerCommittedSnapshot nameEq actor state
    owner@(MkFiber component parent retiredFlag table lifecycle) ownerFound installed |
    Active accumulator view =
      MkInstalledCommittedSnapshot (viewProviders view)
        (MkCommittedSnapshot
          (MkFiber component parent retiredFlag table
            (Active accumulator view))
          ownerFound view Refl Refl) Refl
  installedOwnerCommittedSnapshot nameEq actor state
    owner@(MkFiber component parent retiredFlag table lifecycle) ownerFound installed |
    Unloading accumulator view outcome =
      MkInstalledCommittedSnapshot (viewProviders view)
        (MkCommittedSnapshot
          (MkFiber component parent retiredFlag table
            (Unloading accumulator view outcome))
          ownerFound view Refl Refl) Refl

public export
0 snapshotResolvesRelianceAnchor :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (wanted : key) -> (provider : name) ->
  (snapshot : CommittedSnapshot name key world error value nameEq actor
    providers state) ->
  viewLookup @{keyEq} wanted
    (dependencies (componentDependencies (fiberComponent
      (committedFiber snapshot))))
    (committedView snapshot) = Just provider ->
  resolvedProviderAt @{nameEq} @{keyEq} actor wanted provider state = True
snapshotResolvesRelianceAnchor nameEq keyEq actor wanted provider
  (MkCommittedSnapshot
    (MkFiber component parent retiredFlag table lifecycle) found view committedView
      providerNames) resolved =
    rewrite found in
    rewrite committedView in
    rewrite resolved in sameProvider
  where
    sameProvider : (case decEq @{nameEq} provider provider of
      Yes Refl => True
      No _ => False) = True
    sameProvider with (decEq @{nameEq} provider provider)
      sameProvider | Yes Refl = Refl
      sameProvider | No distinct = void (distinct Refl)

0 falseNotTrueRelianceSnapshot : False = True -> Void
falseNotTrueRelianceSnapshot Refl impossible

0 fiberResolvesRelianceSnapshot :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (provider : name) ->
  Fiber name key value world error -> Bool
fiberResolvesRelianceSnapshot nameEq keyEq wanted provider
  (MkFiber component parent retiredFlag table lifecycle) =
    case committed lifecycle of
      Nothing => False
      Just view => case viewLookup @{keyEq} wanted
        (dependencies (componentDependencies component)) view of
          Nothing => False
          Just actual => case decEq @{nameEq} actual provider of
            Yes Refl => True
            No _ => False

0 resolvedMaybeFiberRelianceSnapshot :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (provider : name) ->
  Maybe (Fiber name key value world error) -> Bool
resolvedMaybeFiberRelianceSnapshot nameEq keyEq wanted provider Nothing = False
resolvedMaybeFiberRelianceSnapshot nameEq keyEq wanted provider (Just fiber) =
  fiberResolvesRelianceSnapshot nameEq keyEq wanted provider fiber

0 resolvedAtLookupRelianceSnapshot :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (wanted : key) -> (provider : name) ->
  (state : SystemState name key value world error) ->
  resolvedProviderAt @{nameEq} @{keyEq} actor wanted provider state =
    resolvedMaybeFiberRelianceSnapshot {name = name} {key = key}
      {value = value} {world = world} {error = error} nameEq keyEq wanted
      provider (lookupFiber @{nameEq} {name = name} {key = key}
        {value = value} {world = world} {error = error} actor (registry state))
resolvedAtLookupRelianceSnapshot nameEq keyEq actor wanted provider
  state@(MkSystemState ambient fibers)
  with (lookupFiber @{nameEq} actor fibers)
  resolvedAtLookupRelianceSnapshot nameEq keyEq actor wanted provider
    state@(MkSystemState ambient fibers) | Nothing = Refl
  resolvedAtLookupRelianceSnapshot nameEq keyEq actor wanted provider
    state@(MkSystemState ambient fibers) |
    Just (MkFiber component parent retiredFlag table (Inactive outcome)) = Refl
  resolvedAtLookupRelianceSnapshot nameEq keyEq actor wanted provider
    state@(MkSystemState ambient fibers) |
    Just (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator view))
    with (viewLookup @{keyEq} wanted
      (dependencies (componentDependencies component)) view)
    resolvedAtLookupRelianceSnapshot nameEq keyEq actor wanted provider
      state@(MkSystemState ambient fibers) |
      Just (MkFiber component parent retiredFlag table
        (Reloading remaining accumulator view)) | Nothing = Refl
    resolvedAtLookupRelianceSnapshot nameEq keyEq actor wanted provider
      state@(MkSystemState ambient fibers) |
      Just (MkFiber component parent retiredFlag table
        (Reloading remaining accumulator view)) | Just actual
      with (decEq @{nameEq} actual provider)
      resolvedAtLookupRelianceSnapshot nameEq keyEq actor wanted provider
        state@(MkSystemState ambient fibers) |
        Just (MkFiber component parent retiredFlag table
          (Reloading remaining accumulator view)) | Just provider | Yes Refl = Refl
      resolvedAtLookupRelianceSnapshot nameEq keyEq actor wanted provider
        state@(MkSystemState ambient fibers) |
        Just (MkFiber component parent retiredFlag table
          (Reloading remaining accumulator view)) | Just actual | No distinct = Refl
  resolvedAtLookupRelianceSnapshot nameEq keyEq actor wanted provider
    state@(MkSystemState ambient fibers) |
    Just (MkFiber component parent retiredFlag table
      (Active accumulator view))
    with (viewLookup @{keyEq} wanted
      (dependencies (componentDependencies component)) view)
    resolvedAtLookupRelianceSnapshot nameEq keyEq actor wanted provider
      state@(MkSystemState ambient fibers) |
      Just (MkFiber component parent retiredFlag table
        (Active accumulator view)) | Nothing = Refl
    resolvedAtLookupRelianceSnapshot nameEq keyEq actor wanted provider
      state@(MkSystemState ambient fibers) |
      Just (MkFiber component parent retiredFlag table
        (Active accumulator view)) | Just actual
      with (decEq @{nameEq} actual provider)
      resolvedAtLookupRelianceSnapshot nameEq keyEq actor wanted provider
        state@(MkSystemState ambient fibers) |
        Just (MkFiber component parent retiredFlag table
          (Active accumulator view)) | Just provider | Yes Refl = Refl
      resolvedAtLookupRelianceSnapshot nameEq keyEq actor wanted provider
        state@(MkSystemState ambient fibers) |
        Just (MkFiber component parent retiredFlag table
          (Active accumulator view)) | Just actual | No distinct = Refl
  resolvedAtLookupRelianceSnapshot nameEq keyEq actor wanted provider
    state@(MkSystemState ambient fibers) |
    Just (MkFiber component parent retiredFlag table
      (Unloading accumulator view outcome))
    with (viewLookup @{keyEq} wanted
      (dependencies (componentDependencies component)) view)
    resolvedAtLookupRelianceSnapshot nameEq keyEq actor wanted provider
      state@(MkSystemState ambient fibers) |
      Just (MkFiber component parent retiredFlag table
        (Unloading accumulator view outcome)) | Nothing = Refl
    resolvedAtLookupRelianceSnapshot nameEq keyEq actor wanted provider
      state@(MkSystemState ambient fibers) |
      Just (MkFiber component parent retiredFlag table
        (Unloading accumulator view outcome)) | Just actual
      with (decEq @{nameEq} actual provider)
      resolvedAtLookupRelianceSnapshot nameEq keyEq actor wanted provider
        state@(MkSystemState ambient fibers) |
        Just (MkFiber component parent retiredFlag table
          (Unloading accumulator view outcome)) | Just provider | Yes Refl = Refl
      resolvedAtLookupRelianceSnapshot nameEq keyEq actor wanted provider
        state@(MkSystemState ambient fibers) |
        Just (MkFiber component parent retiredFlag table
          (Unloading accumulator view outcome)) | Just actual | No distinct = Refl

0 resolvedFiberFromFoundRelianceSnapshot :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (wanted : key) -> (provider : name) ->
  (state : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor (registry state) = Just fiber ->
  resolvedProviderAt @{nameEq} @{keyEq} actor wanted provider state = True ->
  fiberResolvesRelianceSnapshot nameEq keyEq wanted provider fiber = True
resolvedFiberFromFoundRelianceSnapshot nameEq keyEq actor wanted provider state
  fiber found resolved =
    trans
      (sym (cong
        (resolvedMaybeFiberRelianceSnapshot nameEq keyEq wanted provider) found))
      (trans
        (sym (resolvedAtLookupRelianceSnapshot nameEq keyEq actor wanted provider
          state)) resolved)

public export
0 snapshotLookupFromResolvedRelianceAnchor :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (wanted : key) -> (provider : name) ->
  (snapshot : CommittedSnapshot name key world error value nameEq actor
    providers state) ->
  resolvedProviderAt @{nameEq} @{keyEq} actor wanted provider state = True ->
  viewLookup @{keyEq} wanted
    (dependencies (componentDependencies
      (fiberComponent (committedFiber snapshot))))
    (committedView snapshot) = Just provider
snapshotLookupFromResolvedRelianceAnchor nameEq keyEq actor wanted provider
  (MkCommittedSnapshot
    (MkFiber component parent retiredFlag table (Inactive outcome)) found view
      committedView providerNames) resolved = case committedView of Refl impossible
snapshotLookupFromResolvedRelianceAnchor nameEq keyEq actor wanted provider
  (MkCommittedSnapshot
    (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator actualView)) found view committedView
      providerNames) resolved =
        case justInjective committedView of
          Refl => resolvedLookup (resolvedFiberFromFoundRelianceSnapshot nameEq
            keyEq actor wanted provider state
            (MkFiber component parent retiredFlag table
              (Reloading remaining accumulator actualView)) found resolved)
  where
    resolvedLookup : fiberResolvesRelianceSnapshot nameEq keyEq wanted provider
      (MkFiber component parent retiredFlag table
        (Reloading remaining accumulator actualView)) = True ->
      viewLookup @{keyEq} wanted
        (dependencies (componentDependencies component)) actualView = Just provider
    resolvedLookup fiberResolved with (viewLookup @{keyEq} wanted
      (dependencies (componentDependencies component)) actualView) proof observed
      resolvedLookup fiberResolved | Nothing = case fiberResolved of Refl impossible
      resolvedLookup fiberResolved | Just actual with (decEq @{nameEq} actual provider)
        resolvedLookup fiberResolved | Just actual | Yes same =
          cong Just same
        resolvedLookup fiberResolved | Just actual | No distinct =
          case fiberResolved of Refl impossible
snapshotLookupFromResolvedRelianceAnchor nameEq keyEq actor wanted provider
  (MkCommittedSnapshot
    (MkFiber component parent retiredFlag table (Active accumulator actualView))
      found view committedView providerNames) resolved =
        case justInjective committedView of
          Refl => resolvedLookup (resolvedFiberFromFoundRelianceSnapshot nameEq
            keyEq actor wanted provider state
            (MkFiber component parent retiredFlag table
              (Active accumulator actualView)) found resolved)
  where
    resolvedLookup : fiberResolvesRelianceSnapshot nameEq keyEq wanted provider
      (MkFiber component parent retiredFlag table
        (Active accumulator actualView)) = True ->
      viewLookup @{keyEq} wanted
        (dependencies (componentDependencies component)) actualView = Just provider
    resolvedLookup fiberResolved with (viewLookup @{keyEq} wanted
      (dependencies (componentDependencies component)) actualView) proof observed
      resolvedLookup fiberResolved | Nothing = case fiberResolved of Refl impossible
      resolvedLookup fiberResolved | Just actual with (decEq @{nameEq} actual provider)
        resolvedLookup fiberResolved | Just actual | Yes same =
          cong Just same
        resolvedLookup fiberResolved | Just actual | No distinct =
          case fiberResolved of Refl impossible
snapshotLookupFromResolvedRelianceAnchor nameEq keyEq actor wanted provider
  (MkCommittedSnapshot
    (MkFiber component parent retiredFlag table
      (Unloading accumulator actualView outcome)) found view committedView
      providerNames) resolved =
        case justInjective committedView of
          Refl => resolvedLookup (resolvedFiberFromFoundRelianceSnapshot nameEq
            keyEq actor wanted provider state
            (MkFiber component parent retiredFlag table
              (Unloading accumulator actualView outcome)) found resolved)
  where
    resolvedLookup : fiberResolvesRelianceSnapshot nameEq keyEq wanted provider
      (MkFiber component parent retiredFlag table
        (Unloading accumulator actualView outcome)) = True ->
      viewLookup @{keyEq} wanted
        (dependencies (componentDependencies component)) actualView = Just provider
    resolvedLookup fiberResolved with (viewLookup @{keyEq} wanted
      (dependencies (componentDependencies component)) actualView) proof observed
      resolvedLookup fiberResolved | Nothing = case fiberResolved of Refl impossible
      resolvedLookup fiberResolved | Just actual with (decEq @{nameEq} actual provider)
        resolvedLookup fiberResolved | Just actual | Yes same =
          cong Just same
        resolvedLookup fiberResolved | Just actual | No distinct =
          case fiberResolved of Refl impossible

public export
0 consumerResolutionEndRelianceAnchor :
  (trace : Transitions first finalState) ->
  ConsumerResolutionConstant name key world error value nameEq keyEq actor wanted
    provider trace ->
  resolvedProviderAt @{nameEq} @{keyEq} actor wanted provider finalState = True
consumerResolutionEndRelianceAnchor NoTransitions
  (ResolutionConstantEnd finalResolved) = finalResolved
consumerResolutionEndRelianceAnchor
  (MoreTransitions transition rest)
  (ResolutionConstantStep transition rest sourceResolved tail) =
    consumerResolutionEndRelianceAnchor rest tail
