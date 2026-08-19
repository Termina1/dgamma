module DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceObservation

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import Decidable.Equality

%default total

public export
0 viewLookupImpliesContainsRelianceAnchor :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (deps : List key) -> (view : View name deps) ->
  (provider : name) ->
  viewLookup @{keyEq} wanted deps view = Just provider ->
  viewContains @{nameEq} provider view = True
viewLookupImpliesContainsRelianceAnchor nameEq keyEq wanted [] EmptyView provider
  found = case found of Refl impossible
viewLookupImpliesContainsRelianceAnchor nameEq keyEq wanted (current :: rest)
  (ProviderView currentProvider tail) provider found
  with (decEq @{keyEq} wanted current)
  viewLookupImpliesContainsRelianceAnchor nameEq keyEq current (current :: rest)
    (ProviderView currentProvider tail) provider found | Yes Refl =
      case justInjective found of
        Refl => sameProvider
    where
      sameProvider : viewContains @{nameEq} currentProvider
        (ProviderView currentProvider tail) = True
      sameProvider with (decEq @{nameEq} currentProvider currentProvider)
        sameProvider | Yes Refl = Refl
        sameProvider | No distinct = void (distinct Refl)
  viewLookupImpliesContainsRelianceAnchor nameEq keyEq wanted (current :: rest)
    (ProviderView currentProvider tail) provider found | No wantedDistinct
    with (decEq @{nameEq} provider currentProvider)
    viewLookupImpliesContainsRelianceAnchor nameEq keyEq wanted (current :: rest)
      (ProviderView provider tail) provider found | No wantedDistinct |
      Yes Refl = Refl
    viewLookupImpliesContainsRelianceAnchor nameEq keyEq wanted (current :: rest)
      (ProviderView currentProvider tail) provider found | No wantedDistinct |
      No providerDistinct = viewLookupImpliesContainsRelianceAnchor nameEq keyEq
        wanted rest tail provider found

public export
0 reliedHeadFromSnapshotRelianceAnchor :
  (nameEq : DecEq name) -> (selected, actor : name) ->
  Not (actor = selected) ->
  (snapshot : CommittedSnapshot name key world error value nameEq actor
    providers state) ->
  viewContains @{nameEq} selected (committedView snapshot) = True ->
  reliedHead @{nameEq} selected selected
    (Bind actor (committedFiber snapshot)) = True
reliedHeadFromSnapshotRelianceAnchor nameEq selected actor actorDistinct
  (MkCommittedSnapshot
    (MkFiber component parent retiredFlag table (Inactive outcome)) found view
      committedView providerNames) contains = case committedView of Refl impossible
reliedHeadFromSnapshotRelianceAnchor nameEq selected actor actorDistinct
  (MkCommittedSnapshot
    (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator actualView)) found view committedView
      providerNames) contains =
    case justInjective committedView of
      Refl => distinctHead contains
  where
    distinctHead : viewContains @{nameEq} selected actualView = True ->
      reliedHead @{nameEq} selected selected
        (Bind actor (MkFiber component parent retiredFlag table
          (Reloading remaining accumulator actualView))) = True
    distinctHead sees with (decEq @{nameEq} actor selected)
      distinctHead sees | Yes same = void (actorDistinct same)
      distinctHead sees | No _ = rewrite sees in Refl
reliedHeadFromSnapshotRelianceAnchor nameEq selected actor actorDistinct
  (MkCommittedSnapshot
    (MkFiber component parent retiredFlag table (Active accumulator actualView))
      found view committedView providerNames) contains =
    case justInjective committedView of
      Refl => distinctHead contains
  where
    distinctHead : viewContains @{nameEq} selected actualView = True ->
      reliedHead @{nameEq} selected selected
        (Bind actor (MkFiber component parent retiredFlag table
          (Active accumulator actualView))) = True
    distinctHead sees with (decEq @{nameEq} actor selected)
      distinctHead sees | Yes same = void (actorDistinct same)
      distinctHead sees | No _ = rewrite sees in Refl
reliedHeadFromSnapshotRelianceAnchor nameEq selected actor actorDistinct
  (MkCommittedSnapshot
    (MkFiber component parent retiredFlag table
      (Unloading accumulator actualView outcome)) found view committedView
      providerNames) contains =
    case justInjective committedView of
      Refl => distinctHead contains
  where
    distinctHead : viewContains @{nameEq} selected actualView = True ->
      reliedHead @{nameEq} selected selected
        (Bind actor (MkFiber component parent retiredFlag table
          (Unloading accumulator actualView outcome))) = True
    distinctHead sees with (decEq @{nameEq} actor selected)
      distinctHead sees | Yes same = void (actorDistinct same)
      distinctHead sees | No _ = rewrite sees in Refl
