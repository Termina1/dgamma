module DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceResolved

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Data.List.Elem
import Decidable.Equality

%default total

0 fiberValueMaybeRelianceAnchor :
  (keyEq : DecEq key) -> (wanted : key) ->
  Maybe (Fiber name key value world error) -> Maybe (value wanted)
fiberValueMaybeRelianceAnchor keyEq wanted Nothing = Nothing
fiberValueMaybeRelianceAnchor keyEq wanted (Just fiber) =
  lookupBinding @{keyEq} wanted (ownedValues (fiberTable fiber))

0 providerValueAtLookupRelianceAnchor :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider : name) -> (wanted : key) ->
  (state : SystemState name key value world error) ->
  providerValueAt @{nameEq} @{keyEq} provider wanted state =
    fiberValueMaybeRelianceAnchor {name = name} {key = key} {value = value}
      {world = world} {error = error} keyEq wanted
      (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
        {world = world} {error = error} provider (registry state))
providerValueAtLookupRelianceAnchor nameEq keyEq provider wanted
  state@(MkSystemState ambient fibers)
  with (lookupFiber @{nameEq} provider fibers)
  providerValueAtLookupRelianceAnchor nameEq keyEq provider wanted
    state@(MkSystemState ambient fibers) | Nothing = Refl
  providerValueAtLookupRelianceAnchor nameEq keyEq provider wanted
    state@(MkSystemState ambient fibers) |
    Just (MkFiber component parent retiredFlag table lifecycle)
    with (lookupBinding @{keyEq} wanted (ownedValues table))
    providerValueAtLookupRelianceAnchor nameEq keyEq provider wanted
      state@(MkSystemState ambient fibers) |
      Just (MkFiber component parent retiredFlag table lifecycle) | Nothing = Refl
    providerValueAtLookupRelianceAnchor nameEq keyEq provider wanted
      state@(MkSystemState ambient fibers) |
      Just (MkFiber component parent retiredFlag table lifecycle) | Just found = Refl

0 providerValueAtFoundRelianceAnchor :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider : name) -> (wanted : key) ->
  (state : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} provider (registry state) = Just fiber ->
  providerValueAt @{nameEq} @{keyEq} provider wanted state =
    fiberValueMaybeRelianceAnchor keyEq wanted (Just fiber)
providerValueAtFoundRelianceAnchor nameEq keyEq provider wanted state fiber found =
  trans (providerValueAtLookupRelianceAnchor nameEq keyEq provider wanted state)
    (cong (fiberValueMaybeRelianceAnchor keyEq wanted) found)

0 lookupBindingJustElemRelianceAnchor :
  (keyEq : DecEq key) -> (wanted : key) ->
  (table : CoeffectContext key value) -> (provided : value wanted) ->
  lookupBinding @{keyEq} wanted table = Just provided ->
  Elem wanted (bindingKeys (bindings table))
lookupBindingJustElemRelianceAnchor keyEq wanted
  (MkCoeffectContext entries unique) provided found =
    lookupJustElem @{keyEq} wanted entries provided found

public export
0 resolvedProviderDeclaresRelianceAnchor :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider : name) -> (wanted : key) ->
  (state : SystemState name key value world error) ->
  (resolved : ResolvedProviderData name key world error value nameEq keyEq
    actor wanted provider state) ->
  Elem wanted (dependencies (componentProvisions
    (fiberComponent (resolvedProviderFiber resolved))))
resolvedProviderDeclaresRelianceAnchor nameEq keyEq provider wanted state
  (MkResolvedProviderData
    providerFiber@(MkFiber component parent retiredFlag table lifecycle)
    providerFound providerStable provided valuePresent providerInstalled) =
      let 0 valueAtFiber :
            (lookupBinding @{keyEq} wanted (ownedValues table) = Just provided)
          valueAtFiber = trans
            (sym (providerValueAtFoundRelianceAnchor nameEq keyEq provider wanted
              state providerFiber providerFound))
            valuePresent
          0 tableMember : Elem wanted
            (bindingKeys (bindings (ownedValues table)))
          tableMember = lookupBindingJustElemRelianceAnchor keyEq wanted
            (ownedValues table) provided valueAtFiber
      in ownedSound table wanted tableMember
