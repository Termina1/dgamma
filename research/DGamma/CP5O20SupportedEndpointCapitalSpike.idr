module DGamma.CP5O20SupportedEndpointCapitalSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionControlCore
import DGamma.CP4DeletionSelectedForeignControlCore
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5O20SupportedBirthBridgeSpike
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| ORIGINAL support reaches actual canonical support through this very
||| schedule's block, not an assumed endpoint support-preservation oracle.
export
0 canonicalSupportedTruthFromOriginal :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (original : Transitions initial finalState) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  (selected : name) ->
  isSupported @{nameEq} @{keyEq} selected finalState = True ->
  isSupported @{nameEq} @{keyEq} selected (canonicalFinal (canonicalSchedule capital)) = True
canonicalSupportedTruthFromOriginal name key world error value nameEq keyEq protocol original capital selected supported =
  trans (replaySupportMatchesActive (canonicalReplayPremises capital) selected)
    (blockActiveAtFinal (canonicalBlock (canonicalSchedule capital) selected
      (orderComplete (supportLinearization (canonicalSchedule capital)) selected supported)))

||| Actual supported canonical lookup with endpoint facts. The stored view
||| invariant concerns the actual registry; it does not compare two schedules.
public export
record SupportedCanonicalEndpointView
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (state : SystemState name key value world error) where
  constructor MkSupportedCanonicalEndpointView
  supportedCanonicalFiber : Fiber name key value world error
  0 supportedCanonicalFound : lookupFiber @{nameEq} selected (registry state) = Just supportedCanonicalFiber
  0 supportedCanonicalTruth : isSupported @{nameEq} @{keyEq} selected state = True
  0 supportedCanonicalActive : supportedActiveAt @{nameEq} selected state = True
  0 supportedCanonicalNotRetired : retired supportedCanonicalFiber = False
  0 supportedCanonicalViewDomain : fiberViewInvariant @{nameEq} @{keyEq} supportedCanonicalFiber (registry state) = True

||| All fields come from actual computed support and this canonical replay's
||| preserved well-formedness. No canonical lookup or activity oracle is taken.
export
0 canonicalSupportedEndpointView :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (original : Transitions initial finalState) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  (selected : name) ->
  isSupported @{nameEq} @{keyEq} selected finalState = True ->
  SupportedCanonicalEndpointView name key world error value nameEq keyEq selected (canonicalFinal (canonicalSchedule capital))
canonicalSupportedEndpointView name key world error value nameEq keyEq protocol original capital selected supported =
  case computedSupportPresent name key world error value nameEq keyEq
    (canonicalFinal (canonicalSchedule capital)) selected
    (canonicalSupportedTruthFromOriginal name key world error value nameEq keyEq protocol original capital selected supported) of
    (fiber ** found) => MkSupportedCanonicalEndpointView fiber found
      (canonicalSupportedTruthFromOriginal name key world error value nameEq keyEq protocol original capital selected supported)
      (blockActiveAtFinal (canonicalBlock (canonicalSchedule capital) selected
        (orderComplete (supportLinearization (canonicalSchedule capital)) selected supported)))
      (computedSupportNotRetired name key world error value nameEq keyEq
        (canonicalFinal (canonicalSchedule capital)) selected fiber found
        (canonicalSupportedTruthFromOriginal name key world error value nameEq keyEq protocol original capital selected supported))
      (wellFormedFiberView nameEq keyEq selected (canonicalFinal (canonicalSchedule capital)) fiber found
        (replayFinalWellFormed (canonicalReplayPremises capital)))

||| Eliminate a raw withdrawal already PROVIDED by the canonical endpoint;
||| do not manufacture an O21 absent/present generation-withdrawal branch.
export
0 canonicalPresentOutsideWithdrawals :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (originalFinal, canonicalFinal : SystemState name key value world error) ->
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq originalFinal canonicalFinal) ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry canonicalFinal) = Just fiber ->
  Not (Elem selected (endpointWithdrawnNames endpoint))
canonicalPresentOutsideWithdrawals name key world error value nameEq keyEq originalFinal canonicalFinal endpoint selected fiber found member =
  case endpointNamesWithdrawn endpoint selected member of
    VestigialNameWithdrawn _ _ _ _ _ absent =>
      case trans (sym absent) found of Refl impossible
    NameAlreadyAbsent _ absent =>
      case trans (sym absent) found of Refl impossible

||| Recover the actual ORIGINAL fiber and full same-name control relation
||| from canonical presence. This is strictly one-sided, not an R147 bridge.
export
0 canonicalSupportedOriginalControl :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (original : Transitions initial finalState) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  (selected : name) ->
  (view : SupportedCanonicalEndpointView name key world error value nameEq keyEq selected (canonicalFinal (canonicalSchedule capital))) ->
  ForeignRelatedFiberFound name key world error value nameEq selected
    (registry (canonicalFinal (canonicalSchedule capital))) (registry finalState) (supportedCanonicalFiber view)
canonicalSupportedOriginalControl name key world error value nameEq keyEq protocol original capital selected view =
  foreignControlLookupFound nameEq selected (registry (canonicalFinal (canonicalSchedule capital)))
    (registry finalState) (supportedCanonicalFiber view) (supportedCanonicalFound view)
    (fiberControlMaybeSymmetric (endpointControlsOutside (canonicalEndpoint (canonicalSchedule capital)) selected
      (canonicalPresentOutsideWithdrawals name key world error value nameEq keyEq finalState
        (canonicalFinal (canonicalSchedule capital)) (canonicalEndpoint (canonicalSchedule capital)) selected
        (supportedCanonicalFiber view) (supportedCanonicalFound view))))

||| Reify the actual Active accumulator/view and retain its actual registry
||| domain proof. No two accumulators or provider names are compared here.
export
0 activeFiberViewDomain :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  isActive (fiberLifecycle fiber) = True ->
  fiberViewInvariant @{nameEq} @{keyEq} fiber fibers = True ->
  (accumulator : (LocalState key value world (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world (componentProvisions (fiberComponent fiber))) **
   view : View name (dependencies (componentDependencies (fiberComponent fiber))) **
   (fiberLifecycle fiber = Active {key = key} {value = value} {world = world} {error = error} {name = name} accumulator view,
    viewBindingsInvariant {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq}
      (dependencies (componentDependencies (fiberComponent fiber))) view fibers = True))
activeFiberViewDomain name key world error value nameEq keyEq
  (MkFiber component parent retiredFlag table (Inactive outcome)) fibers Refl valid impossible
activeFiberViewDomain name key world error value nameEq keyEq
  (MkFiber component parent retiredFlag table (Reloading rest accumulator view)) fibers Refl valid impossible
activeFiberViewDomain name key world error value nameEq keyEq
  (MkFiber component parent retiredFlag table (Active accumulator view)) fibers active valid =
    (accumulator ** view ** (Refl, valid))
activeFiberViewDomain name key world error value nameEq keyEq
  (MkFiber component parent retiredFlag table (Unloading accumulator view outcome)) fibers Refl valid impossible

||| Consumer of the producer-owned lookup packet: exact Active payload plus
||| stable-provider and resolvable-coeffect-domain conjunction at THIS endpoint.
export
0 supportedCanonicalCommittedView :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) -> (selected : name) ->
  (packet : SupportedCanonicalEndpointView name key world error value nameEq keyEq selected state) ->
  (accumulator : (LocalState key value world (componentProvisions (fiberComponent (supportedCanonicalFiber packet))) ->
    LocalState key value world (componentProvisions (fiberComponent (supportedCanonicalFiber packet)))) **
   view : View name (dependencies (componentDependencies (fiberComponent (supportedCanonicalFiber packet)))) **
   (fiberLifecycle (supportedCanonicalFiber packet) = Active {key = key} {value = value} {world = world} {error = error} {name = name} accumulator view,
    viewBindingsInvariant {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq}
      (dependencies (componentDependencies (fiberComponent (supportedCanonicalFiber packet)))) view (registry state) = True))
supportedCanonicalCommittedView name key world error value nameEq keyEq state selected packet =
  activeFiberViewDomain name key world error value nameEq keyEq (supportedCanonicalFiber packet) (registry state)
    (trans (sym (the
      (supportedActiveAt @{nameEq} selected state = isActive (fiberLifecycle (supportedCanonicalFiber packet)))
      (rewrite supportedCanonicalFound packet in Refl))) (supportedCanonicalActive packet))
    (supportedCanonicalViewDomain packet)
