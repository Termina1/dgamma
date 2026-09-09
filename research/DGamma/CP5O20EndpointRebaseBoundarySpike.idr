module DGamma.CP5O20EndpointRebaseBoundarySpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O20AllNameSynchronizationSpike
import DGamma.CP5O20EpisodeSynchronizationSpike
import DGamma.CP5O20HistoryNameTransportSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import Data.List
import Decidable.Equality

%default total
%unbound_implicits off

||| Identity name transport preserves an arbitrary provider word. This
||| structural proof is used for all four native lifecycle constructors.
export
0 o20IdentityProviderWord :
  {name : Type} -> (providers : List name) ->
  (map (renameForward (identityNameBijection {name})) providers = providers)
o20IdentityProviderWord [] = Refl
o20IdentityProviderWord (provider :: rest) = cong (provider ::) (o20IdentityProviderWord rest)

||| Both native parent constructors are related by the literal identity map.
export
0 o20IdentityParent :
  {name : Type} -> (parent : Parent name) ->
  ParentRelatedBy identityNameBijection parent parent
o20IdentityParent Root = RootsRelated
o20IdentityParent (ChildOf selected) = ChildrenRelated Refl

||| Exact identity-renamed lifecycle relation for every native constructor,
||| including the real accumulator's runtime observations and committed view.
export
0 o20IdentityLifecycle :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {deps : List key} -> {provision : CoeffectSpec key} ->
  (lifecycle : Lifecycle key value world error name deps provision) ->
  LifecycleRelatedBy identityNameBijection lifecycle lifecycle
o20IdentityLifecycle (Inactive outcome) = RenamedInactive Refl
o20IdentityLifecycle (Reloading remaining accumulator view) =
  RenamedReloading Refl (\input => localStateRuntimeReflexive (accumulator input))
    (o20IdentityProviderWord (viewProviders view))
o20IdentityLifecycle {error} (Active accumulator view) =
  RenamedActive {error} (\input => localStateRuntimeReflexive (accumulator input))
    (o20IdentityProviderWord (viewProviders view))
o20IdentityLifecycle (Unloading accumulator view outcome) =
  RenamedUnloading (\input => localStateRuntimeReflexive (accumulator input))
    (o20IdentityProviderWord (viewProviders view)) Refl

||| Full identity-renamed fiber control at one ACTUAL fiber value; no
||| independently reconstructed registry or erased uniqueness proof occurs.
export
0 o20IdentityFiber :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (fiber : Fiber name key value world error) ->
  FiberRelatedBy identityNameBijection fiber fiber
o20IdentityFiber (MkFiber component parent retiredFlag table lifecycle) =
  RenamedFibers parent parent retiredFlag retiredFlag table table lifecycle lifecycle
    (o20IdentityParent parent) Refl (o20IdentityLifecycle lifecycle)

||| Both actual lookup outcomes have full identity-renamed controls.
export
0 o20IdentityMaybeFiber :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (observed : Maybe (Fiber name key value world error)) ->
  MaybeFiberRelatedBy identityNameBijection observed observed
o20IdentityMaybeFiber Nothing = RenamedAbsent
o20IdentityMaybeFiber (Just fiber) = RenamedPresent (o20IdentityFiber fiber)

||| ANY single runtime state owns its identity ALL-name cut, not merely
||| supported or present entries. Both endpoints are the SAME state value.
export
0 o20IdentityAllNameCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (state : SystemState name key value world error) ->
  O20AllNameCut name key world error value nameEq identityNameBijection state state
o20IdentityAllNameCut {name} {key} {world} {error} {value} nameEq state =
  MkO20AllNameCut (MkRenamedRuntimeEffects Refl (\selected => Refl))
    (\selected => o20IdentityMaybeFiber
      (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry state)))

||| An actual trace scanned against itself owns an internal identity history
||| cut at BOTH authentic final generation environments. This is not a cut
||| at the supplied current endpoint bijection; that rebasing is separate.
export
0 o20IdentityHistoryCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq identityRegistrationGenerationBijection trace trace) ->
  O20HistoryCut name key world error value nameEq identityRegistrationGenerationBijection
    (leftFinalGenerations registrations) (rightFinalGenerations registrations) finalState finalState
o20IdentityHistoryCut {name} {key} {world} {error} {value} {finalState} nameEq trace registrations =
  MkO20HistoryCut identityNameBijection (o20IdentityAllNameCut nameEq finalState)
    (\selected, stamp, found => sym (cong generationName (currentBirthStampExact
      (acceptedLeftCurrentBirth name key world error value nameEq trace trace identityRegistrationGenerationBijection
        registrations selected stamp found))))
    (\selected, stamp, found => sym (cong generationName (currentBirthStampExact
      (acceptedRightCurrentBirth name key world error value nameEq trace trace identityRegistrationGenerationBijection
        registrations selected stamp found))))

||| Exact Maybe-fiber renaming never relates a present fiber to absence.
||| A full vestigial packet is a different relation, not this constructor.
export
0 o20PresentAbsentImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {renaming : NameBijection name} -> {fiber : Fiber name key value world error} ->
  MaybeFiberRelatedBy renaming (Just fiber) Nothing -> Void
o20PresentAbsentImpossible RenamedAbsent impossible
o20PresentAbsentImpossible (RenamedPresent related) impossible

||| Two primitive lookup observations refute an ALL-name cut whose supplied
||| map sends a real present fiber to absence. No support predicate is used.
export
0 o20CutRejectsPresentAbsent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (renaming : NameBijection name) ->
  (left, right : SystemState name key value world error) ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry left) = Just fiber) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq}
    (renameForward renaming selected) (registry right) = Nothing) ->
  O20AllNameCut name key world error value nameEq renaming left right -> Void
o20CutRejectsPresentAbsent nameEq renaming left right selected fiber present absent cut =
  o20PresentAbsentImpossible {renaming} {fiber}
    (rewrite (sym present) in rewrite (sym absent) in allNameControls cut selected)

||| Observe the accepted endpoint partition. A genuine history/current name
||| disagreement forces its FULL original vestigial packet; unsupportedness
||| or discarded-generation membership alone is not substituted for its fields.
export
0 o20DisagreementVestigialChoice :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  (current : CurrentEndpointRenaming nameEq keyEq mapping left right registrations) ->
  (selected : name) -> (stamp : RegistrationGeneration name) ->
  Not (o20HistoricalTarget mapping stamp = renameForward (currentNameBijection current) selected) ->
  Either
    (VestigialEndpointGeneration name key world error value nameEq keyEq
      (leftFinalGenerations registrations) (leftDeletedGenerations registrations) selected leftFinal)
    (o20HistoricalTarget mapping stamp = renameForward (currentNameBijection current) selected) ->
  VestigialEndpointGeneration name key world error value nameEq keyEq
    (leftFinalGenerations registrations) (leftDeletedGenerations registrations) selected leftFinal
o20DisagreementVestigialChoice mapping registrations current selected stamp different (Left vestigial) = vestigial
o20DisagreementVestigialChoice mapping registrations current selected stamp different (Right same) = void (different same)
