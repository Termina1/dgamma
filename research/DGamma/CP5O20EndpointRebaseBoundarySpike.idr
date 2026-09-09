module DGamma.CP5O20EndpointRebaseBoundarySpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O20AllNameSynchronizationSpike
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
