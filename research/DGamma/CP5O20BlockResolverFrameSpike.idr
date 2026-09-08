module DGamma.CP5O20BlockResolverFrameSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorTrace
import DGamma.CP5O19ActivationResolutionSpike
import DGamma.CP5O19InsertObservationSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP4DeletionFrameCore
import DGamma.CP5O20RightOpeningTransportSpike
import DGamma.CP5O20SelectorResolverFrameSpike
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Installed evidence yields physical presence by one explicit primitive
||| lookup observation. No existential fiber producer is eliminated.
export
0 o20InstalledLookupPresentObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (state : SystemState name key value world error) ->
  (installedAt {name} {key} {value} {world} {error} @{nameEq} actor state = True) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry state) = observed) ->
  (isJust (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry state)) = True)
o20InstalledLookupPresentObserved {name} {key} {world} {error} {value} nameEq actor state installed Nothing found =
  absurd (trans (sym (the (installedAt {name} {key} {value} {world} {error} @{nameEq} actor state = False)
    (rewrite found in Refl))) installed)
o20InstalledLookupPresentObserved nameEq actor state installed (Just fiber) found = rewrite found in Refl

||| The native owned head of an installed segment preserves a disjoint
||| dependency resolver. Its immutable component is transported from the
||| ACTUAL segment endpoint through InstalledTrace, not supplied per cut.
export
0 o20InstalledHeadResolverObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) -> (deps : List key) ->
  (before, middle, finalState : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} action before = Just (tag, middle)) ->
  (actionOwner action = actor) ->
  (rest : Transitions middle finalState) ->
  (installedAt {name} {key} {value} {world} {error} @{nameEq} actor before = True) ->
  InstalledTrace name key world error value nameEq keyEq actor rest ->
  (lastFiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry finalState) = Just lastFiber) ->
  ((wanted : key) -> Elem wanted deps -> Not (Elem wanted (dependencies (componentProvisions (fiberComponent lastFiber))))) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before) = observed) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps (registry middle) =
   resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps (registry before))
o20InstalledHeadResolverObserved {name} {key} {world} {error} {value} nameEq keyEq actor deps before middle finalState
  action tag checked owned rest installed tailInstalled lastFiber lastFound excluded Nothing found =
    absurd (trans (sym (the (installedAt {name} {key} {value} {world} {error} @{nameEq} actor before = False)
      (rewrite found in Refl))) installed)
o20InstalledHeadResolverObserved {name} {key} {world} {error} {value} nameEq keyEq actor deps before middle finalState
  action tag checked owned rest installed tailInstalled lastFiber lastFound excluded (Just old) found =
    o19ResolvePresentLocalUpdate nameEq keyEq deps actor (registry before) (registry middle) old found
      (o20InstalledLookupPresentObserved nameEq actor middle (installedTraceStart tailInstalled)
        (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry middle)) Refl)
      (replace {p = \selected => RegistryLocalUpdate name key world error value nameEq selected (registry before) (registry middle)} owned
        (systemRegistryUpdate (applyActionLocalUpdate nameEq keyEq action before middle tag
          (checkedActionProjects nameEq keyEq action before middle tag checked))))
      (\wanted, needed, provided => excluded wanted needed
        (replace {p = \component => Elem wanted (dependencies (componentProvisions component))}
          (sym (installedTracePreservesComponent nameEq keyEq actor (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
            (InstalledStep action tag checked rest installed tailInstalled) old lastFiber found lastFound)) provided))

||| Observe the actual installed source exactly once at the native boundary.
export
0 o20InstalledHeadResolver :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) -> (deps : List key) ->
  (before, middle, finalState : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} action before = Just (tag, middle)) ->
  (actionOwner action = actor) ->
  (rest : Transitions middle finalState) ->
  (installedAt {name} {key} {value} {world} {error} @{nameEq} actor before = True) ->
  InstalledTrace name key world error value nameEq keyEq actor rest ->
  (lastFiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry finalState) = Just lastFiber) ->
  ((wanted : key) -> Elem wanted deps -> Not (Elem wanted (dependencies (componentProvisions (fiberComponent lastFiber))))) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps (registry middle) =
   resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps (registry before))
o20InstalledHeadResolver {name} {key} {world} {error} {value} nameEq keyEq actor deps before middle finalState
  action tag checked owned rest installed tailInstalled lastFiber lastFound excluded =
    o20InstalledHeadResolverObserved nameEq keyEq actor deps before middle finalState action tag checked owned rest
      installed tailInstalled lastFiber lastFound excluded
      (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before)) Refl

||| Project both equations from ONE producer-owned resolver observation.
export
0 o20ResolverObservationFrame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (deps : List key) ->
  (before, afterState : Registry name key value world error) ->
  O19ResolutionObservation name key world error value nameEq keyEq deps before afterState ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps afterState =
   resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps before)
o20ResolverObservationFrame nameEq keyEq deps before afterState observed =
  trans (resolutionAfter observed) (sym (resolutionBefore observed))

||| A genuine checked child/root insertion is resolver-inert because the
||| native inserted fiber is inactive. No activation-domain premise is used.
export
0 o20NativeInsertionResolverFrame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (deps : List key) ->
  (child : name) -> (parent : Parent name) -> (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (OInsert child parent component) before = Just (tag, afterState)) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps (registry afterState) =
   resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps (registry before))
o20NativeInsertionResolverFrame nameEq keyEq deps child parent component before afterState tag checked =
  o20ResolverObservationFrame nameEq keyEq deps (registry before) (registry afterState)
    (o19ResolutionAfterCheckedInsert nameEq keyEq deps child parent component before afterState tag checked)
