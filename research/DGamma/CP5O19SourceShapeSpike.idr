module DGamma.CP5O19SourceShapeSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorOpen
import DGamma.CP4ProgressProgramBound
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O20BeginObservationSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Actual installation evolution plus paper activation rules forces owner
||| survival. The impossible preserved-uninstalled Advance contradicts its
||| real installed source, not a precomputed target-presence assumption.
export
0 o19ActivationEvolutionInstalled :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (first, afterState : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action first = Just (tag, afterState)) ->
  InstallationEvolution name key world error value nameEq keyEq (actionOwner action) first afterState action tag ->
  PaperActivationStep (Fired {before = first} {afterState} nameEq keyEq action tag checked) ->
  (installedAt {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) afterState = True)
o19ActivationEvolutionInstalled nameEq keyEq first afterState action tag checked
  (RemainedInstalled beforeInstalled afterInstalled) activation = afterInstalled
o19ActivationEvolutionInstalled nameEq keyEq first afterState action tag checked
  (RemainedUninstalled beforeUninstalled afterUninstalled) activation =
    case activation of
      PaperBeginStep {actor} sameAction sameTag => case sameAction of
        Refl => snd (snd (lBeginBoundary nameEq keyEq actor first afterState tag checked))
      PaperIterStep {actor} sameAction sameTag => case sameAction of
        Refl => void (uninhabited (trans (sym beforeUninstalled)
          (lAdvanceStartsInstalled nameEq keyEq actor first afterState tag
            (checkedActionProjects nameEq keyEq (LAdvance actor) first afterState tag checked))))
      PaperFinishStep {actor} sameAction sameTag => case sameAction of
        Refl => void (uninhabited (trans (sym beforeUninstalled)
          (lAdvanceStartsInstalled nameEq keyEq actor first afterState tag
            (checkedActionProjects nameEq keyEq (LAdvance actor) first afterState tag checked))))
o19ActivationEvolutionInstalled nameEq keyEq first afterState (LBegin actor) LBeginTag checked
  OpenedInstallation activation = snd (snd (lBeginBoundary nameEq keyEq actor first afterState LBeginTag checked))
o19ActivationEvolutionInstalled nameEq keyEq first afterState (LUnload actor) LUnloadTag checked
  ClosedInstallation activation = case activation of
    PaperBeginStep sameAction sameTag => case sameAction of Refl impossible
    PaperIterStep sameAction sameTag => case sameAction of Refl impossible
    PaperFinishStep sameAction sameTag => case sameAction of Refl impossible

||| Convert installation to presence through the actual owner lookup result.
export
0 o19InstalledOwnerObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) -> (state : SystemState name key value world error) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (lookupFiber @{nameEq} actor (registry state) = observed) ->
  (installedAt {name} {key} {value} {world} {error} @{nameEq} actor state = True) ->
  (isJust (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry state)) = True)
o19InstalledOwnerObserved nameEq actor state Nothing exact installed =
  case trans (sym (the (installedAt {name} {key} {value} {world} {error} @{nameEq} actor state = False)
    (rewrite exact in Refl))) installed of Refl impossible
o19InstalledOwnerObserved nameEq actor state (Just fiber) exact installed = cong isJust exact

||| Both owner observations are PRODUCED from the aligned actual activation:
||| source presence by rule inversion, target survival by installation evolution.
export
0 o19AlignedActivationOwner :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, afterState : SystemState name key value world error} ->
  (step : Transition first afterState) ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions step NoTransitions) ->
  PaperActivationStep step ->
  ((fiber : Fiber name key value world error ** lookupFiber @{nameEq} (actionOwner (transitionAction step)) (registry first) = Just fiber),
   (isJust (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner (transitionAction step)) (registry afterState)) = True))
o19AlignedActivationOwner {first} {afterState} nameEq keyEq _
  (AlignedStep action tag checked _ AlignedEnd) activation =
    (lifecycleActorPresent nameEq keyEq action first afterState tag
      (checkedActionProjects nameEq keyEq action first afterState tag checked)
      (case activation of
        PaperBeginStep sameAction sameTag => trans (cong isLifecycleAction sameAction) Refl
        PaperIterStep sameAction sameTag => trans (cong isLifecycleAction sameAction) Refl
        PaperFinishStep sameAction sameTag => trans (cong isLifecycleAction sameAction) Refl),
     o19InstalledOwnerObserved nameEq (actionOwner action) afterState
       (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) (registry afterState)) Refl
       (o19ActivationEvolutionInstalled nameEq keyEq first afterState action tag checked
         (installationEvolutionStep nameEq keyEq (actionOwner action) action tag first afterState checked) activation))

||| Owner-survival source-shape producer at the ACTUAL O19 pair cut. Bundle
||| alignment is extracted from its authenticated decomposition, never supplied
||| as an extra applicability or owner-observation premise.
export
0 o19SourcePairOwner :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {initial, first, middle, last, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) -> (earlier : Transitions initial first) ->
  (left : Transition first middle) -> (right : Transition middle last) -> (later : Transitions last finalState) ->
  (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)) = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source -> PaperActivationStep left ->
  ((fiber : Fiber name key value world error ** lookupFiber @{nameEq} (actionOwner (transitionAction left)) (registry first) = Just fiber),
   (isJust (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner (transitionAction left)) (registry middle)) = True))
o19SourcePairOwner nameEq keyEq protocol source earlier left right later decomposition premises activation =
  o19AlignedActivationOwner nameEq keyEq left
    (fst (alignedAppendSplit (MoreTransitions left NoTransitions) (MoreTransitions right NoTransitions)
      (fst (o19SourcePairFacts nameEq keyEq protocol source earlier left right later decomposition premises)))) activation

||| WF unique declared provisions and an ACTUAL resolved active provider rule
||| out a requested key in an inactive owner's static provision declaration.
export
0 o19InactiveResolvedKeyExcluded :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) -> (actor : name) ->
  (owner : Fiber name key value world error) -> (lookupFiber @{nameEq} actor (registry state) = Just owner) ->
  (isActive (fiberLifecycle owner) = False) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} state = True) ->
  (wanted : key) -> (provider : name) ->
  ProviderOfSound name key world error value nameEq keyEq wanted provider (registry state) ->
  Not (Elem wanted (dependencies (componentProvisions (fiberComponent owner))))
o19InactiveResolvedKeyExcluded nameEq keyEq state actor owner found inactive wellFormed wanted provider sound declares =
  uninhabited (trans (sym inactive)
    (trans (cong (\fiber => isActive (fiberLifecycle fiber))
      (justInjective (trans (sym found)
        (trans (cong (\selected => lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry state))
          (pairwiseSharedProvisionSameName keyEq (registryFibers (registry state))
            (registryWellFormedPairwiseOpenAnchor nameEq keyEq state wellFormed)
            actor provider owner (providerOfFiber sound)
            (lookupEntryElemOpenAnchor nameEq actor (registryFibers (registry state)) owner
              (lookupFiberEntries nameEq actor owner (registry state) found))
            (lookupEntryElemOpenAnchor nameEq provider (registryFibers (registry state)) (providerOfFiber sound)
              (lookupFiberEntries nameEq provider (providerOfFiber sound) (registry state) (providerOfLookup sound)))
            wanted declares
            (ownedSound (fiberTable (providerOfFiber sound)) wanted
              (memberKeyTrueElemOpenAnchor keyEq wanted (ownedValues (fiberTable (providerOfFiber sound)))
                (replace {p = \observed => isJust observed = True}
                  (the (valueFromProvider {name} {key} {value} {world} {error} @{nameEq} @{keyEq} provider wanted (registry state) =
                    lookupBinding @{keyEq} wanted (ownedValues (fiberTable (providerOfFiber sound))))
                    (rewrite providerOfLookup sound in Refl)) (providerOfValue sound))))))
          (providerOfLookup sound))))) (providerOfActive sound)))

||| Induction frame over explicit ACTUAL provider/tail resolver observations.
||| The continuation is precisely the smaller requested-list induction, not an
||| independent nondependency oracle in the public recursive producer below.
export
0 o19ResolutionConsExcluded :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) -> (actor : name) ->
  (owner : Fiber name key value world error) -> (lookupFiber @{nameEq} actor (registry state) = Just owner) ->
  (isActive (fiberLifecycle owner) = False) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} state = True) ->
  (head : key) -> (rest : List key) -> (view : View name (head :: rest)) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (head :: rest) (registry state) = Just view) ->
  (observedHead : Maybe name) ->
  (providerOf {name} {key} {value} {world} {error} @{nameEq} @{keyEq} head (registry state) = observedHead) ->
  (observedTail : Maybe (View name rest)) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} rest (registry state) = observedTail) ->
  ((tail : View name rest) ->
    (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} rest (registry state) = Just tail) ->
    (wanted : key) -> Elem wanted rest -> Not (Elem wanted (dependencies (componentProvisions (fiberComponent owner))))) ->
  (wanted : key) -> Elem wanted (head :: rest) -> Not (Elem wanted (dependencies (componentProvisions (fiberComponent owner))))
o19ResolutionConsExcluded nameEq keyEq state actor owner found inactive wellFormed head rest view resolved
  Nothing headExact tail tailExact smaller wanted member =
    case trans (sym (the
      (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (head :: rest) (registry state) = Nothing)
      (rewrite headExact in Refl))) resolved of Refl impossible
o19ResolutionConsExcluded nameEq keyEq state actor owner found inactive wellFormed head rest view resolved
  (Just provider) headExact Nothing tailExact smaller wanted member =
    case trans (sym (the
      (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (head :: rest) (registry state) = Nothing)
      (rewrite headExact in rewrite tailExact in Refl))) resolved of Refl impossible
o19ResolutionConsExcluded nameEq keyEq state actor owner found inactive wellFormed head rest view resolved
  (Just provider) headExact (Just tail) tailExact smaller _ Here =
    o19InactiveResolvedKeyExcluded nameEq keyEq state actor owner found inactive wellFormed head provider
      (providerOfSound nameEq keyEq head provider (registry state) headExact)
o19ResolutionConsExcluded nameEq keyEq state actor owner found inactive wellFormed head rest view resolved
  (Just provider) headExact (Just tail) tailExact smaller wanted (There later) = smaller tail tailExact wanted later

||| Every successfully resolved dependency excludes the static declarations of
||| an inactive owner. The actual provider and tail observations and the entire
||| exclusion induction are generated here; there is no footprint premise.
export
0 o19ResolvedDependenciesExcluded :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) -> (actor : name) ->
  (owner : Fiber name key value world error) -> (lookupFiber @{nameEq} actor (registry state) = Just owner) ->
  (isActive (fiberLifecycle owner) = False) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} state = True) ->
  (deps : List key) -> (view : View name deps) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps (registry state) = Just view) ->
  (wanted : key) -> Elem wanted deps -> Not (Elem wanted (dependencies (componentProvisions (fiberComponent owner))))
o19ResolvedDependenciesExcluded nameEq keyEq state actor owner found inactive wellFormed [] view resolved wanted absent =
  \declares => uninhabited absent
o19ResolvedDependenciesExcluded nameEq keyEq state actor owner found inactive wellFormed (head :: rest) view resolved wanted member =
  o19ResolutionConsExcluded nameEq keyEq state actor owner found inactive wellFormed head rest view resolved
    (providerOf {name} {key} {value} {world} {error} @{nameEq} @{keyEq} head (registry state)) Refl
    (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} rest (registry state)) Refl
    (\tail, tailExact => o19ResolvedDependenciesExcluded nameEq keyEq state actor owner found inactive wellFormed rest tail tailExact)
    wanted member

||| Actual left opening + safety's actual right-first Begin check PRODUCE both
||| component observations and static nondependency at the pre-left cut. No
||| resolver success, footprint or observer is requested as a new input.
||| Transporting these exact component declarations to arbitrary body cuts is
||| still a separate source-metadata synchronization obligation.
export
0 o19OpeningSourceNondependency :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (leftActor, rightActor : name) ->
  (before, leftAfter : SystemState name key value world error) ->
  (leftOpening : BeginStep nameEq keyEq leftActor before leftAfter) ->
  (rightOpening : CheckedEarlyApplication name key world error value nameEq keyEq before (LBegin rightActor) LBeginTag) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} before = True) ->
  (leftSeen : O20BeginObservation name key world error value nameEq keyEq leftActor before leftAfter **
   rightSeen : O20BeginObservation name key world error value nameEq keyEq rightActor before (earlyApplicationFinal rightOpening) **
   (wanted : key) -> Elem wanted (dependencies (componentDependencies (beginObservedComponent rightSeen))) ->
   Not (Elem wanted (dependencies (componentProvisions (beginObservedComponent leftSeen)))))
o19OpeningSourceNondependency nameEq keyEq leftActor rightActor before leftAfter leftOpening rightOpening wellFormed =
  (o20ObserveActualBegin nameEq keyEq leftActor before leftAfter leftOpening **
   o20ObserveActualBegin nameEq keyEq rightActor before (earlyApplicationFinal rightOpening)
     (MkBeginStep (earlyApplicationChecked rightOpening)) **
   o19ResolvedDependenciesExcluded nameEq keyEq before leftActor
     (MkFiber
       (beginObservedComponent (o20ObserveActualBegin nameEq keyEq leftActor before leftAfter leftOpening))
       (beginObservedParent (o20ObserveActualBegin nameEq keyEq leftActor before leftAfter leftOpening)) False
       (beginObservedTable (o20ObserveActualBegin nameEq keyEq leftActor before leftAfter leftOpening)) (Inactive Nothing))
     (beginObservedFound (o20ObserveActualBegin nameEq keyEq leftActor before leftAfter leftOpening)) Refl wellFormed
     (dependencies (componentDependencies (beginObservedComponent
       (o20ObserveActualBegin nameEq keyEq rightActor before (earlyApplicationFinal rightOpening)
         (MkBeginStep (earlyApplicationChecked rightOpening))))))
     (beginObservedView (o20ObserveActualBegin nameEq keyEq rightActor before (earlyApplicationFinal rightOpening)
       (MkBeginStep (earlyApplicationChecked rightOpening))))
     (beginObservedResolved (o20ObserveActualBegin nameEq keyEq rightActor before (earlyApplicationFinal rightOpening)
       (MkBeginStep (earlyApplicationChecked rightOpening)))))
