module DGamma.CP4DeletionEndpoint

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionBoundaryPlan
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPlanEffects
import DGamma.CP4DeletionRelationalActionCore
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedOwn
import DGamma.CP4DeletionSkeleton
import Data.List.Elem
import Decidable.Equality

%default total

public export
CurrentRegisteredWithdrawable :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  SystemState name key value world error -> Type
CurrentRegisteredWithdrawable name key world error value nameEq registered live
  state =
    (actor : name) -> (generation : RegistrationGeneration name) ->
    Elem generation registered ->
    lookupCurrentGeneration @{nameEq} actor live = Just generation ->
    (fiber : Fiber name key value world error **
      (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} actor (registry state) = Just fiber,
       (retired fiber = True,
        (installed (fiberLifecycle fiber) = False,
         bindings (ownedValues (fiberTable fiber)) = []))))

0 lookupAbsentFromFresh :
  (nameEq : DecEq name) -> (wanted : name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  Not (Elem wanted (bindingKeys entries)) ->
  lookupEntries @{nameEq} wanted entries = Nothing
lookupAbsentFromFresh nameEq wanted [] absent = Refl
lookupAbsentFromFresh nameEq wanted (Bind current fiber :: rest) absent
  with (decEq @{nameEq} wanted current)
  lookupAbsentFromFresh nameEq current (Bind current fiber :: rest) absent |
    Yes Refl = void (absent Here)
  lookupAbsentFromFresh nameEq wanted (Bind current fiber :: rest) absent |
    No distinct = lookupAbsentFromFresh nameEq wanted rest
      (\later => absent (There later))

0 lookupDeleteSelfEndpoint :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (removed : name) ->
  (source : Registry name key value world error) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} removed
    (deleteBinding @{nameEq} removed source) = Nothing
lookupDeleteSelfEndpoint nameEq removed source = lookupDeleteSelf removed source

0 lookupDeletePreservesNothing :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor, removed : name) ->
  (source : Registry name key value world error) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} actor source = Nothing ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} actor (deleteBinding @{nameEq} removed source) = Nothing
lookupDeletePreservesNothing nameEq actor removed source absent
  with (decEq @{nameEq} actor removed)
  lookupDeletePreservesNothing nameEq removed removed source absent | Yes Refl =
    lookupDeleteSelfEndpoint nameEq removed source
  lookupDeletePreservesNothing nameEq actor removed source absent | No distinct =
    trans (lookupDeleteOther actor removed distinct source) absent

0 planPreservesLookupNothing :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} actor source = Nothing ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} actor target = Nothing
planPreservesLookupNothing nameEq actor source source NoInactiveLeafDeletion
  absent = absent
planPreservesLookupNothing nameEq actor source target
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest) absent =
      planPreservesLookupNothing nameEq actor
        (deleteBinding @{nameEq} removed source) target rest
        (lookupDeletePreservesNothing nameEq actor removed source absent)

0 deletedPlanActorLookupNothing :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target) ->
  ActorDeletedByInactivePlan actor plan ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} actor target = Nothing
deletedPlanActorLookupNothing nameEq actor source source NoInactiveLeafDeletion
  member impossible
deletedPlanActorLookupNothing nameEq removed source target
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest) Here =
      planPreservesLookupNothing nameEq removed
        (deleteBinding @{nameEq} removed source) target rest
        (lookupDeleteSelfEndpoint nameEq removed source)
deletedPlanActorLookupNothing nameEq actor source target
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest) (There later) =
      deletedPlanActorLookupNothing nameEq actor
        (deleteBinding @{nameEq} removed source) target rest later

0 effectSymmetricEndpoint : EffectStateRelated keyEq left right ->
  EffectStateRelated keyEq right left
effectSymmetricEndpoint (MkEffectStateRelated ambient tables) =
  MkEffectStateRelated (sym ambient) (\actor => sym (tables actor))

0 effectTransitiveEndpoint : EffectStateRelated keyEq left middle ->
  EffectStateRelated keyEq middle right -> EffectStateRelated keyEq left right
effectTransitiveEndpoint (MkEffectStateRelated firstAmbient firstTables)
  (MkEffectStateRelated secondAmbient secondTables) =
    MkEffectStateRelated (trans firstAmbient secondAmbient)
      (\actor => trans (firstTables actor) (secondTables actor))

||| Endpoint effects, controls, and generation-wise withdrawal from the final
||| relational suffix boundary.  The sole remaining trace-derived input is the
||| explicit retirement disposition of current registered generations.
public export
0 relationalBoundaryGivesEndpointEvidence :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : RelationalNoEpisodeReplayBoundary name key world error value
    nameEq keyEq registered live original survivor) ->
  EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult
      (relationalCompletePlan boundary))) ->
  CurrentRegisteredWithdrawable name key world error value nameEq registered
    live original ->
  (EffectStateRelated keyEq (projectEffectState @{nameEq} original)
      (projectEffectState @{nameEq} survivor),
   ControlEquivalentOutsideGenerations nameEq registered live original survivor,
   RegisteredNamesWithdrawn nameEq registered live original survivor)
relationalBoundaryGivesEndpointEvidence nameEq keyEq registered live unique
  original survivor boundary emptyPlan withdrawable =
    let originalToPlanConcrete = emptyInactivePlanPreservesEffects nameEq keyEq
          (worldState original) (registry original)
          (planTarget (completePlanResult (relationalCompletePlan boundary)))
          (inactiveLeafPlan
            (completePlanResult (relationalCompletePlan boundary))) emptyPlan
        originalToPlan = replace
          {p = \observed => EffectStateRelated keyEq
            (projectEffectState @{nameEq} observed)
            (projectEffectState @{nameEq}
              (MkSystemState (worldState original)
                (planTarget (completePlanResult
                  (relationalCompletePlan boundary)))))}
          (systemEtaEndpoint original) originalToPlanConcrete
        finalEffects = effectTransitiveEndpoint originalToPlan
          (relationalEffects boundary)
        finalControls = \actor, outside =>
          let strongOutside = currentGenerationOutsideImpliesActorOutsidePlan
                nameEq registered live unique actor outside
              planOutside = actorOutsidePlan
                (completePlanResult (relationalCompletePlan boundary)) actor
                strongOutside
              planLookup = lookupOutsideInactivePlan nameEq actor
                (registry original)
                (planTarget (completePlanResult
                  (relationalCompletePlan boundary)))
                (inactiveLeafPlan (completePlanResult
                  (relationalCompletePlan boundary))) planOutside
              planToSurvivor = orderedControlsLookup nameEq actor
                (planTarget (completePlanResult
                  (relationalCompletePlan boundary)))
                (registry survivor) (relationalOrderedControls boundary)
          in replace
            {p = \observed => FiberControlMaybeRelated observed
              (lookupFiber @{nameEq} actor (registry survivor))}
            planLookup planToSurvivor
        withdrawn = \generation, member =>
          case decEq (lookupCurrentGeneration @{nameEq}
            (generationName generation) live) (Just generation) of
            No historical => HistoricalGenerationClosed historical
            Yes current =>
              let currentEntry = currentGenerationEntryFromLookup nameEq
                    (generationName generation) generation live current
                  planMember = currentPlanComplete
                    (relationalCompletePlan boundary)
                    (generationName generation) generation currentEntry member
                  planAbsent = deletedPlanActorLookupNothing nameEq
                    (generationName generation) (registry original)
                    (planTarget (completePlanResult
                      (relationalCompletePlan boundary)))
                    (inactiveLeafPlan (completePlanResult
                      (relationalCompletePlan boundary))) planMember
                  survivorAbsent = orderedControlsNothingOnRight nameEq
                    (generationName generation)
                    (planTarget (completePlanResult
                      (relationalCompletePlan boundary)))
                    (registry survivor) (relationalOrderedControls boundary)
                    planAbsent
              in case withdrawable (generationName generation) generation member
                current of
                (fiber ** (found, (retiredTrue, (uninstalled, empty)))) =>
                  CurrentGenerationWithdrawn fiber current found retiredTrue
                    uninstalled empty survivorAbsent
    in (finalEffects, finalControls, withdrawn)
  where
  0 systemEtaEndpoint : (state : SystemState name key value world error) ->
    MkSystemState (worldState state) (registry state) = state
  systemEtaEndpoint (MkSystemState ambient fibers) = Refl
