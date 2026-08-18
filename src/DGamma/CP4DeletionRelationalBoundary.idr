module DGamma.CP4DeletionRelationalBoundary

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionNoEpisodeReplay
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4RuntimeBindings
import Decidable.Equality

%default total

||| Ordered control skeleton used by relational replay.  Binding names/order,
||| components, parents, retirement bits, lifecycle constructors, continuations,
||| views, and accumulators (extensionally) are retained; owned tables remain on
||| the separate exact ordered-effect relation.
public export
data OrderedRegistryControlsRelated :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  List (Binding name (FiberAt name key value world error)) ->
  List (Binding name (FiberAt name key value world error)) -> Type where
  OrderedControlsNil : OrderedRegistryControlsRelated name key world error value
    [] []
  OrderedControlsCons :
    (actor : name) ->
    FiberControlRelated leftFiber rightFiber ->
    OrderedRegistryControlsRelated name key world error value leftRest
      rightRest ->
    OrderedRegistryControlsRelated name key world error value
      (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest)

public export
0 orderedControlsReflexive :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  OrderedRegistryControlsRelated name key world error value entries entries
orderedControlsReflexive [] = OrderedControlsNil
orderedControlsReflexive (Bind actor fiber :: rest) =
  OrderedControlsCons actor (fiberControlReflexive fiber)
    (orderedControlsReflexive rest)

0 orderedLookupControlsRelated :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {left, right : List (Binding name (FiberAt name key value world error))} ->
  (nameEq : DecEq name) -> (actor : name) ->
  OrderedRegistryControlsRelated name key world error value left right ->
  FiberControlMaybeRelated
    (lookupEntries @{nameEq} {key = name}
      {value = FiberAt name key value world error} actor left)
    (lookupEntries @{nameEq} {key = name}
      {value = FiberAt name key value world error} actor right)
orderedLookupControlsRelated nameEq actor OrderedControlsNil = NoControlFibers
orderedLookupControlsRelated nameEq actor
  (OrderedControlsCons current fibers tail) with (decEq @{nameEq} actor current)
  orderedLookupControlsRelated nameEq current
    (OrderedControlsCons current fibers tail) | Yes Refl =
      SomeControlFibers fibers
  orderedLookupControlsRelated nameEq actor
    (OrderedControlsCons current fibers tail) | No distinct =
      orderedLookupControlsRelated nameEq actor tail

public export
0 orderedControlsGiveControlEquivalent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  (left, right : SystemState name key value world error) ->
  OrderedRegistryControlsRelated name key world error value
    (bindings (registry left)) (bindings (registry right)) ->
  ControlEquivalent name key world error value nameEq left right
orderedControlsGiveControlEquivalent nameEq
  (MkSystemState leftWorld (MkCoeffectContext leftEntries leftUnique))
  (MkSystemState rightWorld (MkCoeffectContext rightEntries rightUnique))
  ordered = MkControlEquivalent (\actor =>
    orderedLookupControlsRelated nameEq actor ordered)

||| Apply the current-R deletion plan to registry control while retaining the
||| original ambient state.  This is the conceptual source of the relational
||| suffix replay; no equality of the registry's erased uniqueness proof is
||| requested.
public export
plannedSystemState :
  (original : SystemState name key value world error) ->
  (plan : CurrentRegisteredPlanResult name key world error value nameEq
    registered live (registry original)) ->
  SystemState name key value world error
plannedSystemState original plan = MkSystemState (worldState original)
  (planTarget plan)

||| Primary general boundary after selected recovery.  The survivor is related
||| to the original state *after* deleting its exact current R leaves.  Complete
||| effects retain ambient state and every ordered actor table; complete control
||| relation additionally proves those R leaves are absent from the survivor.
public export
record RelationalNoEpisodeReplayBoundary
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (registered : List (RegistrationGeneration name))
  (live : GenerationEnvironment name)
  (original, survivor : SystemState name key value world error) where
  constructor MkRelationalNoEpisodeReplayBoundary
  relationalCompletePlan : CompleteCurrentRegisteredPlanResult name key world
    error value nameEq registered live (registry original)
  0 relationalEffects : EffectStateRelated keyEq
    (projectEffectState @{nameEq}
      (plannedSystemState original
        (completePlanResult relationalCompletePlan)))
    (projectEffectState @{nameEq} survivor)
  0 relationalOrderedControls : OrderedRegistryControlsRelated name key world
    error value
    (bindings (registry (plannedSystemState original
      (completePlanResult relationalCompletePlan))))
    (bindings (registry survivor))
  0 relationalOriginalWellFormed : registryWellFormed @{nameEq} @{keyEq}
    original = True
  0 relationalSurvivorWellFormed : registryWellFormed @{nameEq} @{keyEq}
    survivor = True

public export
0 relationalControlEquivalent :
  (boundary : RelationalNoEpisodeReplayBoundary name key world error value
    nameEq keyEq registered live original survivor) ->
  ControlEquivalent name key world error value nameEq
    (plannedSystemState original
      (completePlanResult (relationalCompletePlan boundary))) survivor
relationalControlEquivalent boundary = orderedControlsGiveControlEquivalent
  nameEq
  (plannedSystemState original
    (completePlanResult (relationalCompletePlan boundary))) survivor
  (relationalOrderedControls boundary)

0 projectEffectTableReproof :
  (nameEq : DecEq name) -> (actor : name) -> (ambient : world) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (leftUnique, rightUnique : UniqueKeys (bindingKeys entries)) ->
  bindings (effectTables (projectEffectState @{nameEq}
    (the (SystemState name key value world error)
      (MkSystemState ambient (MkCoeffectContext entries leftUnique)))) actor) =
  bindings (effectTables (projectEffectState @{nameEq}
    (the (SystemState name key value world error)
      (MkSystemState ambient (MkCoeffectContext entries rightUnique)))) actor)
projectEffectTableReproof nameEq actor ambient entries leftUnique rightUnique
  with (lookupEntries @{nameEq} actor entries)
  projectEffectTableReproof nameEq actor ambient entries leftUnique rightUnique |
    Nothing = Refl
  projectEffectTableReproof nameEq actor ambient entries leftUnique rightUnique |
    Just fiber = Refl

0 orderedControlsFromRuntimeSnapshot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (left, right : SystemState name key value world error) ->
  runtimeSnapshot left = runtimeSnapshot right ->
  OrderedRegistryControlsRelated name key world error value
    (bindings (registry left)) (bindings (registry right))
orderedControlsFromRuntimeSnapshot
  (MkSystemState leftWorld (MkCoeffectContext leftEntries leftUnique))
  (MkSystemState rightWorld (MkCoeffectContext rightEntries rightUnique)) same =
    case cong snapshotBindings same of
      Refl => orderedControlsReflexive rightEntries

0 fiberControlMaybeReproof :
  {name, key, world, error : Type} ->
  (value : key -> Type) ->
  (nameEq : DecEq name) -> (actor : name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (leftUnique, rightUnique : UniqueKeys (bindingKeys entries)) ->
  FiberControlMaybeRelated
    (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} actor
      (MkCoeffectContext entries leftUnique))
    (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} actor
      (MkCoeffectContext entries rightUnique))
fiberControlMaybeReproof value nameEq actor entries leftUnique rightUnique
  with (lookupEntries @{nameEq} actor entries)
  fiberControlMaybeReproof value nameEq actor entries leftUnique rightUnique |
    Nothing = NoControlFibers
  fiberControlMaybeReproof value nameEq actor entries leftUnique rightUnique |
    Just fiber = SomeControlFibers (fiberControlReflexive fiber)

||| Exact host-observable runtime equality implies the project's extensional
||| effect/control equivalence even when the two registries carry distinct
||| erased `UniqueKeys` certificates.
public export
0 runtimeSnapshotGivesSystemEquivalent :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (left, right : SystemState name key value world error) ->
  runtimeSnapshot left = runtimeSnapshot right ->
  SystemEquivalent name key world error value nameEq keyEq left right
runtimeSnapshotGivesSystemEquivalent nameEq keyEq
  left@(MkSystemState leftWorld (MkCoeffectContext leftEntries leftUnique))
  right@(MkSystemState rightWorld (MkCoeffectContext rightEntries rightUnique))
  snapshotsSame =
    let 0 worldSame = cong snapshotWorld snapshotsSame
        0 entriesSame = cong snapshotBindings snapshotsSame
    in case worldSame of
      Refl => case entriesSame of
        Refl => MkSystemEquivalent
          (MkEffectStateRelated Refl (\actor =>
            projectEffectTableReproof nameEq actor leftWorld rightEntries
              leftUnique rightUnique))
          (MkControlEquivalent (\actor => fiberControlMaybeReproof value nameEq
            actor rightEntries leftUnique rightUnique))

||| The former exact suffix scaffold is the reflexive/runtime-equality
||| specialization of the relational boundary.  It remains available to the
||| existing exact fold while later selected recovery enters through the same
||| primary relation without function extensionality.
public export
0 exactBoundaryGivesRelational :
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  RelationalNoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor
exactBoundaryGivesRelational
  boundary@(MkNoEpisodeReplayBoundary ambient source originalShape completePlan
    survivorAmbient survivorBindings unique originalWellFormed
    survivorWellFormed) =
      case originalShape of
        Refl =>
          let planned : SystemState name key value world error
              planned = plannedSystemState (MkSystemState ambient source)
                (completePlanResult completePlan)
              0 snapshotsSame : runtimeSnapshot
                    (plannedSystemState (MkSystemState ambient source)
                      (completePlanResult completePlan)) =
                  runtimeSnapshot survivor
              snapshotsSame = boundaryPlanSnapshotMatchesSurvivor
                (MkNoEpisodeReplayBoundary ambient source Refl completePlan
                  survivorAmbient survivorBindings unique originalWellFormed
                  survivorWellFormed)
              0 equivalent : SystemEquivalent name key world error value nameEq
                keyEq
                (plannedSystemState (MkSystemState ambient source)
                  (completePlanResult completePlan)) survivor
              equivalent = runtimeSnapshotGivesSystemEquivalent nameEq keyEq
                (plannedSystemState (MkSystemState ambient source)
                  (completePlanResult completePlan)) survivor snapshotsSame
              0 ordered : OrderedRegistryControlsRelated name key world error
                value
                (bindings (registry
                  (plannedSystemState (MkSystemState ambient source)
                    (completePlanResult completePlan))))
                (bindings (registry survivor))
              ordered = orderedControlsFromRuntimeSnapshot
                (plannedSystemState (MkSystemState ambient source)
                  (completePlanResult completePlan)) survivor snapshotsSame
          in MkRelationalNoEpisodeReplayBoundary completePlan
            (effectsEquivalent equivalent) ordered originalWellFormed
            survivorWellFormed
