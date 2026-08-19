module DGamma.CP4DeletionSelectedDeletedPlan

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryPlan
import DGamma.CP4DeletionChildlessInvariant
import DGamma.CP4DeletionCommuteCore
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionEmptyTableInvariant
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPlanEffects
import DGamma.CP4DeletionPlanRuntime
import DGamma.CP4DeletionRetainedAction
import Data.List.Elem
import Decidable.Equality

%default total

0 nothingNotJustDeletedPlan : Nothing = Just item -> Void
nothingNotJustDeletedPlan Refl impossible

0 lookupNotElemNothingDeletedPlan : DecEq key => (wanted : key) ->
  (entries : List (Binding key value)) ->
  Not (Elem wanted (bindingKeys entries)) ->
  lookupEntries wanted entries = Nothing
lookupNotElemNothingDeletedPlan wanted [] absent = Refl
lookupNotElemNothingDeletedPlan wanted (Bind current next :: rest) absent
  with (decEq wanted current)
  lookupNotElemNothingDeletedPlan current (Bind current next :: rest) absent |
    Yes Refl = void (absent Here)
  lookupNotElemNothingDeletedPlan wanted (Bind current next :: rest) absent |
    No distinct = lookupNotElemNothingDeletedPlan wanted rest
      (\later => absent (There later))

0 lookupDeleteSelfDeletedPlan : DecEq key => (removed : key) ->
  (table : CoeffectContext key value) ->
  lookupBinding removed (deleteBinding removed table) = Nothing
lookupDeleteSelfDeletedPlan removed (MkCoeffectContext entries unique) =
  lookupNotElemNothingDeletedPlan removed (deleteEntries removed entries)
    (deletedKeyNotElem removed entries unique)

||| One exact leaf of an empty-table deletion plan, observed back at the plan
||| source.  Keeping the concrete fiber fields avoids proof irrelevance when the
||| caller supplies an independently obtained lookup witness.
public export
record EmptyInactiveFiberAt
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (actor : name)
  (source : Registry name key value world error) where
  constructor MkEmptyInactiveFiberAt
  emptyInactiveComponent : Component key value world error
  emptyInactiveParent : Parent name
  emptyInactiveRetired : Bool
  emptyInactiveTable : OwnedTable key value
    (componentProvisions emptyInactiveComponent)
  emptyInactiveOutcome : Maybe error
  0 emptyInactiveFound : lookupFiber @{nameEq} actor source =
    Just (MkFiber emptyInactiveComponent emptyInactiveParent emptyInactiveRetired
      emptyInactiveTable (Inactive emptyInactiveOutcome))
  0 emptyInactiveTableBindings : bindings (ownedValues emptyInactiveTable) = []

||| Locate a plan member and recover both its Inactive lifecycle and its empty
||| runtime table at the original plan source.
public export
0 emptyInactiveFiberFromPlanMember :
  (nameEq : DecEq name) -> (actor : name) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target) ->
  EmptyTableInactivePlan name key world error value nameEq plan ->
  Elem actor (inactivePlanActors plan) ->
  EmptyInactiveFiberAt name key world error value nameEq actor source
emptyInactiveFiberFromPlanMember nameEq actor source source
  NoInactiveLeafDeletion EmptyTablePlanEnd present = case present of
    Here impossible
    There later impossible
emptyInactiveFiberFromPlanMember nameEq actor source target
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest)
  (EmptyTablePlanStep tableEmpty emptyRest) present
  with (decEq @{nameEq} actor removed)
  emptyInactiveFiberFromPlanMember nameEq removed source target
    (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
      noChild rest)
    (EmptyTablePlanStep tableEmpty emptyRest) present | Yes Refl = case present of
      Here => MkEmptyInactiveFiberAt component parent retiredFlag table outcome
        found tableEmpty
      There later =>
        let tail = emptyInactiveFiberFromPlanMember nameEq removed
              (deleteBinding @{nameEq} removed source) target rest emptyRest later
        in void (nothingNotJustDeletedPlan
          (trans (sym (lookupDeleteSelfDeletedPlan removed source))
            (emptyInactiveFound tail)))
  emptyInactiveFiberFromPlanMember nameEq actor source target
    (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
      noChild rest)
    (EmptyTablePlanStep tableEmpty emptyRest) present | No distinct = case present of
      Here => void (distinct Refl)
      There later => case emptyInactiveFiberFromPlanMember nameEq actor
        (deleteBinding @{nameEq} removed source) target rest emptyRest later of
        MkEmptyInactiveFiberAt observedComponent observedParent observedRetired
          observedTable observedOutcome tailFound observedEmpty =>
            MkEmptyInactiveFiberAt observedComponent observedParent
              observedRetired observedTable observedOutcome
              (trans (sym (lookupDeleteOther actor removed distinct source))
                tailFound)
              observedEmpty

||| A complete empty plan already contains exactly the pointwise Inactive
||| invariant expected by the one-step no-episode table induction.
public export
0 completeEmptyPlanGivesCurrentRegisteredInactive :
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  (state : SystemState name key value world error) ->
  (plan : CompleteCurrentRegisteredPlanResult name key world error value nameEq
    registered live (registry state)) ->
  EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult plan)) ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered
    live state
completeEmptyPlanGivesCurrentRegisteredInactive nameEq registered live state plan
  empty selected generation member current =
    let 0 currentEntry = currentGenerationEntryFromLookup nameEq selected
          generation live current
        0 planMember = currentPlanComplete plan selected generation currentEntry
          member
    in case emptyInactiveFiberFromPlanMember nameEq selected (registry state)
      (planTarget (completePlanResult plan))
      (inactiveLeafPlan (completePlanResult plan)) empty planMember of
      MkEmptyInactiveFiberAt component parent retiredFlag table outcome found
        tableEmpty => MkInactiveFiberAt component parent retiredFlag table outcome
          found

||| The same complete empty plan exposes the table half of the invariant without
||| equating independently constructed dependent fibers.
public export
0 completeEmptyPlanGivesCurrentRegisteredEmptyTables :
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  (state : SystemState name key value world error) ->
  (plan : CompleteCurrentRegisteredPlanResult name key world error value nameEq
    registered live (registry state)) ->
  EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult plan)) ->
  CurrentRegisteredEmptyTables name key world error value nameEq registered live
    state
completeEmptyPlanGivesCurrentRegisteredEmptyTables nameEq registered live state
  plan empty selected generation member current fiber fiberFound =
    let 0 currentEntry = currentGenerationEntryFromLookup nameEq selected
          generation live current
        0 planMember = currentPlanComplete plan selected generation currentEntry
          member
    in case emptyInactiveFiberFromPlanMember nameEq selected (registry state)
      (planTarget (completePlanResult plan))
      (inactiveLeafPlan (completePlanResult plan)) empty planMember of
      MkEmptyInactiveFiberAt component parent retiredFlag table outcome found
        tableEmpty =>
          let 0 sameFiber : (fiber =
                MkFiber component parent retiredFlag table (Inactive outcome))
              sameFiber = justInjective (trans (sym fiberFound) found)
          in case sameFiber of Refl => tableEmpty

0 entryAfterDistinctPutComesFromOld :
  (nameEq : DecEq name) -> (inserted, selected : name) ->
  Not (selected = inserted) ->
  (fresh, generation : RegistrationGeneration name) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  Elem (selected, generation)
    (putCurrentGeneration @{nameEq} inserted fresh live) ->
  Elem (selected, generation) live
entryAfterDistinctPutComesFromOld nameEq inserted selected distinct fresh
  generation live unique present =
    let 0 nextUnique = putCurrentGenerationPreservesUnique nameEq inserted fresh
          live unique
        0 nextCurrent = lookupCurrentGenerationFromElem nameEq
          (putCurrentGeneration @{nameEq} inserted fresh live) nextUnique present
        0 oldCurrent : (lookupCurrentGeneration @{nameEq} selected live =
              Just generation)
        oldCurrent = trans
          (sym (lookupPutCurrentOther nameEq selected inserted distinct fresh live))
          nextCurrent
    in currentGenerationEntryFromLookup nameEq selected generation live oldCurrent

||| Complete-plan update for an O-Insert that is itself deleted as an R birth.
||| The new fresh empty/Inactive leaf is prepended to the plan, so deleting it
||| and the old leaves reaches the old plan target at the same ordered runtime
||| bindings.
public export
0 completePlanAfterDeletedInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (inserted : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (source : Registry name key value world error) ->
  (oldPlan : CompleteCurrentRegisteredPlanResult name key world error value
    nameEq registered live source) ->
  (absent : lookupFiber @{nameEq} inserted source = Nothing) ->
  Elem (MkRegistrationGeneration inserted ordinal) registered ->
  (noChild : hasChild @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} inserted
    (insertBinding @{nameEq} inserted (freshFiber component parent) source absent) =
      False) ->
  (nextPlan : CompleteCurrentRegisteredPlanResult name key world error value
      nameEq registered
      (putCurrentGeneration @{nameEq} inserted
        (MkRegistrationGeneration inserted ordinal) live)
      (insertBinding @{nameEq} inserted (freshFiber component parent) source absent) **
    bindings (planTarget (completePlanResult nextPlan)) =
      bindings (planTarget (completePlanResult oldPlan)))
completePlanAfterDeletedInsert {name} {key} {world} {error} {value}
  nameEq registered ordinal live unique inserted parent component source
  oldComplete@(MkCompleteCurrentRegisteredPlanResult
    oldResult@(MkCurrentRegisteredPlanResult oldTarget oldInactive oldOutside)
    oldPlanComplete)
  absent freshMember noChild =
    let fresh : RegistrationGeneration name
        fresh = MkRegistrationGeneration inserted ordinal
        newSource : Registry name key value world error
        newSource = insertBinding @{nameEq} inserted
          (freshFiber component parent) source absent
        tailSource : Registry name key value world error
        tailSource = deleteBinding @{nameEq} inserted newSource
        0 tailsSame : (bindings source = bindings tailSource)
        tailsSame = sym (deleteBindingAfterFreshInsertBindings nameEq inserted
          (freshFiber component parent) source absent)
        0 transported : InactivePlanBindingsTransport name key world error value
          nameEq oldInactive tailSource
        transported = transportInactivePlanAcrossBindings nameEq source oldTarget
          tailSource oldInactive tailsSame
        0 newTarget : Registry name key value world error
        newTarget = transportedPlanTarget transported
        0 tailPlan : InactiveLeafDeletionPlan {name = name} {key = key}
          {value = value} {world = world} {error = error} nameEq tailSource
          newTarget
        tailPlan = transportedInactivePlan transported
        0 newPlan : InactiveLeafDeletionPlan {name = name} {key = key}
          {value = value} {world = world} {error = error} nameEq newSource newTarget
        newPlan = DeleteInactiveLeaf inserted component parent False emptyOwned
          Nothing (lookupInserted inserted (freshFiber component parent) source
            absent) noChild tailPlan
        0 newLive : GenerationEnvironment name
        newLive = putCurrentGeneration @{nameEq} inserted fresh live
        0 freshPresent : Elem (inserted, fresh) newLive
        freshPresent = currentGenerationEntryFromLookup nameEq inserted fresh
          newLive (lookupPutCurrentSelf nameEq inserted fresh live)
        0 insertedOldOutsidePlan : ActorOutsideDeletionPlan inserted oldInactive
        insertedOldOutsidePlan = absentActorOutsideDeletionPlan nameEq inserted
          source oldTarget oldInactive absent
        0 insertedOldOutsideCurrent : ActorOutsideCurrentRegistered inserted
          registered live
        insertedOldOutsideCurrent = actorOutsideCurrentFromCompletePlan oldResult
          oldPlanComplete inserted insertedOldOutsidePlan
        0 outsideNew : (actor : name) ->
          ActorOutsideCurrentRegistered actor registered newLive ->
          ActorOutsideDeletionPlan actor newPlan
        outsideNew actor outside =
          let 0 actorDistinct : Not (actor = inserted)
              actorDistinct = outside inserted fresh freshPresent freshMember
              0 oldOutsideCurrent : ActorOutsideCurrentRegistered actor registered
                    live
              oldOutsideCurrent selected generation present member =
                outside selected generation
                  (putPreservesOtherEntry nameEq inserted selected
                    (insertedOldOutsideCurrent selected generation present member)
                    fresh generation live present)
                  member
          in ActorOutsideDeletionStep tailPlan actorDistinct
            (transportedActorOutside transported actor
              (oldOutside actor oldOutsideCurrent))
        0 newResult : CurrentRegisteredPlanResult name key world error value
          nameEq registered newLive newSource
        newResult = MkCurrentRegisteredPlanResult newTarget newPlan outsideNew
        0 newUnique : GenerationEnvironmentNamesUnique newLive
        newUnique = putCurrentGenerationPreservesUnique nameEq inserted fresh live
          unique
        0 newComplete : CurrentRegisteredPlanComplete name key world error value
          nameEq registered newLive newResult
        newComplete selected generation present member
          with (decEq @{nameEq} selected inserted)
          newComplete _ generation present member | Yes Refl = Here
          newComplete selected generation present member | No distinct =
            let 0 oldPresent = entryAfterDistinctPutComesFromOld nameEq inserted
                  selected distinct fresh generation live unique present
                0 oldMember = oldPlanComplete selected generation oldPresent member
                0 transportedMember : Elem selected
                      (inactivePlanActors tailPlan)
                transportedMember = replace {p = Elem selected}
                  (sym (transportedPlanActors transported)) oldMember
            in There transportedMember
        0 nextComplete : CompleteCurrentRegisteredPlanResult name key world error
          value nameEq registered newLive newSource
        nextComplete = MkCompleteCurrentRegisteredPlanResult newResult newComplete
        0 targetBindings : (bindings newTarget = bindings oldTarget)
        targetBindings = sym (transportedPlanBindings transported)
    in (nextComplete ** targetBindings)
