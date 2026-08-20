module DGamma.CP4DeletionSelectedCloseBoundary

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionEmptyTableInvariant
import DGamma.CP4DeletionGenerationStamped
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPlanEffects
import DGamma.CP4DeletionPlanEmpty
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedCloseEffect
import DGamma.CP4DeletionSelectedOwn
import DGamma.CP4DeletionSelectedForeignLifecycleUnload
import DGamma.CP4RuntimeBindings
import Data.List.Elem
import Decidable.Equality

%default total

%inline
closeSourceFiber :
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (outcome : Maybe error) -> Fiber name key value world error
closeSourceFiber component parent retiredFlag table accumulator view outcome =
  MkFiber component parent retiredFlag table
    (Unloading accumulator view outcome)

%inline
closeTargetFiber :
  (keyEq : DecEq key) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (outcome : Maybe error) -> (ambient : world) ->
  Fiber name key value world error
closeTargetFiber keyEq component parent retiredFlag table accumulator outcome
  ambient = MkFiber component parent retiredFlag
    (localTable (accumulator
      (MkLocalState ambient
        (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component)
          (ownedValues table)))))
    (Inactive outcome)


record ClosingUnloadSource
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (state : SystemState name key value world error) where
  constructor MkClosingUnloadSource
  closingComponent : Component key value world error
  closingParent : Parent name
  closingRetired : Bool
  closingTable : OwnedTable key value
    (componentProvisions closingComponent)
  closingAccumulator : LocalState key value world
    (componentProvisions closingComponent) ->
    LocalState key value world (componentProvisions closingComponent)
  closingView : View name
    (dependencies (componentDependencies closingComponent))
  closingOutcome : Maybe error
  0 closingFound : lookupFiber @{nameEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} selected
    (registry state) = Just
    (MkFiber closingComponent closingParent closingRetired closingTable
      (Unloading closingAccumulator closingView closingOutcome))
  0 closingUnrelied : relied @{nameEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} selected
    (registry state) = False

closingUnloadSource :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (state, afterState : SystemState name key value world error) ->
  (0 raw : applyAction @{nameEq} @{keyEq} (LUnload selected) state =
    Just (LUnloadTag, afterState)) ->
  ClosingUnloadSource name key world error value nameEq keyEq selected state
closingUnloadSource nameEq keyEq selected state@(MkSystemState ambient source)
  afterState raw with (lookupFiber @{nameEq} selected source) proof found
  closingUnloadSource nameEq keyEq selected
    state@(MkSystemState ambient source) afterState raw | Nothing =
      void (nothingIsNotJust raw)
  closingUnloadSource nameEq keyEq selected
    state@(MkSystemState ambient source) afterState raw |
    Just (MkFiber component parent retiredFlag table (Inactive outcome)) =
      void (nothingIsNotJust raw)
  closingUnloadSource nameEq keyEq selected
    state@(MkSystemState ambient source) afterState raw |
    Just (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator view)) = void (nothingIsNotJust raw)
  closingUnloadSource nameEq keyEq selected
    state@(MkSystemState ambient source) afterState raw |
    Just (MkFiber component parent retiredFlag table (Active accumulator view)) =
      void (nothingIsNotJust raw)
  closingUnloadSource nameEq keyEq selected
    state@(MkSystemState ambient source) afterState raw |
    Just (MkFiber component parent retiredFlag table
      (Unloading accumulator view outcome))
    with (relied @{nameEq} selected source) proof unrelied
    closingUnloadSource nameEq keyEq selected
      state@(MkSystemState ambient source) afterState raw |
      Just (MkFiber component parent retiredFlag table
        (Unloading accumulator view outcome)) | True =
          void (nothingIsNotJust raw)
    closingUnloadSource nameEq keyEq selected
      state@(MkSystemState ambient source) afterState raw |
      Just (MkFiber component parent retiredFlag table
        (Unloading accumulator view outcome)) | False =
          MkClosingUnloadSource component parent retiredFlag table accumulator
            view outcome found unrelied

public export
record PostCloseSelectedBoundary
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (registered : List (RegistrationGeneration name))
  (ordinal : Nat) (live : GenerationEnvironment name)
  (original, survivor : SystemState name key value world error) where
  constructor MkPostCloseSelectedBoundary
  postClosePlan : CompleteCurrentRegisteredPlanResult name key world error value
    nameEq registered live (registry original)
  0 postCloseEffects : EffectStateRelated keyEq
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState (worldState original)
          (planTarget (completePlanResult postClosePlan)))))
    (projectEffectState @{nameEq} survivor)
  0 postCloseControls : SelectedOrderedRegistryControlsRelated name key world
    error value selected
    (bindings (planTarget (completePlanResult postClosePlan)))
    (bindings (registry survivor))
  0 postCloseCleanInactive : SelectedSurvivorCleanInactive name key world error
    value nameEq selected survivor
  0 postCloseOriginalWellFormed : registryWellFormed @{nameEq} @{keyEq}
    original = True
  0 postCloseSurvivorWellFormed : registryWellFormed @{nameEq} @{keyEq}
    survivor = True
  0 postCloseCurrentInactive : CurrentRegisteredInactiveFibers name key world
    error value nameEq registered live original
  0 postCloseCurrentEmpty : CurrentRegisteredEmptyTables name key world error
    value nameEq registered live original
  0 postClosePlanEmpty : EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult postClosePlan))

0 unloadIsNotBegin :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {selected : name} ->
  {registered : List (RegistrationGeneration name)} ->
  {ordinal : Nat} -> {live : GenerationEnvironment name} ->
  IsBeginAction (the (Action name key value world error) (LUnload selected)) ->
  GenerationOwnedActor nameEq registered ordinal live
    (the (Action name key value world error) (LUnload selected)) -> Void
unloadIsNotBegin ItIsLBegin deleted impossible

0 stateEtaClose : (state : SystemState name key value world error) ->
  MkSystemState (worldState state) (registry state) = state
stateEtaClose (MkSystemState ambient fibers) = Refl

0 unloadRawAtEta :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (state, afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (LUnload selected) state =
    Just (LUnloadTag, afterState) ->
  applyAction @{nameEq} @{keyEq} (LUnload selected)
    (MkSystemState (worldState state) (registry state)) =
    Just (LUnloadTag, afterState)
unloadRawAtEta nameEq keyEq selected state afterState raw =
  trans (cong (applyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (LUnload selected)))
    (stateEtaClose state)) raw

0 effectSymmetricClose : EffectStateRelated keyEq left right ->
  EffectStateRelated keyEq right left
effectSymmetricClose (MkEffectStateRelated ambient tables) =
  MkEffectStateRelated (sym ambient) (\actor => sym (tables actor))

0 effectTransitiveClose : EffectStateRelated keyEq left middle ->
  EffectStateRelated keyEq middle right -> EffectStateRelated keyEq left right
effectTransitiveClose (MkEffectStateRelated firstAmbient firstTables)
  (MkEffectStateRelated secondAmbient secondTables) =
    MkEffectStateRelated (trans firstAmbient secondAmbient)
      (\actor => trans (firstTables actor) (secondTables actor))

||| Delete the selected closing L-Unload.  The accumulator effect closes
||| against the unchanged survivor, while the selected cell is replaced only on
||| the plan side and remains statically related to the survivor's clean
||| Inactive cell.  This relation intentionally survives failed closes; the
||| post-close fold later discharges it at selected O-Remove/reinsert.
public export
0 selectedUnloadClosesPostBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  GenerationEnvironmentStamped live ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (closing : UnloadStep nameEq keyEq selected before afterState) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult
      (selectedBoundaryPlan boundary))) ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered
    live before ->
  CurrentRegisteredEmptyTables name key world error value nameEq registered live
    before ->
  PostCloseSelectedBoundary name key world error value nameEq keyEq selected
    registered (S ordinal) live afterState survivor
selectedUnloadClosesPostBoundary
  {name} {key} {world} {error} {value}
  nameEq keyEq selected registered ordinal live unique stamped selectedOutside
  whole before afterState survivor closing boundary oldEmpty sourceInactive
  sourceEmpty =
    let raw = checkedActionProjects nameEq keyEq (LUnload selected) before
            afterState LUnloadTag (unloadEquation closing)
        0 rawEta : (applyAction @{nameEq} @{keyEq} (LUnload selected)
          (the (SystemState name key value world error)
            (MkSystemState (worldState before) (registry before))) =
          Just (LUnloadTag, afterState))
        rawEta = unloadRawAtEta nameEq keyEq selected before afterState raw
        sourceView = closingUnloadSource nameEq keyEq selected before afterState
          raw
    in case sourceView of
      MkClosingUnloadSource component parent retiredFlag table accumulator view
        outcome exactSourceFound unrelied =>
          let input = MkLocalState (worldState before)
                      (restrictOwnedPreservingOrder @{keyEq}
                        (componentProvisions component) (ownedValues table))
              restored = accumulator input
              concreteAfter : SystemState name key value world error
              concreteAfter = MkSystemState
                (localWorld (accumulator
                  (MkLocalState (worldState before)
                    (restrictOwnedPreservingOrder @{keyEq}
                      (componentProvisions component)
                      (ownedValues table)))))
                (replaceBinding @{nameEq} selected
                  (MkFiber component parent retiredFlag
                    (localTable (accumulator
                      (MkLocalState (worldState before)
                        (restrictOwnedPreservingOrder @{keyEq}
                          (componentProvisions component)
                          (ownedValues table)))))
                    (Inactive outcome)) (registry before))
              concreteRaw : applyAction @{nameEq} @{keyEq}
                (LUnload selected)
                (MkSystemState (worldState before) (registry before)) =
                Just (LUnloadTag, concreteAfter)
              concreteRaw = rewrite exactSourceFound in rewrite unrelied in Refl
              rawAtConcrete : applyAction @{nameEq} @{keyEq}
                (LUnload selected)
                (MkSystemState (worldState before) (registry before)) =
                Just (LUnloadTag, afterState)
              rawAtConcrete = rawEta
              pairSame : ((LUnloadTag, concreteAfter) =
                (LUnloadTag, afterState))
              pairSame = justInjective
                (trans (sym concreteRaw) rawAtConcrete)
              afterShape : concreteAfter = afterState
              afterShape = cong snd pairSame
              targetFoundConcrete : lookupFiber @{nameEq} selected
                (registry concreteAfter) = Just (closeTargetFiber keyEq component parent retiredFlag table accumulator outcome
                      (worldState before))
              targetFoundConcrete = lookupReplacedFiber selected (closeSourceFiber component parent retiredFlag table accumulator view outcome)
                (closeTargetFiber keyEq component parent retiredFlag table accumulator outcome
                      (worldState before)) (registry before) exactSourceFound
              targetFound : lookupFiber @{nameEq} selected
                (registry afterState) = Just (closeTargetFiber keyEq component parent retiredFlag table accumulator outcome
                      (worldState before))
              targetFound = replace
                {p = \observed => lookupFiber @{nameEq} selected
                  (registry observed) = Just (closeTargetFiber keyEq component parent retiredFlag table accumulator outcome
                      (worldState before))}
                afterShape targetFoundConcrete
              0 outside : ActorOutsideDeletionPlan selected
                (inactiveLeafPlan (completePlanResult
                  (selectedBoundaryPlan boundary)))
              outside = selectedOutsideBoundaryPlan selected registered live
                stamped selectedOutside (selectedBoundaryPlan boundary)
              0 update : RegistryLocalUpdate name key world error value
                nameEq selected (registry before) (registry afterState)
              update = systemRegistryUpdate
                (applyActionLocalUpdate nameEq keyEq (LUnload selected)
                  before afterState LUnloadTag raw)
          in case registryReplacementPreservesPlanAndControls nameEq
            selected registered live (registry before) (registry afterState)
            (selectedBoundaryPlan boundary) outside (closeSourceFiber component parent retiredFlag table accumulator view outcome) exactSourceFound
            (closeTargetFiber keyEq component parent retiredFlag table accumulator outcome
                      (worldState before)) targetFound Refl update of
            MkSelectedReplacementPlanStep nextPlan targetBindings static =>
              let 0 planSourceFound : (lookupFiber @{nameEq} selected
                    (planTarget (completePlanResult (selectedBoundaryPlan boundary))) = Just (closeSourceFiber component parent retiredFlag table accumulator view outcome))
                  planSourceFound = trans
                    (lookupOutsideInactivePlan nameEq selected (registry before)
                      (planTarget (completePlanResult (selectedBoundaryPlan boundary))) (inactiveLeafPlan (completePlanResult (selectedBoundaryPlan boundary))) outside)
                    exactSourceFound
                  0 entriesFound : (lookupEntries @{nameEq} selected
                    (bindings (planTarget (completePlanResult (selectedBoundaryPlan boundary)))) = Just (closeSourceFiber component parent retiredFlag table accumulator view outcome))
                  entriesFound = trans
                    (sym (lookupFiberAsEntries nameEq selected
                      (planTarget (completePlanResult (selectedBoundaryPlan boundary))))) planSourceFound
                  0 replaced : SelectedOrderedRegistryControlsRelated name
                    key world error value selected
                    (replaceEntries @{nameEq} selected
                      (closeTargetFiber keyEq component parent retiredFlag
                        table accumulator outcome (worldState before))
                      (bindings (planTarget (completePlanResult
                        (selectedBoundaryPlan boundary)))))
                    (bindings (registry survivor))
                  replaced = selectedOrderedReplaceSelectedLeft nameEq
                    selected
                    (closeSourceFiber component parent retiredFlag table
                      accumulator view outcome)
                    (closeTargetFiber keyEq component parent retiredFlag
                      table accumulator outcome (worldState before))
                    (bindings (planTarget (completePlanResult
                      (selectedBoundaryPlan boundary))))
                    (bindings (registry survivor)) entriesFound static
                    (selectedBoundaryOrderedControls boundary)
                  0 nextOrdered : SelectedOrderedRegistryControlsRelated
                    name key world error value selected
                    (bindings (planTarget (completePlanResult nextPlan)))
                    (bindings (registry survivor))
                  nextOrdered = selectedOrderedTransport
                    (sym targetBindings) Refl replaced
                  0 afterToSurvivor : EffectStateRelated keyEq
                    (projectEffectState @{nameEq} afterState)
                    (projectEffectState @{nameEq} survivor)
                  afterToSurvivor = selectedUnloadClosesEffectBoundary
                    nameEq keyEq selected before afterState survivor whole
                    (selectedBoundaryEffects boundary) closing
                  0 nextInactive : CurrentRegisteredInactiveFibers name
                    key world error value nameEq registered live afterState
                  nextInactive = currentRegisteredInactiveStep nameEq keyEq
                    registered ordinal live unique (LUnload selected) before
                    afterState LUnloadTag raw
                    (unloadIsNotBegin {nameEq = nameEq} {selected = selected}
                      {registered = registered} {ordinal = ordinal} {live = live})
                    sourceInactive
                  0 nextEmpty : CurrentRegisteredEmptyTables name key world
                    error value nameEq registered live afterState
                  nextEmpty = currentRegisteredEmptyTableStep nameEq keyEq
                    registered ordinal live unique (LUnload selected) before
                    afterState LUnloadTag raw
                    (unloadIsNotBegin {nameEq = nameEq} {selected = selected}
                      {registered = registered} {ordinal = ordinal} {live = live})
                    sourceInactive sourceEmpty
                  0 nextUnique : GenerationEnvironmentNamesUnique live
                  nextUnique = advanceGenerationEnvironmentPreservesUnique
                    nameEq ordinal
                    (the (Action name key value world error) (LUnload selected))
                    live unique
                  0 nextPlanEmpty : EmptyTableInactivePlan name key world
                    error value nameEq
                    (inactiveLeafPlan (completePlanResult nextPlan))
                  nextPlanEmpty = completeCurrentRegisteredPlanHasEmptyTables
                    nameEq registered live nextUnique (worldState afterState)
                    (registry afterState) nextPlan nextEmpty
                  0 afterToPlan : EffectStateRelated keyEq
                    (projectEffectState @{nameEq} afterState)
                    (projectEffectState @{nameEq}
                      (the (SystemState name key value world error)
                        (MkSystemState (worldState afterState)
                          (planTarget (completePlanResult nextPlan)))))
                  afterToPlan = replace
                    {p = \observed => EffectStateRelated keyEq
                      (projectEffectState @{nameEq} observed)
                      (projectEffectState @{nameEq}
                        (the (SystemState name key value world error)
                          (MkSystemState (worldState afterState)
                            (planTarget
                              (completePlanResult nextPlan)))))}
                    (stateEtaClose afterState)
                    (emptyInactivePlanPreservesEffects nameEq keyEq
                      (worldState afterState) (registry afterState)
                      (planTarget (completePlanResult nextPlan))
                      (inactiveLeafPlan (completePlanResult nextPlan))
                      nextPlanEmpty)
                  0 planToSurvivor : EffectStateRelated keyEq
                    (projectEffectState @{nameEq}
                      (the (SystemState name key value world error)
                        (MkSystemState (worldState afterState)
                          (planTarget (completePlanResult nextPlan)))))
                    (projectEffectState @{nameEq} survivor)
                  planToSurvivor = effectTransitiveClose
                    (effectSymmetricClose afterToPlan) afterToSurvivor
                  0 afterWellFormed : registryWellFormed @{nameEq} @{keyEq}
                    afterState = True
                  afterWellFormed = preservationTheoremProof nameEq keyEq
                    (LUnload selected) before afterState LUnloadTag
                    (selectedOriginalWellFormed boundary) raw
              in MkPostCloseSelectedBoundary nextPlan planToSurvivor
                nextOrdered (selectedBoundarySurvivorCleanInactive boundary)
                afterWellFormed (selectedSurvivorWellFormed boundary)
                nextInactive nextEmpty nextPlanEmpty
