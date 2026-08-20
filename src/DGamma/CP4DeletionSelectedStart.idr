module DGamma.CP4DeletionSelectedStart

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionCommuteCore
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionGenerationBounds
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4RuntimeBindings
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

0 environmentElemBirthBound :
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentBounded ordinal live ->
  Elem (actor, generation) live ->
  LT (generationBirthOrdinal generation) ordinal
environmentElemBirthBound [] bounded present impossible
environmentElemBirthBound
  ((actor, generation) :: rest) (headBound, tailBound) Here = headBound
environmentElemBirthBound
  ((current, currentGeneration) :: rest) (headBound, tailBound) (There later) =
    environmentElemBirthBound rest tailBound later

0 generationScanPreservesBounded :
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) ->
  GenerationEnvironmentBounded ordinal live ->
  (trace : Transitions first finalState) ->
  GenerationTraceScan nameEq ordinal live trace finalOrdinal finalLive ->
  GenerationEnvironmentBounded finalOrdinal finalLive
generationScanPreservesBounded nameEq bounded NoTransitions
  GenerationTraceScanEnd = bounded
generationScanPreservesBounded nameEq bounded
  (MoreTransitions transition rest)
  (GenerationTraceScanStep transition rest tail) =
    generationScanPreservesBounded nameEq
      (advanceGenerationEnvironmentBounded nameEq _
        (transitionAction transition) _ bounded) rest tail

0 noCurrentRegisteredAtEpisodeStart :
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentBounded startOrdinal live ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    LTE startOrdinal (generationBirthOrdinal generation)) ->
  (actor : name) -> (generation : RegistrationGeneration name) ->
  Elem (actor, generation) live -> Elem generation registered -> Void
noCurrentRegisteredAtEpisodeStart registered live bounded lower actor generation
  present member =
    let bornBefore = environmentElemBirthBound live bounded present
        bornAfter = lower generation member
        impossibleBound = transitive bornBefore bornAfter
    in succNotLTEpred impossibleBound

||| At the selected opening boundary every exact R generation is still unborn,
||| so the complete current-generation plan is constructively the identity.
public export
0 episodeStartCompletePlan :
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (startOrdinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentBounded startOrdinal live ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    LTE startOrdinal (generationBirthOrdinal generation)) ->
  (source : Registry name key value world error) ->
  CompleteCurrentRegisteredPlanResult name key world error value nameEq
    registered live source
episodeStartCompletePlan nameEq registered startOrdinal live bounded lower source =
  MkCompleteCurrentRegisteredPlanResult
    (MkCurrentRegisteredPlanResult source NoInactiveLeafDeletion
      (\actor, outside => ActorOutsideDeletionEnd))
    (\actor, generation, present, member =>
      void (noCurrentRegisteredAtEpisodeStart registered live bounded lower actor
        generation present member))

0 episodeStartPlanTargetSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (startOrdinal : Nat) -> (live : GenerationEnvironment name) ->
  (bounded : GenerationEnvironmentBounded startOrdinal live) ->
  (lower : (generation : RegistrationGeneration name) ->
    Elem generation registered ->
    LTE startOrdinal (generationBirthOrdinal generation)) ->
  (source : Registry name key value world error) ->
  planTarget (completePlanResult
    (episodeStartCompletePlan {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq registered startOrdinal live
      bounded lower source)) = source
episodeStartPlanTargetSame nameEq registered startOrdinal live bounded lower
  source = Refl

0 fiberStaticReflexiveStart :
  (fiber : Fiber name key value world error) ->
  FiberStaticRelated name key world error value fiber fiber
fiberStaticReflexiveStart
  (MkFiber component parent retiredFlag table lifecycle) =
    FibersStaticRelated parent parent retiredFlag retiredFlag table table
      lifecycle lifecycle Refl Refl

public export
0 selectedOrderedReflexive :
  (nameEq : DecEq name) -> (selected : name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    entries entries
selectedOrderedReflexive nameEq selected [] = SelectedOrderedControlsNil
selectedOrderedReflexive nameEq selected (Bind actor fiber :: rest)
  with (decEq @{nameEq} actor selected)
  selectedOrderedReflexive nameEq actor (Bind actor fiber :: rest) | Yes Refl =
    SelectedOrderedControlsCons actor
      (SelectedFiberControls Refl (fiberStaticReflexiveStart fiber))
      (selectedOrderedReflexive nameEq actor rest)
  selectedOrderedReflexive nameEq selected (Bind actor fiber :: rest) |
    No distinct =
      SelectedOrderedControlsCons actor
        (ForeignFiberControls distinct (fiberControlReflexive fiber))
        (selectedOrderedReflexive nameEq selected rest)

||| Checked L-Begin changes only the selected cell.  Replacing that cell on the
||| left of the reflexive ordered skeleton yields the selected-exempt opening
||| controls without equating registry uniqueness certificates.
public export
0 selectedOpeningOrderedControls :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {preStart, start : SystemState name key value world error} ->
  (opening : BeginStep nameEq keyEq selected preStart start) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (bindings (registry start)) (bindings (registry preStart))
selectedOpeningOrderedControls nameEq keyEq selected
  {preStart = MkSystemState ambient source} {start} opening =
    let raw = checkedActionProjects nameEq keyEq (LBegin selected)
          (MkSystemState ambient source) start LBeginTag (beginEquation opening)
        clean = selectedCleanInactiveBeforeBegin nameEq keyEq selected
          (MkSystemState ambient source) start (beginEquation opening)
    in case clean of
      SelectedCleanInactiveWitness component parent retiredFlag table found =>
        openingByRetired component parent retiredFlag table found raw
  where
  0 openingByRetired :
    (component : Component key value world error) ->
    (parent : Parent name) -> (retiredFlag : Bool) ->
    (table : OwnedTable key value (componentProvisions component)) ->
    lookupFiber @{nameEq} selected source = Just
      (MkFiber component parent retiredFlag table (Inactive Nothing)) ->
    applyAction @{nameEq} @{keyEq} (LBegin selected)
      (MkSystemState ambient source) = Just (LBeginTag, start) ->
    SelectedOrderedRegistryControlsRelated name key world error value selected
      (bindings (registry start)) (bindings source)
  openingByRetired component parent True table found raw =
    let actionNothing : (applyAction @{nameEq} @{keyEq}
          (the (Action name key value world error) (LBegin selected))
          (MkSystemState ambient source) = Nothing)
        actionNothing = rewrite found in Refl
    in void (nothingIsNotJust (trans (sym actionNothing) raw))
  openingByRetired component parent False table found raw
    with (targetFiber @{nameEq} @{keyEq}
      (MkFiber component parent False table (Inactive Nothing)) source)
      proof target
    openingByRetired component parent False table found raw | Nothing =
      let actionNothing : (applyAction @{nameEq} @{keyEq}
            (the (Action name key value world error) (LBegin selected))
            (MkSystemState ambient source) = Nothing)
          actionNothing = rewrite found in rewrite target in Refl
      in void (nothingIsNotJust (trans (sym actionNothing) raw))
    openingByRetired component parent False table found raw | Just view =
      let oldFiber : Fiber name key value world error
          oldFiber = MkFiber component parent False table (Inactive Nothing)
          nextFiber : Fiber name key value world error
          nextFiber = MkFiber component parent False table
            (Reloading (componentProgram component) (\local => local) view)
          concreteAfter : SystemState name key value world error
          concreteAfter = MkSystemState ambient
            (replaceBinding @{nameEq} selected nextFiber source)
          concrete : applyAction @{nameEq} @{keyEq} (LBegin selected)
            (MkSystemState ambient source) = Just (LBeginTag, concreteAfter)
          concrete = rewrite found in rewrite target in Refl
          pairSame : (LBeginTag, concreteAfter) = (LBeginTag, start)
          pairSame = justInjective (trans (sym concrete) raw)
          0 afterShape : concreteAfter = start
          afterShape = cong snd pairSame
          0 static : FiberStaticRelated name key world error value nextFiber
            oldFiber
          static = FibersStaticRelated parent parent False False table table
            (Reloading (componentProgram component) (\local => local) view)
            (Inactive Nothing) Refl Refl
          0 entriesFound : lookupEntries @{nameEq} selected (bindings source) =
            Just oldFiber
          entriesFound = trans (sym (lookupFiberAsEntries nameEq selected source))
            found
          0 replaced : SelectedOrderedRegistryControlsRelated name key world
            error value selected
            (replaceEntries @{nameEq} selected nextFiber (bindings source))
            (bindings source)
          replaced = selectedOrderedReplaceSelectedLeft nameEq selected oldFiber
            nextFiber (bindings source) (bindings source) entriesFound static
            (selectedOrderedReflexive nameEq selected (bindings source))
          0 runtimeBindings : bindings
            (replaceBinding @{nameEq} selected nextFiber source) =
            replaceEntries @{nameEq} selected nextFiber (bindings source)
          runtimeBindings = replaceBindingRuntimeBindings nameEq selected
            nextFiber source
          0 concreteControls : SelectedOrderedRegistryControlsRelated name key
            world error value selected
            (bindings (replaceBinding @{nameEq} selected nextFiber source))
            (bindings source)
          concreteControls = selectedOrderedTransport (sym runtimeBindings)
            Refl replaced
      in selectedOrderedTransport
        (cong (\state => bindings (registry state)) afterShape) Refl
        concreteControls

||| Assemble the first selected quotient boundary from the public episode-start
||| scan and exact registered-birth lower bound.
public export
0 initialSelectedEpisodeBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (episodeStartOrdinal : Nat) ->
  (episodeStartLive : GenerationEnvironment name) ->
  {beforeFirst, beforeLast, episodeFirst, episodeLast :
    SystemState name key value world error} ->
  (before : Transitions beforeFirst beforeLast) ->
  GenerationTraceScan nameEq 0 [] before episodeStartOrdinal episodeStartLive ->
  (episodeTrace : Transitions episodeFirst episodeLast) ->
  RegisteredGenerationsDuring selected episodeStartOrdinal registered
    episodeTrace ->
  {preStart, start : SystemState name key value world error} ->
  (whole : Transitions start wholeLast) ->
  (opening : BeginStep nameEq keyEq selected preStart start) ->
  registryWellFormed @{nameEq} @{keyEq} preStart = True ->
  SelectedEpisodeReplayBoundary name key world error value nameEq keyEq selected
    registered (S episodeStartOrdinal) episodeStartLive whole start preStart
initialSelectedEpisodeBoundary nameEq keyEq selected registered
  episodeStartOrdinal episodeStartLive before beforeScan episodeTrace
  registeredDuring whole opening
  preWellFormed =
    let bounded = generationScanPreservesBounded nameEq () before beforeScan
        lower = registeredDuringBirthLowerBound registeredDuring
        plan : CompleteCurrentRegisteredPlanResult name key world error value
          nameEq registered episodeStartLive (registry start)
        plan = episodeStartCompletePlan nameEq registered episodeStartOrdinal
          episodeStartLive bounded lower (registry start)
        0 targetSame : planTarget (completePlanResult plan) = registry start
        targetSame = episodeStartPlanTargetSame {name = name} {key = key}
          {world = world} {error = error} {value = value} nameEq registered
          episodeStartOrdinal episodeStartLive bounded lower (registry start)
        0 openingOrdered : SelectedOrderedRegistryControlsRelated name key
          world error value selected (bindings (registry start))
          (bindings (registry preStart))
        openingOrdered = selectedOpeningOrderedControls nameEq keyEq selected
          opening
        0 ordered : SelectedOrderedRegistryControlsRelated name key world error
          value selected
          (bindings (planTarget (completePlanResult plan)))
          (bindings (registry preStart))
        ordered = selectedOrderedTransport
          (cong bindings (sym targetSame)) Refl openingOrdered
    in beginSelectedEpisodeReplayBoundary nameEq keyEq selected registered
      episodeStartOrdinal episodeStartLive whole opening plan ordered
      preWellFormed
