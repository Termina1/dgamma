module DGamma.CP4DeletionSelectedBoundary

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionSelectedEffectCore
import Decidable.Equality

%default total

||| Static selected-fiber relation used while its lifecycle episode is erased.
||| The component, parent, and retirement bit remain exact; owned tables are on
||| the effect side and the selected lifecycle is deliberately unconstrained.
public export
data FiberStaticRelated :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  Fiber name key value world error -> Fiber name key value world error -> Type where
  FibersStaticRelated :
    {key : Type} -> {value : key -> Type} ->
    {world, error, name : Type} ->
    {component : Component key value world error} ->
    (leftParent, rightParent : Parent name) ->
    (leftRetired, rightRetired : Bool) ->
    (leftTable, rightTable : OwnedTable key value
      (componentProvisions component)) ->
    (leftLifecycle, rightLifecycle : Lifecycle key value world error name
      (dependencies (componentDependencies component))
      (componentProvisions component)) ->
    leftParent = rightParent -> leftRetired = rightRetired ->
    FiberStaticRelated name key world error value
      (MkFiber component leftParent leftRetired leftTable leftLifecycle)
      (MkFiber component rightParent rightRetired rightTable rightLifecycle)

0 fiberStaticReflexive : (fiber : Fiber name key value world error) ->
  FiberStaticRelated name key world error value fiber fiber
fiberStaticReflexive
  (MkFiber component parent retiredFlag table lifecycle) =
    FibersStaticRelated parent parent retiredFlag retiredFlag table table
      lifecycle lifecycle Refl Refl

0 fiberStaticTransitive :
  FiberStaticRelated name key world error value first middle ->
  FiberStaticRelated name key world error value middle finalState ->
  FiberStaticRelated name key world error value first finalState
fiberStaticTransitive
  (FibersStaticRelated firstParent middleParent firstRetired middleRetired
    firstTable middleTable firstLifecycle middleLifecycle firstParentEq
    firstRetiredEq)
  (FibersStaticRelated middleParent finalParent middleRetired finalRetired
    middleTable finalTable middleLifecycle finalLifecycle secondParentEq
    secondRetiredEq) =
      FibersStaticRelated firstParent finalParent firstRetired finalRetired
        firstTable finalTable firstLifecycle finalLifecycle
        (trans firstParentEq secondParentEq)
        (trans firstRetiredEq secondRetiredEq)

||| One ordered control cell in the selected quotient.  The selected actor uses
||| the static relation above; every other actor retains the full extensional
||| lifecycle/accumulator relation.
public export
data SelectedFiberControlsRelated :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (selected, actor : name) ->
  Fiber name key value world error -> Fiber name key value world error -> Type where
  SelectedFiberControls :
    {key : Type} -> {value : key -> Type} ->
    {world, error, name : Type} ->
    {selected, actor : name} ->
    {left, right : Fiber name key value world error} ->
    actor = selected ->
    FiberStaticRelated name key world error value left right ->
    SelectedFiberControlsRelated name key world error value selected actor
      left right
  ForeignFiberControls :
    {key : Type} -> {value : key -> Type} ->
    {world, error, name : Type} ->
    {selected, actor : name} ->
    {left, right : Fiber name key value world error} ->
    Not (actor = selected) -> FiberControlRelated left right ->
    SelectedFiberControlsRelated name key world error value selected actor
      left right

||| Ordered, domain-exact selected-episode control skeleton.  It is stated
||| against the complete current-R plan target, so exact R leaves are absent and
||| provider selection keeps its executable registry order.
public export
data SelectedOrderedRegistryControlsRelated :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (selected : name) ->
  List (Binding name (FiberAt name key value world error)) ->
  List (Binding name (FiberAt name key value world error)) -> Type where
  SelectedOrderedControlsNil :
    {key : Type} -> {value : key -> Type} ->
    {world, error, name : Type} -> {selected : name} ->
    SelectedOrderedRegistryControlsRelated name key world error value selected
      [] []
  SelectedOrderedControlsCons :
    {key : Type} -> {value : key -> Type} ->
    {world, error, name : Type} -> {selected : name} ->
    (actor : name) ->
    {leftFiber, rightFiber : Fiber name key value world error} ->
    {leftRest, rightRest :
      List (Binding name (FiberAt name key value world error))} ->
    SelectedFiberControlsRelated name key world error value selected actor
      leftFiber rightFiber ->
    SelectedOrderedRegistryControlsRelated name key world error value selected
      leftRest rightRest ->
    SelectedOrderedRegistryControlsRelated name key world error value selected
      (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest)

||| Replace the selected cell on the plan side while keeping the survivor
||| fixed.  Lookup evidence pins the unique ordered occurrence; the new static
||| relation composes with the old selected cell.
public export
0 selectedOrderedReplaceSelectedLeft :
  (nameEq : DecEq name) -> (selected : name) ->
  (oldFiber, nextFiber : Fiber name key value world error) ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  lookupEntries @{nameEq} selected left = Just oldFiber ->
  FiberStaticRelated name key world error value nextFiber oldFiber ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    left right ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (replaceEntries @{nameEq} selected nextFiber left) right
selectedOrderedReplaceSelectedLeft nameEq selected oldFiber nextFiber [] []
  found nextToOld SelectedOrderedControlsNil = case found of Refl impossible
selectedOrderedReplaceSelectedLeft nameEq selected oldFiber nextFiber
  (Bind current leftFiber :: leftRest) (Bind current rightFiber :: rightRest)
  found nextToOld (SelectedOrderedControlsCons current relation tail)
  with (decEq @{nameEq} selected current)
  selectedOrderedReplaceSelectedLeft nameEq current oldFiber nextFiber
    (Bind current leftFiber :: leftRest) (Bind current rightFiber :: rightRest)
    found nextToOld
    (SelectedOrderedControlsCons current
      (SelectedFiberControls currentIsSelected oldStatic) tail) | Yes Refl =
        let 0 oldSame = justInjective found
            0 nextToHead : FiberStaticRelated name key world error value
              nextFiber leftFiber
            nextToHead = replace
              {p = \observed => FiberStaticRelated name key world error value
                nextFiber observed}
              (sym oldSame) nextToOld
        in SelectedOrderedControlsCons current
          (SelectedFiberControls currentIsSelected
            (fiberStaticTransitive nextToHead oldStatic)) tail
  selectedOrderedReplaceSelectedLeft nameEq current oldFiber nextFiber
    (Bind current leftFiber :: leftRest) (Bind current rightFiber :: rightRest)
    found nextToOld
    (SelectedOrderedControlsCons current
      (ForeignFiberControls currentDistinct fibers) tail) | Yes Refl =
        void (currentDistinct Refl)
  selectedOrderedReplaceSelectedLeft nameEq selected oldFiber nextFiber
    (Bind current leftFiber :: leftRest) (Bind current rightFiber :: rightRest)
    found nextToOld (SelectedOrderedControlsCons current relation tail) |
    No selectedDifferent =
      SelectedOrderedControlsCons current relation
        (selectedOrderedReplaceSelectedLeft nameEq selected oldFiber nextFiber
          leftRest rightRest found nextToOld tail)

public export
0 selectedOrderedInsertForeign :
  (selected, actor : name) -> Not (actor = selected) ->
  FiberControlRelated leftFiber rightFiber ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    left right ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (Bind actor leftFiber :: left) (Bind actor rightFiber :: right)
selectedOrderedInsertForeign selected actor distinct fibers tail =
  SelectedOrderedControlsCons actor (ForeignFiberControls distinct fibers) tail

public export
0 selectedOrderedReplaceForeign :
  (nameEq : DecEq name) -> (selected, actor : name) ->
  Not (actor = selected) ->
  (nextLeft, nextRight : Fiber name key value world error) ->
  FiberControlRelated nextLeft nextRight ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    left right ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (replaceEntries @{nameEq} actor nextLeft left)
    (replaceEntries @{nameEq} actor nextRight right)
selectedOrderedReplaceForeign nameEq selected actor distinct nextLeft nextRight
  nextRelated [] [] SelectedOrderedControlsNil = SelectedOrderedControlsNil
selectedOrderedReplaceForeign nameEq selected actor distinct nextLeft nextRight
  nextRelated (Bind current leftFiber :: leftRest)
  (Bind current rightFiber :: rightRest)
  (SelectedOrderedControlsCons current currentRelated tail)
  with (decEq @{nameEq} actor current)
  selectedOrderedReplaceForeign nameEq selected current distinct nextLeft
    nextRight nextRelated (Bind current leftFiber :: leftRest)
    (Bind current rightFiber :: rightRest)
    (SelectedOrderedControlsCons current
      (SelectedFiberControls currentIsSelected static) tail) | Yes Refl =
        void (distinct currentIsSelected)
  selectedOrderedReplaceForeign nameEq selected current distinct nextLeft
    nextRight nextRelated (Bind current leftFiber :: leftRest)
    (Bind current rightFiber :: rightRest)
    (SelectedOrderedControlsCons current
      (ForeignFiberControls currentDistinct oldRelated) tail) | Yes Refl =
        SelectedOrderedControlsCons current
          (ForeignFiberControls distinct nextRelated) tail
  selectedOrderedReplaceForeign nameEq selected actor distinct nextLeft
    nextRight nextRelated (Bind current leftFiber :: leftRest)
    (Bind current rightFiber :: rightRest)
    (SelectedOrderedControlsCons current currentRelated tail) |
    No actorDifferent =
      SelectedOrderedControlsCons current currentRelated
        (selectedOrderedReplaceForeign nameEq selected actor distinct nextLeft
          nextRight nextRelated leftRest rightRest tail)

public export
0 selectedOrderedDeleteForeign :
  (nameEq : DecEq name) -> (selected, actor : name) ->
  Not (actor = selected) ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    left right ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (deleteEntries @{nameEq} actor left) (deleteEntries @{nameEq} actor right)
selectedOrderedDeleteForeign nameEq selected actor distinct [] []
  SelectedOrderedControlsNil = SelectedOrderedControlsNil
selectedOrderedDeleteForeign nameEq selected actor distinct
  (Bind current leftFiber :: leftRest) (Bind current rightFiber :: rightRest)
  (SelectedOrderedControlsCons current currentRelated tail)
  with (decEq @{nameEq} actor current)
  selectedOrderedDeleteForeign nameEq selected current distinct
    (Bind current leftFiber :: leftRest) (Bind current rightFiber :: rightRest)
    (SelectedOrderedControlsCons current
      (SelectedFiberControls currentIsSelected static) tail) | Yes Refl =
        void (distinct currentIsSelected)
  selectedOrderedDeleteForeign nameEq selected current distinct
    (Bind current leftFiber :: leftRest) (Bind current rightFiber :: rightRest)
    (SelectedOrderedControlsCons current
      (ForeignFiberControls currentDistinct oldRelated) tail) | Yes Refl = tail
  selectedOrderedDeleteForeign nameEq selected actor distinct
    (Bind current leftFiber :: leftRest) (Bind current rightFiber :: rightRest)
    (SelectedOrderedControlsCons current currentRelated tail) |
    No actorDifferent =
      SelectedOrderedControlsCons current currentRelated
        (selectedOrderedDeleteForeign nameEq selected actor distinct leftRest
          rightRest tail)

public export
0 selectedOrderedLookupControlsRelated :
  (nameEq : DecEq name) -> (selected, actor : name) ->
  Not (actor = selected) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    left right ->
  FiberControlMaybeRelated
    (lookupEntries @{nameEq} {key = name}
      {value = FiberAt name key value world error} actor left)
    (lookupEntries @{nameEq} {key = name}
      {value = FiberAt name key value world error} actor right)
selectedOrderedLookupControlsRelated nameEq selected actor distinct
  SelectedOrderedControlsNil = NoControlFibers
selectedOrderedLookupControlsRelated nameEq selected actor distinct
  (SelectedOrderedControlsCons current relation tail)
  with (decEq @{nameEq} actor current)
  selectedOrderedLookupControlsRelated nameEq selected current distinct
    (SelectedOrderedControlsCons current
      (SelectedFiberControls currentIsSelected static) tail) | Yes Refl =
        void (distinct currentIsSelected)
  selectedOrderedLookupControlsRelated nameEq selected current distinct
    (SelectedOrderedControlsCons current
      (ForeignFiberControls currentDistinct fibers) tail) | Yes Refl =
        SomeControlFibers fibers
  selectedOrderedLookupControlsRelated nameEq selected actor distinct
    (SelectedOrderedControlsCons current relation tail) | No actorDifferent =
      selectedOrderedLookupControlsRelated nameEq selected actor distinct tail

public export
0 lookupFiberAsEntries :
  (nameEq : DecEq name) -> (actor : name) ->
  (context : Registry name key value world error) ->
  lookupFiber @{nameEq} actor context =
    lookupEntries @{nameEq} actor (bindings context)
lookupFiberAsEntries nameEq actor (MkCoeffectContext entries unique) = Refl

public export
0 lookupOutsideInactivePlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target) ->
  ActorOutsideDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} actor plan ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor target =
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor source
lookupOutsideInactivePlan nameEq actor source source NoInactiveLeafDeletion
  ActorOutsideDeletionEnd = Refl
lookupOutsideInactivePlan nameEq actor source target
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest)
  (ActorOutsideDeletionStep rest distinct outsideRest) =
    trans (lookupOutsideInactivePlan nameEq actor
      (deleteBinding @{nameEq} removed source) target rest outsideRest)
      (lookupDeleteOther actor removed distinct source)

||| Control agreement needed only for actors whose current generation is not
||| erased and which are not the selected activation itself.  This is now a
||| projection of the ordered skeleton rather than a second drifting invariant.
public export
SelectedControlsOutside :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  List (RegistrationGeneration name) -> GenerationEnvironment name ->
  SystemState name key value world error ->
  SystemState name key value world error -> Type
SelectedControlsOutside {name} nameEq selected registered live original
  survivor =
    (actor : name) -> Not (actor = selected) ->
    ActorOutsideCurrentRegistered actor registered live ->
    FiberControlMaybeRelated
      (lookupFiber @{nameEq} actor (registry original))
      (lookupFiber @{nameEq} actor (registry survivor))

||| Combined intermediate boundary for the selected-episode quotient.  It owns
||| the exact current-R deletion plan, Theorem-61 effect recovery, an ordered
||| selected-exempt control skeleton, and both checked-validity facts.  Unlike
||| `NoEpisodeReplayBoundary`, no raw runtime-snapshot equality is claimed:
||| selected effects are related only after applying the live accumulator.
public export
record SelectedEpisodeReplayBoundary
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (registered : List (RegistrationGeneration name))
  (ordinal : Nat) (live : GenerationEnvironment name)
  {wholeFirst, wholeLast : SystemState name key value world error}
  (whole : Transitions wholeFirst wholeLast)
  (original, survivor : SystemState name key value world error) where
  constructor MkSelectedEpisodeReplayBoundary
  0 selectedBoundaryEffects : SelectedEffectReplayBoundary name key world error
    value nameEq keyEq selected whole original survivor
  selectedBoundaryPlan : CompleteCurrentRegisteredPlanResult name key world
    error value nameEq registered live (registry original)
  0 selectedBoundaryOrderedControls :
    SelectedOrderedRegistryControlsRelated name key world error value selected
      (bindings (planTarget
        (completePlanResult selectedBoundaryPlan)))
      (bindings (registry survivor))
  0 selectedOriginalWellFormed : registryWellFormed @{nameEq} @{keyEq}
    original = True
  0 selectedSurvivorWellFormed : registryWellFormed @{nameEq} @{keyEq}
    survivor = True

public export
0 selectedBoundaryControls :
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole original survivor) ->
  SelectedControlsOutside nameEq selected registered live original survivor
selectedBoundaryControls {name} {key} {world} {error} {value}
  {registered} {live} {original} {survivor}
  (MkSelectedEpisodeReplayBoundary effects completePlan orderedControls
    originalWellFormed survivorWellFormed)
  actor actorDistinct outsideCurrent =
  let 0 outsidePlan : ActorOutsideDeletionPlan
        {name = name} {key = key} {value = value} {world = world}
        {error = error} actor
        (inactiveLeafPlan (completePlanResult completePlan))
      outsidePlan = actorOutsidePlan (completePlanResult completePlan) actor
        outsideCurrent
      0 planLookup : lookupFiber @{nameEq} {name = name} {key = key}
            {value = value} {world = world} {error = error} actor
            (planTarget (completePlanResult completePlan)) =
          lookupFiber @{nameEq} {name = name} {key = key} {value = value}
            {world = world} {error = error} actor (registry original)
      planLookup = lookupOutsideInactivePlan nameEq actor (registry original)
        (planTarget (completePlanResult completePlan))
        (inactiveLeafPlan (completePlanResult completePlan)) outsidePlan
      0 orderedLookup : FiberControlMaybeRelated
        (lookupEntries @{nameEq} actor (bindings (planTarget
          (completePlanResult completePlan))))
        (lookupEntries @{nameEq} actor (bindings (registry survivor)))
      orderedLookup = selectedOrderedLookupControlsRelated nameEq selected
        actor actorDistinct orderedControls
      0 planToSurvivor : FiberControlMaybeRelated
        (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
          {world = world} {error = error} actor
          (planTarget (completePlanResult completePlan)))
        (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
          {world = world} {error = error} actor (registry survivor))
      planToSurvivor = replace
        {p = \left => FiberControlMaybeRelated left
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
            {world = world} {error = error} actor (registry survivor))}
        (sym (lookupFiberAsEntries nameEq actor
          (planTarget (completePlanResult completePlan))))
        (replace
          {p = \right => FiberControlMaybeRelated
            (lookupEntries @{nameEq} actor (bindings
              (planTarget (completePlanResult completePlan))))
            right}
          (sym (lookupFiberAsEntries nameEq actor (registry survivor)))
          orderedLookup)
  in replace
    {p = \observed => FiberControlMaybeRelated observed
      (lookupFiber @{nameEq} actor (registry survivor))}
    planLookup planToSurvivor

0 openingForeignLookup :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected, actor : name) ->
  Not (actor = selected) ->
  {preStart, start : SystemState name key value world error} ->
  (opening : BeginStep nameEq keyEq selected preStart start) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor (registry start) =
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor (registry preStart)
openingForeignLookup nameEq keyEq selected actor distinct {preStart} {start}
  opening =
    let 0 raw = checkedActionProjects nameEq keyEq (LBegin selected) preStart
          start LBeginTag (beginEquation opening)
        0 update = applyActionLocalUpdate nameEq keyEq (LBegin selected) preStart
          start LBeginTag raw
    in systemLocalUpdateForeign nameEq actor selected distinct preStart start
      update

||| Delete the checked opening and establish the first installed quotient
||| boundary.  The supplied complete plan is normally empty of current R births
||| at this ordinal; keeping it indexed avoids a second special representation.
public export
0 beginSelectedEpisodeReplayBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  {preStart, start : SystemState name key value world error} ->
  (whole : Transitions start wholeLast) ->
  (opening : BeginStep nameEq keyEq selected preStart start) ->
  (plan : CompleteCurrentRegisteredPlanResult name key world error value nameEq
    registered live (registry start)) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (bindings (planTarget (completePlanResult plan)))
    (bindings (registry preStart)) ->
  registryWellFormed @{nameEq} @{keyEq} preStart = True ->
  SelectedEpisodeReplayBoundary name key world error value nameEq keyEq selected
    registered (S ordinal) live whole start preStart
beginSelectedEpisodeReplayBoundary nameEq keyEq selected registered ordinal live
  {preStart} {start} whole opening plan ordered preWellFormed =
    let 0 raw = checkedActionProjects nameEq keyEq (LBegin selected) preStart
          start LBeginTag (beginEquation opening)
        0 startWellFormed = preservationTheoremProof nameEq keyEq
          (LBegin selected) preStart start LBeginTag preWellFormed raw
    in MkSelectedEpisodeReplayBoundary
      (beginSelectedEffectReplayBoundary nameEq keyEq selected whole opening)
      plan ordered startWellFormed preWellFormed

||| Generic structural half for a selected installed step that is skipped by
||| the quotient.  The caller supplies the already-proved effect step and the
||| complete plan transported through the selected registry replacement; this
||| lemma proves that all foreign controls and checked-validity facts persist.
public export
0 skippedSelectedStepPreservesEpisodeBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (survivor : SystemState name key value world error) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  actionOwner action = selected ->
  (nextEffects : SelectedEffectReplayBoundary name key world error value nameEq
    keyEq selected whole afterState survivor) ->
  (nextPlan : CompleteCurrentRegisteredPlanResult name key world error value
    nameEq registered live (registry afterState)) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (bindings (planTarget (completePlanResult nextPlan)))
    (bindings (registry survivor)) ->
  SelectedEpisodeReplayBoundary name key world error value nameEq keyEq selected
    registered (S ordinal) live whole afterState survivor
skippedSelectedStepPreservesEpisodeBoundary nameEq keyEq selected registered
  ordinal live action tag before afterState checked whole survivor
  (MkSelectedEpisodeReplayBoundary oldEffects oldPlan oldOrdered
    beforeWellFormed survivorWellFormed)
  owner nextEffects nextPlan nextOrdered =
    let 0 raw = checkedActionProjects nameEq keyEq action before afterState tag
          checked
        0 afterWellFormed = preservationTheoremProof nameEq keyEq action before
          afterState tag beforeWellFormed raw
    in MkSelectedEpisodeReplayBoundary nextEffects nextPlan nextOrdered
      afterWellFormed survivorWellFormed
