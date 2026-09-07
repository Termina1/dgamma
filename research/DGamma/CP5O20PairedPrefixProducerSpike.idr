module DGamma.CP5O20PairedPrefixProducerSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionFrameCore
import DGamma.CP4RecoveryAccumulator
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorOpen
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20EpisodeSynchronizationSpike
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Connect R180's observed-head recursion to the ACTUAL committed resolver.
||| The effect/view arguments are an induction hypothesis, not new O20 premises.
||| At canonical cuts the caller must instantiate the fixed accepted bijection.
export
0 pairedCommittedResolution :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (renaming : NameBijection name) -> (deps : List key) ->
  (leftView, rightView : View name deps) ->
  (left, right : SystemState name key value world error) ->
  RenamedRuntimeEffects name key world value renaming
    (projectEffectState {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} left)
    (projectEffectState {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} right) ->
  ViewRelatedBy renaming leftView rightView ->
  (resolveCommittedValues {name = name} {key = key} {value = value} {world = world}
    {error = error} @{nameEq} @{keyEq} deps leftView (registry left) =
   resolveCommittedValues {name = name} {key = key} {value = value} {world = world}
    {error = error} @{nameEq} @{keyEq} deps rightView (registry right))
pairedCommittedResolution name key world error value nameEq keyEq renaming deps
  leftView rightView left right effects views =
    trans (sym (resolveEffectValuesProjected nameEq keyEq deps leftView left))
      (trans (synchronizationResolutionFromObservedHeads name key world value keyEq
        renaming deps leftView rightView (projectEffectState @{nameEq} left)
        (projectEffectState @{nameEq} right) effects views)
        (resolveEffectValuesProjected nameEq keyEq deps rightView right))

||| Transport a paired induction hypothesis through independently PRODUCED
||| exact runtime projection frames. These frames compare each side only to
||| its own observation; no cross-cut agreement is invented by this helper.
export
0 pairedEffectsAcrossFrames :
  (name, key, world : Type) -> (value : key -> Type) ->
  (keyEq : DecEq key) -> (renaming : NameBijection name) ->
  (leftBefore, leftAfter, rightBefore, rightAfter : EffectState name key value world) ->
  EffectStateRelated keyEq leftBefore leftAfter ->
  RenamedRuntimeEffects name key world value renaming leftBefore rightBefore ->
  EffectStateRelated keyEq rightBefore rightAfter ->
  RenamedRuntimeEffects name key world value renaming leftAfter rightAfter
pairedEffectsAcrossFrames name key world value keyEq renaming leftBefore leftAfter
  rightBefore rightAfter leftFrame paired rightFrame =
    MkRenamedRuntimeEffects
      (trans (sym (ambientExact leftFrame))
        (trans (synchronizedAmbient paired) (ambientExact rightFrame)))
      (\selected => trans (sym (tablesExact leftFrame selected))
        (trans (synchronizedTables paired selected)
          (tablesExact rightFrame (renameForward renaming selected))))

||| Observe the actual decision before projecting a foreign table update.
||| The producer passes decEq itself; this equation is never a caller oracle.
export
0 pairedForeignTableObserved :
  (name, key, world : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (selected, actor : name) ->
  Not (selected = actor) -> (table : CoeffectContext key value) ->
  (state : EffectState name key value world) ->
  (decision : Dec (selected = actor)) ->
  (decEq @{nameEq} selected actor = decision) ->
  (bindings (effectTables (setEffectTable @{nameEq} actor table state) selected) =
    bindings (effectTables state selected))
pairedForeignTableObserved name key world value nameEq selected actor distinct table
  state (Yes same) observed = void (distinct same)
pairedForeignTableObserved name key world value nameEq selected actor distinct table
  state (No different) observed = rewrite observed in Refl

||| Simultaneous table-update law at the SAME bijection. Both equality
||| decisions are generated here; injectivity derives the foreign right case.
export
0 pairedSetTableBindings :
  (name, key, world : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (renaming : NameBijection name) -> (actor : name) ->
  (leftTable, rightTable : CoeffectContext key value) ->
  (bindings leftTable = bindings rightTable) ->
  (left, right : EffectState name key value world) ->
  RenamedRuntimeEffects name key world value renaming left right ->
  (selected : name) ->
  (bindings (effectTables (setEffectTable @{nameEq} actor leftTable left) selected) =
   bindings (effectTables (setEffectTable @{nameEq} (renameForward renaming actor)
      rightTable right) (renameForward renaming selected)))
pairedSetTableBindings name key world value nameEq renaming actor leftTable rightTable
  tableSame left right paired selected =
    case decEq @{nameEq} selected actor of
      Yes same => rewrite same in
        trans (cong bindings (effectTableAfterSetSelf nameEq actor leftTable left))
          (trans tableSame (sym (cong bindings (effectTableAfterSetSelf nameEq
            (renameForward renaming actor) rightTable right))))
      No different =>
        trans (pairedForeignTableObserved name key world value nameEq selected actor
          different leftTable left (decEq @{nameEq} selected actor) Refl)
          (trans (synchronizedTables paired selected)
            (sym (pairedForeignTableObserved name key world value nameEq
              (renameForward renaming selected) (renameForward renaming actor)
              (\same => different (trans (sym (renameLeftInverse renaming selected))
                (trans (cong (renameBackward renaming) same)
                  (renameLeftInverse renaming actor))))
              rightTable right (decEq @{nameEq} (renameForward renaming selected)
                (renameForward renaming actor)) Refl)))

||| Simultaneously update GLOBAL ambient and the two mapped actor tables.
||| These are actual executable setEffectTable/setEffectAmbient outputs.
export
0 pairedSetRuntimeEffects :
  (name, key, world : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (renaming : NameBijection name) -> (actor : name) ->
  (leftWorld, rightWorld : world) -> (leftWorld = rightWorld) ->
  (leftTable, rightTable : CoeffectContext key value) ->
  (bindings leftTable = bindings rightTable) ->
  (left, right : EffectState name key value world) ->
  RenamedRuntimeEffects name key world value renaming left right ->
  RenamedRuntimeEffects name key world value renaming
    (setEffectTable @{nameEq} actor leftTable (setEffectAmbient leftWorld left))
    (setEffectTable @{nameEq} (renameForward renaming actor) rightTable
      (setEffectAmbient rightWorld right))
pairedSetRuntimeEffects name key world value nameEq renaming actor leftWorld rightWorld
  worldSame leftTable rightTable tableSame left right paired =
    MkRenamedRuntimeEffects worldSame
      (pairedSetTableBindings name key world value nameEq renaming actor leftTable
        rightTable tableSame (setEffectAmbient leftWorld left)
        (setEffectAmbient rightWorld right)
        (MkRenamedRuntimeEffects worldSame (synchronizedTables paired)))

||| Simultaneous registration EFFECT producer at the two actual insertBinding
||| outputs. The surrounding paired trace must authenticate the OInsert guards;
||| this lemma neither assumes nor produces the missing canonical prefix choice.
export
0 pairedInsertEffects :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (renaming : NameBijection name) -> (actor : name) ->
  (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) ->
  (leftWorld, rightWorld : world) ->
  (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftAbsent : (lookupFiber {name = name} {key = key} {value = value}
    {world = world} {error = error} @{nameEq} actor leftRegistry = Nothing)) ->
  (rightAbsent : (lookupFiber {name = name} {key = key} {value = value}
    {world = world} {error = error} @{nameEq} (renameForward renaming actor)
      rightRegistry = Nothing)) ->
  RenamedRuntimeEffects name key world value renaming
    (projectEffectState {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} (MkSystemState leftWorld leftRegistry))
    (projectEffectState {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} (MkSystemState rightWorld rightRegistry)) ->
  RenamedRuntimeEffects name key world value renaming
    (projectEffectState {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} (MkSystemState leftWorld (insertBinding @{nameEq}
        actor (freshFiber component leftParent) leftRegistry leftAbsent)))
    (projectEffectState {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} (MkSystemState rightWorld (insertBinding @{nameEq}
        (renameForward renaming actor) (freshFiber component rightParent)
          rightRegistry rightAbsent)))
pairedInsertEffects name key world error value nameEq keyEq renaming actor component
  leftParent rightParent leftWorld rightWorld leftRegistry rightRegistry leftAbsent
  rightAbsent paired =
    pairedEffectsAcrossFrames name key world value keyEq renaming
      (setEffectTable @{nameEq} actor emptyContext
        (projectEffectState @{nameEq} (MkSystemState leftWorld leftRegistry)))
      (projectEffectState @{nameEq} (MkSystemState leftWorld (insertBinding @{nameEq}
        actor (freshFiber component leftParent) leftRegistry leftAbsent)))
      (setEffectTable @{nameEq} (renameForward renaming actor) emptyContext
        (projectEffectState @{nameEq} (MkSystemState rightWorld rightRegistry)))
      (projectEffectState @{nameEq} (MkSystemState rightWorld (insertBinding @{nameEq}
        (renameForward renaming actor) (freshFiber component rightParent)
          rightRegistry rightAbsent)))
      (projectInsertEffectFrame nameEq keyEq actor leftWorld component leftParent
        leftRegistry leftAbsent)
      (pairedSetRuntimeEffects name key world value nameEq renaming actor leftWorld
        rightWorld (synchronizedAmbient paired) emptyContext emptyContext Refl
        (projectEffectState @{nameEq} (MkSystemState leftWorld leftRegistry))
        (projectEffectState @{nameEq} (MkSystemState rightWorld rightRegistry)) paired)
      (projectInsertEffectFrame nameEq keyEq (renameForward renaming actor) rightWorld
        component rightParent rightRegistry rightAbsent)

||| Actual inserted/foreign lookup split, preserving the selected control cut.
||| No selected-name opacity: fresh and foreign cases use actual lookup laws.
export
0 pairedInsertControls :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (renaming : NameBijection name) -> (actor : name) ->
  (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) ->
  ParentRelatedBy renaming leftParent rightParent ->
  (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftAbsent : (lookupFiber {name = name} {key = key} {value = value}
    {world = world} {error = error} @{nameEq} actor leftRegistry = Nothing)) ->
  (rightAbsent : (lookupFiber {name = name} {key = key} {value = value}
    {world = world} {error = error} @{nameEq} (renameForward renaming actor)
      rightRegistry = Nothing)) ->
  (selected : name) ->
  MaybeFiberRelatedBy {name = name} {key = key} {world = world} {error = error}
    {value = value} renaming (lookupFiber {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} selected leftRegistry)
    (lookupFiber {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} (renameForward renaming selected) rightRegistry) ->
  MaybeFiberRelatedBy {name = name} {key = key} {world = world} {error = error}
    {value = value} renaming
    (lookupFiber {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} selected (insertBinding @{nameEq} actor
      (freshFiber component leftParent) leftRegistry leftAbsent))
    (lookupFiber {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} (renameForward renaming selected) (insertBinding @{nameEq}
      (renameForward renaming actor) (freshFiber component rightParent)
        rightRegistry rightAbsent))
pairedInsertControls name key world error value nameEq renaming actor component
  leftParent rightParent parents leftRegistry rightRegistry leftAbsent rightAbsent
  selected controls = case decEq @{nameEq} selected actor of
    Yes same => rewrite same in
      rewrite lookupInserted @{nameEq} actor (freshFiber component leftParent)
        leftRegistry leftAbsent in
      rewrite lookupInserted @{nameEq} (renameForward renaming actor)
        (freshFiber component rightParent) rightRegistry rightAbsent in
      RenamedPresent (RenamedFibers {component = component} leftParent rightParent
        False False emptyOwned emptyOwned (Inactive Nothing) (Inactive Nothing)
        parents Refl (RenamedInactive Refl))
    No different =>
      rewrite lookupInsertOther @{nameEq} selected actor different
        (freshFiber component leftParent) leftRegistry leftAbsent in
      rewrite lookupInsertOther @{nameEq} (renameForward renaming selected)
        (renameForward renaming actor)
        (\same => different (trans (sym (renameLeftInverse renaming selected))
          (trans (cong (renameBackward renaming) same)
            (renameLeftInverse renaming actor))))
        (freshFiber component rightParent) rightRegistry rightAbsent in controls

||| NONZERO paired-cut producer at actual registration outputs, not merely a
||| standalone effect law. It extends BOTH exact prefix occurrences, preserving
||| the original executions and expectedBridgeBijection. Actual transition
||| endpoints are observed by equations, never replaced with a chosen replay.
||| This handles a matched insertion pair; selecting such pairs along the
||| canonical schedules, Begin/Advance/Finish, and gaps remain separate work.
export
0 synchronizationRegistrationSuccessor :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftOriginalFinal, rightOriginalFinal, leftExecutionFinal,
   rightExecutionFinal, leftAfter, rightAfter : SystemState name key value world error} ->
  (leftOriginal : Transitions initial leftOriginalFinal) ->
  (rightOriginal : Transitions initial rightOriginalFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftOriginal rightOriginal) ->
  (leftExecution : Transitions initial leftExecutionFinal) ->
  (rightExecution : Transitions initial rightExecutionFinal) ->
  (selected, actor : name) -> (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) ->
  ParentRelatedBy (expectedBridgeBijection sameInputs) leftParent rightParent ->
  (leftWorld, rightWorld : world) ->
  (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftAbsent : (lookupFiber {name = name} {key = key} {value = value}
    {world = world} {error = error} @{nameEq} actor leftRegistry = Nothing)) ->
  (rightAbsent : (lookupFiber {name = name} {key = key} {value = value}
    {world = world} {error = error} @{nameEq}
      (renameForward (expectedBridgeBijection sameInputs) actor) rightRegistry = Nothing)) ->
  (leftPrefix : Transitions initial (MkSystemState leftWorld leftRegistry)) ->
  (rightPrefix : Transitions initial (MkSystemState rightWorld rightRegistry)) ->
  (leftEdge : Transition (MkSystemState leftWorld leftRegistry) leftAfter) ->
  (rightEdge : Transition (MkSystemState rightWorld rightRegistry) rightAfter) ->
  (leftTail : Transitions leftAfter leftExecutionFinal) ->
  (rightTail : Transitions rightAfter rightExecutionFinal) ->
  (leftAfter = MkSystemState leftWorld (insertBinding @{nameEq} actor
    (freshFiber component leftParent) leftRegistry leftAbsent)) ->
  (rightAfter = MkSystemState rightWorld (insertBinding @{nameEq}
    (renameForward (expectedBridgeBijection sameInputs) actor)
      (freshFiber component rightParent) rightRegistry rightAbsent)) ->
  SupportedCanonicalEpisodeSynchronization name key world error value nameEq keyEq
    leftOriginal rightOriginal sameInputs leftExecution rightExecution selected
    (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry)
    leftPrefix (MoreTransitions leftEdge leftTail)
    rightPrefix (MoreTransitions rightEdge rightTail) ->
  SupportedCanonicalEpisodeSynchronization name key world error value nameEq keyEq
    leftOriginal rightOriginal sameInputs leftExecution rightExecution selected
    leftAfter rightAfter
    (appendTransitions leftPrefix (MoreTransitions leftEdge NoTransitions)) leftTail
    (appendTransitions rightPrefix (MoreTransitions rightEdge NoTransitions)) rightTail
synchronizationRegistrationSuccessor name key world error value nameEq keyEq
  leftOriginal rightOriginal sameInputs leftExecution rightExecution selected actor
  component leftParent rightParent parents leftWorld rightWorld leftRegistry rightRegistry
  leftAbsent rightAbsent leftPrefix rightPrefix leftEdge rightEdge leftTail rightTail
  Refl Refl paired =
    MkSupportedCanonicalEpisodeSynchronization (synchronizedActorSupported paired)
      (trans (appendTransitionsAssociative leftPrefix
        (MoreTransitions leftEdge NoTransitions) leftTail)
        (synchronizedLeftCutOccurrence paired))
      (trans (appendTransitionsAssociative rightPrefix
        (MoreTransitions rightEdge NoTransitions) rightTail)
        (synchronizedRightCutOccurrence paired))
      (pairedInsertEffects name key world error value nameEq keyEq
        (expectedBridgeBijection sameInputs) actor component leftParent rightParent
        leftWorld rightWorld leftRegistry rightRegistry leftAbsent rightAbsent
        (synchronizedCutEffects paired))
      (pairedInsertControls name key world error value nameEq
        (expectedBridgeBijection sameInputs) actor component leftParent rightParent
        parents leftRegistry rightRegistry leftAbsent rightAbsent selected
        (synchronizedActorControls paired))

||| Simultaneous runtime-write projection, ready for actual Advance/Finish
||| observations. These are separate one-sided lookup/output observations;
||| cross-side world/table equalities must come from the deterministic consumer.
export
0 pairedRuntimeReplacementEffects :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (renaming : NameBijection name) -> (actor : name) ->
  (leftWorld, rightWorld, leftNextWorld, rightNextWorld : world) ->
  (leftOld, rightOld, leftNext, rightNext : Fiber name key value world error) ->
  (leftRegistry, rightRegistry : Registry name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world}
    {error = error} @{nameEq} actor leftRegistry = Just leftOld) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world}
    {error = error} @{nameEq} (renameForward renaming actor) rightRegistry = Just rightOld) ->
  (leftNextWorld = rightNextWorld) ->
  (bindings (ownedValues (fiberTable leftNext)) =
    bindings (ownedValues (fiberTable rightNext))) ->
  RenamedRuntimeEffects name key world value renaming
    (projectEffectState {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} (MkSystemState leftWorld leftRegistry))
    (projectEffectState {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} (MkSystemState rightWorld rightRegistry)) ->
  RenamedRuntimeEffects name key world value renaming
    (projectEffectState {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} (MkSystemState leftNextWorld
        (replaceBinding @{nameEq} actor leftNext leftRegistry)))
    (projectEffectState {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} (MkSystemState rightNextWorld
        (replaceBinding @{nameEq} (renameForward renaming actor) rightNext rightRegistry)))
pairedRuntimeReplacementEffects name key world error value nameEq keyEq renaming
  actor leftWorld rightWorld leftNextWorld rightNextWorld leftOld rightOld leftNext
  rightNext leftRegistry rightRegistry leftFound rightFound worlds tables paired =
    pairedEffectsAcrossFrames name key world value keyEq renaming
      (setEffectTable @{nameEq} actor (ownedValues (fiberTable leftNext))
        (setEffectAmbient leftNextWorld
          (projectEffectState @{nameEq} (MkSystemState leftWorld leftRegistry))))
      (projectEffectState @{nameEq} (MkSystemState leftNextWorld
        (replaceBinding @{nameEq} actor leftNext leftRegistry)))
      (setEffectTable @{nameEq} (renameForward renaming actor)
        (ownedValues (fiberTable rightNext)) (setEffectAmbient rightNextWorld
          (projectEffectState @{nameEq} (MkSystemState rightWorld rightRegistry))))
      (projectEffectState @{nameEq} (MkSystemState rightNextWorld
        (replaceBinding @{nameEq} (renameForward renaming actor) rightNext rightRegistry)))
      (projectRuntimeReplace nameEq keyEq actor leftWorld leftNextWorld leftOld
        leftNext leftRegistry leftFound (ownedValues (fiberTable leftNext)) Refl)
      (pairedSetRuntimeEffects name key world value nameEq renaming actor leftNextWorld
        rightNextWorld worlds (ownedValues (fiberTable leftNext))
        (ownedValues (fiberTable rightNext)) tables
        (projectEffectState @{nameEq} (MkSystemState leftWorld leftRegistry))
        (projectEffectState @{nameEq} (MkSystemState rightWorld rightRegistry)) paired)
      (projectRuntimeReplace nameEq keyEq (renameForward renaming actor) rightWorld
        rightNextWorld rightOld rightNext rightRegistry rightFound
        (ownedValues (fiberTable rightNext)) Refl)

||| Producer-owned deterministic SUCCESS observation. Both successful callback
||| results are tied to their actual runStepEffect inputs; the equality of
||| resulting local states and pointwise pushed undo is DERIVED, not supplied.
export
0 pairedSuccessfulOutcome :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (keyEq : DecEq key) -> (renaming : NameBijection name) ->
  (deps : List key) -> (provision : CoeffectSpec key) -> (actor : name) ->
  (step : StepEffect key value world error deps provision) ->
  (leftView, rightView : View name deps) ->
  (left, right : EffectState name key value world) ->
  (leftCapability, rightCapability : DepValues key value deps) ->
  (leftOlder, rightOlder : LocalState key value world provision ->
    LocalState key value world provision) ->
  (leftAfter, rightAfter : LocalState key value world provision) ->
  (leftUndo, rightUndo : LocalState key value world provision ->
    LocalState key value world provision) ->
  RenamedRuntimeEffects name key world value renaming left right ->
  ViewRelatedBy renaming leftView rightView ->
  AccumulatorRelated leftOlder rightOlder ->
  (resolveEffectValues @{keyEq} deps leftView left = Just leftCapability) ->
  (resolveEffectValues @{keyEq} deps rightView right = Just rightCapability) ->
  (runStepEffect step leftCapability (MkLocalState (effectAmbient left)
    (restrictOwnedPreservingOrder @{keyEq} provision (effectTables left actor))) =
      Right (leftAfter, leftUndo)) ->
  (runStepEffect step rightCapability (MkLocalState (effectAmbient right)
    (restrictOwnedPreservingOrder @{keyEq} provision
      (effectTables right (renameForward renaming actor)))) =
      Right (rightAfter, rightUndo)) ->
  ((leftAfter = rightAfter), AccumulatorRelated
    (pushLocalUndo @{keyEq} provision leftOlder leftUndo)
    (pushLocalUndo @{keyEq} provision rightOlder rightUndo))
pairedSuccessfulOutcome name key world error value keyEq renaming deps provision actor
  step leftView rightView left right leftCapability rightCapability leftOlder rightOlder
  leftAfter rightAfter leftUndo rightUndo effects views older leftResolved rightResolved
  leftRun rightRun =
    case trans (sym leftRun) (trans
      (synchronizationStepOutcome name key world error value keyEq renaming deps provision
        actor step leftView rightView left right leftCapability rightCapability effects
        views leftResolved rightResolved) rightRun) of
      Refl => (Refl, synchronizationPushedUndo key world error value keyEq provision
        leftOlder rightOlder rightAfter rightAfter rightUndo rightUndo older Refl)

||| Observed lookup provenance for a nonempty projected provider table.
||| The actual Maybe lookup is supplied by the producer; Nothing contradicts
||| the observed value. No Active/installed flag is guessed from table data.
export
0 pairedTableOwnerObserved :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (owner : name) -> (wanted : key) ->
  (fibers : Registry name key value world error) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world}
    {error = error} @{nameEq} owner fibers = observed) ->
  (provided : value wanted) ->
  (lookupBinding {key = key} {value = value} @{keyEq} wanted
    (case observed of Nothing => emptyContext
                      Just fiber => ownedValues (fiberTable fiber)) = Just provided) ->
  (fiber : Fiber name key value world error **
    ((lookupFiber {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} owner fibers = Just fiber),
     Elem wanted (dependencies (componentProvisions (fiberComponent fiber)))))
pairedTableOwnerObserved name key world error value nameEq keyEq owner wanted fibers
  Nothing found provided present = void (nothingIsNotJust present)
pairedTableOwnerObserved name key world error value nameEq keyEq owner wanted fibers
  (Just (MkFiber component parent retiredFlag
    (MkOwnedTable (MkCoeffectContext entries unique) confined) lifecycle))
  found provided present =
    (MkFiber component parent retiredFlag
      (MkOwnedTable (MkCoeffectContext entries unique) confined) lifecycle **
      (found, confined wanted (lookupJustElem @{keyEq} wanted entries provided present)))

||| B13 DISTINCT observed-value prerequisite, authorized while B12 is parked
||| at2/3. Split the ACTUAL lookup before comparing the projection's suspended
||| tableFor case with the observed table. No guessed callback or value.
export
0 pairedProjectOwnerTableObserved :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (ambient : world) ->
  (fibers : Registry name key value world error) -> (owner : name) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (lookupBinding {key = name} {value = FiberAt name key value world error}
    @{nameEq} owner fibers = observed) ->
  (effectTables (projectEffectState {name = name} {key = key} {value = value}
    {world = world} {error = error} @{nameEq} (MkSystemState ambient fibers)) owner =
    case observed of Nothing => emptyContext
                     Just fiber => ownedValues (fiberTable fiber))
pairedProjectOwnerTableObserved name key world error value nameEq ambient fibers owner
  Nothing observed = rewrite observed in Refl
pairedProjectOwnerTableObserved name key world error value nameEq ambient fibers owner
  (Just fiber) observed = rewrite observed in Refl

||| D1 supervisor-authorized cure: the eliminator consumes ONE NAMED TABLE,
||| with its equation to the actual projection. B13 is applied INSIDE the
||| observed-fiber branches, where its anonymous case has already reduced.
||| This re-derives B11's provenance; it does not retry B12's statement.
export
0 pairedNamedTableOwnerObserved :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (owner : name) -> (wanted : key) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (lookupBinding {key = name} {value = FiberAt name key value world error}
    @{nameEq} owner fibers = observed) ->
  (table : CoeffectContext key value) ->
  (effectTables (projectEffectState {name = name} {key = key} {value = value}
    {world = world} {error = error} @{nameEq} (MkSystemState ambient fibers)) owner = table) ->
  (provided : value wanted) ->
  (lookupBinding {key = key} {value = value} @{keyEq} wanted table = Just provided) ->
  (fiber : Fiber name key value world error **
    ((lookupFiber {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} owner fibers = Just fiber),
     Elem wanted (dependencies (componentProvisions (fiberComponent fiber)))))
pairedNamedTableOwnerObserved name key world error value nameEq keyEq ambient fibers
  owner wanted Nothing found table tableObserved provided present =
    void (nothingIsNotJust (trans (sym (cong
      (lookupBinding {key = key} {value = value} @{keyEq} wanted)
      (trans (sym tableObserved) (pairedProjectOwnerTableObserved name key world error
        value nameEq ambient fibers owner Nothing found)))) present))
pairedNamedTableOwnerObserved name key world error value nameEq keyEq ambient fibers
  owner wanted (Just (MkFiber component parent retiredFlag
    (MkOwnedTable (MkCoeffectContext entries unique) confined) lifecycle))
  found table tableObserved provided present =
    (MkFiber component parent retiredFlag
      (MkOwnedTable (MkCoeffectContext entries unique) confined) lifecycle **
      (found, confined wanted (lookupJustElem @{keyEq} wanted entries provided
        (trans (sym (cong (lookupBinding {key = key} {value = value} @{keyEq} wanted)
          (trans (sym tableObserved) (pairedProjectOwnerTableObserved name key world error
            value nameEq ambient fibers owner
            (Just (MkFiber component parent retiredFlag
              (MkOwnedTable (MkCoeffectContext entries unique) confined) lifecycle)) found))))
          present))))

||| D2 DISTINCT observed-table transport statement. Both actual lookup values,
||| named tables, table equations and yielded values are explicit; no anonymous
||| table case crosses this interface. This is not B12's global Boolean surface.
export
0 pairedNamedTableOwnersUnique :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (pairwiseProvisionInvariant {name = name} {key = key} {value = value}
    {world = world} {error = error} @{keyEq} (bindings fibers) = True) ->
  (leftOwner, rightOwner : name) -> (wanted : key) ->
  (leftObserved, rightObserved : Maybe (Fiber name key value world error)) ->
  (lookupBinding {key = name} {value = FiberAt name key value world error}
    @{nameEq} leftOwner fibers = leftObserved) ->
  (lookupBinding {key = name} {value = FiberAt name key value world error}
    @{nameEq} rightOwner fibers = rightObserved) ->
  (leftTable, rightTable : CoeffectContext key value) ->
  (effectTables (projectEffectState {name = name} {key = key} {value = value}
    {world = world} {error = error} @{nameEq} (MkSystemState ambient fibers)) leftOwner = leftTable) ->
  (effectTables (projectEffectState {name = name} {key = key} {value = value}
    {world = world} {error = error} @{nameEq} (MkSystemState ambient fibers)) rightOwner = rightTable) ->
  (leftValue, rightValue : value wanted) ->
  (lookupBinding {key = key} {value = value} @{keyEq} wanted leftTable = Just leftValue) ->
  (lookupBinding {key = key} {value = value} @{keyEq} wanted rightTable = Just rightValue) ->
  leftOwner = rightOwner
pairedNamedTableOwnersUnique name key world error value nameEq keyEq ambient
  (MkCoeffectContext entries unique) pairwise leftOwner rightOwner wanted leftObserved
  rightObserved leftLookup rightLookup leftTable rightTable leftTableObserved
  rightTableObserved leftValue rightValue leftPresent rightPresent =
    case (pairedNamedTableOwnerObserved name key world error value nameEq keyEq ambient
            (MkCoeffectContext entries unique) leftOwner wanted leftObserved leftLookup
            leftTable leftTableObserved leftValue leftPresent,
          pairedNamedTableOwnerObserved name key world error value nameEq keyEq ambient
            (MkCoeffectContext entries unique) rightOwner wanted rightObserved rightLookup
            rightTable rightTableObserved rightValue rightPresent) of
      ((leftFiber ** (leftFound, leftDeclares)),
       (rightFiber ** (rightFound, rightDeclares))) =>
        pairwiseSharedProvisionSameName keyEq entries pairwise leftOwner rightOwner
          leftFiber rightFiber
          (lookupEntryElemOpenAnchor nameEq leftOwner entries leftFiber leftFound)
          (lookupEntryElemOpenAnchor nameEq rightOwner entries rightFiber rightFound)
          wanted leftDeclares rightDeclares

||| Actual committed provider value versus actual effect projection. Observe
||| the registry lookup once; no availability or equality is assumed.
export
0 pairedProviderProjectionObserved :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (owner : name) -> (wanted : key) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (lookupBinding {key = name} {value = FiberAt name key value world error}
    @{nameEq} owner fibers = observed) ->
  (valueFromProvider {name = name} {key = key} {value = value} {world = world}
    {error = error} @{nameEq} @{keyEq} owner wanted fibers =
   lookupBinding {key = key} {value = value} @{keyEq} wanted
    (effectTables (projectEffectState {name = name} {key = key} {value = value}
      {world = world} {error = error} @{nameEq} (MkSystemState ambient fibers)) owner))
pairedProviderProjectionObserved name key world error value nameEq keyEq ambient fibers
  owner wanted Nothing found = rewrite found in Refl
pairedProviderProjectionObserved name key world error value nameEq keyEq ambient fibers
  owner wanted (Just fiber) found = rewrite found in Refl

||| Actual successful providerOf heads MUST be mapped at a paired runtime cut.
||| The right pairwise provision invariant and both owned-table witnesses are
||| enough; no all-actors Active/control-equivalence oracle is introduced.
export
0 pairedActualProviderHeads :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (renaming : NameBijection name) -> (wanted : key) ->
  (leftWorld, rightWorld : world) ->
  (leftRegistry, rightRegistry : Registry name key value world error) ->
  RenamedRuntimeEffects name key world value renaming
    (projectEffectState {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} (MkSystemState leftWorld leftRegistry))
    (projectEffectState {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} (MkSystemState rightWorld rightRegistry)) ->
  (pairwiseProvisionInvariant {name = name} {key = key} {value = value}
    {world = world} {error = error} @{keyEq} (bindings rightRegistry) = True) ->
  (leftOwner, rightOwner : name) ->
  (providerOf {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} @{keyEq} wanted leftRegistry = Just leftOwner) ->
  (providerOf {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} @{keyEq} wanted rightRegistry = Just rightOwner) ->
  renameForward renaming leftOwner = rightOwner
pairedActualProviderHeads name key world error value nameEq keyEq renaming wanted
  leftWorld rightWorld leftRegistry rightRegistry effects rightPairwise leftOwner
  rightOwner leftProvider rightProvider =
    case (isJustTrueWitness (valueFromProvider @{nameEq} @{keyEq} leftOwner wanted
            leftRegistry) (providerOfValue (providerOfSound nameEq keyEq wanted
              leftOwner leftRegistry leftProvider)),
          isJustTrueWitness (valueFromProvider @{nameEq} @{keyEq} rightOwner wanted
            rightRegistry) (providerOfValue (providerOfSound nameEq keyEq wanted
              rightOwner rightRegistry rightProvider))) of
      ((leftValue ** leftPresent), (rightValue ** rightPresent)) =>
        pairedNamedTableOwnersUnique name key world error value nameEq keyEq rightWorld
          rightRegistry rightPairwise (renameForward renaming leftOwner) rightOwner wanted
          (lookupBinding @{nameEq} (renameForward renaming leftOwner) rightRegistry)
          (lookupBinding @{nameEq} rightOwner rightRegistry) Refl Refl
          (effectTables (projectEffectState @{nameEq} (MkSystemState rightWorld rightRegistry))
            (renameForward renaming leftOwner))
          (effectTables (projectEffectState @{nameEq} (MkSystemState rightWorld rightRegistry))
            rightOwner) Refl Refl leftValue rightValue
          (trans (sym (synchronizationLookupBindings key value keyEq wanted
            (effectTables (projectEffectState @{nameEq} (MkSystemState leftWorld leftRegistry))
              leftOwner)
            (effectTables (projectEffectState @{nameEq} (MkSystemState rightWorld rightRegistry))
              (renameForward renaming leftOwner)) (synchronizedTables effects leftOwner)))
            (trans (sym (pairedProviderProjectionObserved name key world error value nameEq
              keyEq leftWorld leftRegistry leftOwner wanted
              (lookupBinding @{nameEq} leftOwner leftRegistry) Refl)) leftPresent))
          (trans (sym (pairedProviderProjectionObserved name key world error value nameEq
            keyEq rightWorld rightRegistry rightOwner wanted
            (lookupBinding @{nameEq} rightOwner rightRegistry) Refl)) rightPresent)
