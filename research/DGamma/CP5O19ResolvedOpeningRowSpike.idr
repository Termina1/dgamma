module DGamma.CP5O19ResolvedOpeningRowSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP3StatementChecks
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19ActivationRowSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5UniqueRawNameInsertions
import Data.Nat
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19OpeningPropagationSpike
import DGamma.CP5O19InsertObservationSpike
import DGamma.CP5O20BeginObservationSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Reconstruct Begin from an EXPLICIT clean component and resolved view.
||| The goal contains only actual lookup/resolveView observations, never an
||| arbitrary targetFiber transport. Preservation supplies the checked domain.
export
0 o19BeginAtResolvedView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (resolved : View name (dependencies (componentDependencies component))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor source =
    Just (MkFiber component parent False table (Inactive Nothing))) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies component)) source = Just resolved) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (MkSystemState ambient source) = True) ->
  CheckedEarlyApplication name key world error value nameEq keyEq
    (MkSystemState ambient source) (LBegin actor) LBeginTag
o19BeginAtResolvedView nameEq keyEq actor ambient source component parent table
  resolved found resolution wellFormed =
    o19CheckObservedRawMove nameEq keyEq (LBegin actor) LBeginTag
      (MkSystemState ambient source) wellFormed
      (MkRawActivationMove
        (MkSystemState ambient (replaceBinding @{nameEq} actor
          (MkFiber component parent False table
            (Reloading (componentProgram component) id resolved)) source))
        (rewrite found in rewrite resolution in Refl))

||| Per-cut insertion guard with the resolved value/equations EXPLICIT.
||| Eliminate only the actual insertion plan. The owner remains the concrete
||| clean fiber observed at the initial Begin; no targetFiber goal arises.
export
0 o19BeginAfterObservedInsertion :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor, child : name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (opened, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (initial : O20BeginObservation name key world error value nameEq keyEq actor
    (MkSystemState ambient source) opened) ->
  (resolution : O19ResolutionObservation name key world error value nameEq keyEq
    (dependencies (componentDependencies (beginObservedComponent initial))) source (registry afterState)) ->
  Not (actor = child) ->
  ForeignInsertPlanView name key world error value nameEq keyEq child parent component
    ambient source tag afterState ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} afterState = True) ->
  CheckedEarlyApplication name key world error value nameEq keyEq afterState (LBegin actor) LBeginTag
o19BeginAfterObservedInsertion nameEq keyEq actor child parent component ambient source
  opened _ _ initial resolution distinct (MkForeignInsertPlanView absent guards) wellFormed =
    o19BeginAtResolvedView nameEq keyEq actor ambient
      (insertBinding @{nameEq} child (freshFiber component parent) source absent)
      (beginObservedComponent initial) (beginObservedParent initial) (beginObservedTable initial)
      (beginObservedView initial)
      (trans (lookupInsertOther @{nameEq} actor child distinct (freshFiber component parent) source absent)
        (beginObservedFound initial))
      (trans (resolutionAfter resolution)
        (trans (sym (resolutionBefore resolution)) (beginObservedResolved initial))) wellFormed

||| Use the SAME checked insertion for its plan and preservation, keeping the
||| resolver observation explicit at the per-cut boundary.
export
0 o19BeginAfterCheckedObservedInsertion :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor, child : name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  (before, opened, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (initial : O20BeginObservation name key world error value nameEq keyEq actor before opened) ->
  (resolution : O19ResolutionObservation name key world error value nameEq keyEq
    (dependencies (componentDependencies (beginObservedComponent initial)))
    (registry before) (registry afterState)) ->
  Not (actor = child) ->
  (checkedApplyAction @{nameEq} @{keyEq} (OInsert child parent component) before = Just (tag, afterState)) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} before = True) ->
  CheckedEarlyApplication name key world error value nameEq keyEq afterState (LBegin actor) LBeginTag
o19BeginAfterCheckedObservedInsertion nameEq keyEq actor child parent component
  (MkSystemState ambient source) opened afterState tag initial resolution distinct checked wellFormed =
    o19BeginAfterObservedInsertion nameEq keyEq actor child parent component ambient source
      opened afterState tag initial resolution distinct
      (foreignInsertPlanView nameEq keyEq child parent component ambient source tag afterState
        (checkedActionProjects nameEq keyEq (OInsert child parent component)
          (MkSystemState ambient source) afterState tag checked))
      (preservationTheoremProof nameEq keyEq (OInsert child parent component)
        (MkSystemState ambient source) afterState tag wellFormed
        (checkedActionProjects nameEq keyEq (OInsert child parent component)
          (MkSystemState ambient source) afterState tag checked))

||| Explicit observation spine for an O/A Begin row. Each cut owns the actual
||| insertion, its resolved value/equations and the child/licensing exclusions.
||| No checked Begin guard is stored for any intermediate cut.
public export
data O19ObservedInsertions :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (deps : List key) ->
  {before, finalState : SystemState name key value world error} ->
  Transitions before finalState -> Type where
  ObservedInsertionsEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} -> {actor : name} -> {deps : List key} ->
    {before : SystemState name key value world error} ->
    O19ObservedInsertions name key world error value nameEq keyEq actor deps (NoTransitions {state = before})
  ObservedInsertionsStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} -> {actor : name} -> {deps : List key} ->
    {before, middle, finalState : SystemState name key value world error} ->
    (child : name) -> (parent : Parent name) -> (component : Component key value world error) ->
    (tag : RuleTag) ->
    (0 checked : checkedApplyAction @{nameEq} @{keyEq} (OInsert child parent component) before = Just (tag, middle)) ->
    (rest : Transitions middle finalState) ->
    (0 childSafe : Not (actor = child)) ->
    (0 parentSafe : (licensor : name) -> (parent = ChildOf licensor) -> Not (actor = licensor)) ->
    (0 resolution : O19ResolutionObservation name key world error value nameEq keyEq deps
      (registry before) (registry middle)) ->
    (0 remaining : O19ObservedInsertions name key world error value nameEq keyEq actor deps rest) ->
    O19ObservedInsertions name key world error value nameEq keyEq actor deps
      (MoreTransitions (Fired {before} {afterState = middle} nameEq keyEq
        (OInsert child parent component) tag checked) rest)


||| State-observed adapter, retaining the EXPLICIT clean fiber and target.
export
0 o19BeginAtResolvedState :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before : SystemState name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (resolved : View name (dependencies (componentDependencies component))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before) =
    Just (MkFiber component parent False table (Inactive Nothing))) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies component)) (registry before) = Just resolved) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    before = True) ->
  CheckedEarlyApplication name key world error value nameEq keyEq
    before (LBegin actor) LBeginTag
o19BeginAtResolvedState nameEq keyEq actor (MkSystemState ambient source) component parent
  table resolved found resolution wellFormed =
    o19BeginAtResolvedView nameEq keyEq actor ambient source component parent table
      resolved found resolution wellFormed

||| Derive EVERY cut guard across arbitrarily many observed insertions. The
||| SAME explicit component/table/view are threaded recursively; actual local
||| updates preserve the lookup, observed equations preserve resolution, and
||| preservation supplies each reached domain. No targetFiber is mentioned.
export
0 o19OpeningAlongObservedInsertions :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (resolved : View name (dependencies (componentDependencies component))) ->
  {before, finalState : SystemState name key value world error} ->
  (spine : Transitions before finalState) ->
  O19ObservedInsertions name key world error value nameEq keyEq actor
    (dependencies (componentDependencies component)) spine ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before) =
    Just (MkFiber component parent False table (Inactive Nothing))) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies component)) (registry before) = Just resolved) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} before = True) ->
  O19EarlyAlong name key world error value nameEq keyEq (LBegin actor) LBeginTag spine
o19OpeningAlongObservedInsertions {before} nameEq keyEq actor component parent table resolved
  _ ObservedInsertionsEnd found resolution wellFormed =
    EarlyAlongEnd (o19BeginAtResolvedState nameEq keyEq actor before component parent table
      resolved found resolution wellFormed)
o19OpeningAlongObservedInsertions {before} nameEq keyEq actor component parent table resolved
  _ (ObservedInsertionsStep {middle} child childParent childComponent tag checked rest
    childSafe parentSafe observed remaining) found resolution wellFormed =
    EarlyAlongStep (Fired {before} {afterState = middle} nameEq keyEq
      (OInsert child childParent childComponent) tag checked) rest
      (o19BeginAtResolvedState nameEq keyEq actor before component parent table
        resolved found resolution wellFormed)
      (o19OpeningAlongObservedInsertions nameEq keyEq actor component parent table resolved rest remaining
        (trans (systemLocalUpdateForeign nameEq actor child childSafe before middle
          (applyActionLocalUpdate nameEq keyEq (OInsert child childParent childComponent) before middle tag
            (checkedActionProjects nameEq keyEq (OInsert child childParent childComponent) before middle tag checked))) found)
        (trans (resolutionAfter observed) (trans (sym (resolutionBefore observed)) resolution))
        (preservationTheoremProof nameEq keyEq (OInsert child childParent childComponent) before middle tag wellFormed
          (checkedActionProjects nameEq keyEq (OInsert child childParent childComponent) before middle tag checked)))


||| External correspondence from the SAME O/A diamond. Root inserts match
||| exactly; generated inserts and activation nodes are proved internal.
export
0 o19InsertActivationExternal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (child : name) -> (parent : Parent name) -> (component : Component key value world error) ->
  {first, middle, last : SystemState name key value world error} ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  (transitionAction left = OInsert child parent component) -> PaperActivationStep right ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  SameExternalOrchestration nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions (movedRight diamond) (MoreTransitions (movedLeft diamond) NoTransitions))
o19InsertActivationExternal nameEq keyEq child Root component left right inserted activation diamond =
  SkipRightInternal (movedRight diamond) (MoreTransitions (movedLeft diamond) NoTransitions)
    (o19ActivationInternal nameEq (movedRight diamond) (movedRightActivationBranch diamond activation))
    (MatchExternalInput (OInsert child Root component) left (MoreTransitions right NoTransitions)
      (RootInsertStep inserted) (movedLeft diamond) NoTransitions
      (RootInsertStep (trans (movedLeftAction diamond) inserted))
      inserted (trans (movedLeftAction diamond) inserted)
      (SkipLeftInternal right NoTransitions (o19ActivationInternal nameEq right activation)
        SameExternalOrchestrationEnd))
o19InsertActivationExternal nameEq keyEq child (ChildOf parent) component left right inserted activation diamond =
  SkipLeftInternal left (MoreTransitions right NoTransitions) (childInsertCannotBeRoot left inserted)
    (SkipLeftInternal right NoTransitions (o19ActivationInternal nameEq right activation)
      (SkipRightInternal (movedRight diamond) (MoreTransitions (movedLeft diamond) NoTransitions)
        (o19ActivationInternal nameEq (movedRight diamond) (movedRightActivationBranch diamond activation))
        (SkipRightInternal (movedLeft diamond) NoTransitions
          (childInsertCannotBeRoot (movedLeft diamond) (trans (movedLeftAction diamond) inserted))
          SameExternalOrchestrationEnd)))

||| Constructor injectivity for the named insertion parent, independent of
||| any computed row. Used to discharge the exact diamond licensing clause.
export
0 o19InsertParentInjective :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (firstChild, secondChild : name) -> (firstParent, secondParent : Parent name) ->
  (firstComponent, secondComponent : Component key value world error) ->
  (OInsert firstChild firstParent firstComponent = OInsert secondChild secondParent secondComponent) ->
  (firstParent = secondParent)
o19InsertParentInjective _ _ _ _ _ _ Refl = Refl

||| Actual O/A diamond from the source bundle and derived early guard. Both
||| insertion exclusions are transported from the named child and parent.
export
0 o19InsertActivationDiamond :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (child : name) -> (parent : Parent name) -> (component : Component key value world error) ->
  {initial, first, middle, last, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) -> (earlier : Transitions initial first) ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  (later : Transitions last finalState) ->
  (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)) = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  (transitionAction left = OInsert child parent component) -> PaperActivationStep right ->
  Not (transitionActor right = child) ->
  ((licensor : name) -> (parent = ChildOf licensor) -> Not (transitionActor right = licensor)) ->
  CheckedEarlyApplication name key world error value nameEq keyEq first
    (transitionAction right) (transitionTag right) ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
o19InsertActivationDiamond {first} nameEq keyEq protocol child parent component
  source earlier left right later decomposition premises inserted activation childSafe parentSafe early =
    orchestrationActivationDiamondSpike nameEq keyEq left right
      (Fired {before = first} {afterState = earlyApplicationFinal early} nameEq keyEq
        (transitionAction right) (transitionTag right) (earlyApplicationChecked early))
      (Builtin.fst (o19SourcePairFacts nameEq keyEq protocol source earlier left right later decomposition premises))
      (AlignedStep (transitionAction right) (transitionTag right) (earlyApplicationChecked early) NoTransitions AlignedEnd)
      Refl Refl (PaperInsertStep inserted) activation
      (\same => childSafe (trans (sym same)
        (trans (o19TransitionActorOwner left) (cong actionOwner inserted))))
      (\otherChild, otherParent, otherComponent, same, collision =>
        childSafe (trans collision (sym (cong actionOwner (trans (sym inserted) same)))))
      (\otherChild, licensor, otherComponent, same => parentSafe licensor
        (o19InsertParentInjective child otherChild parent (ChildOf licensor) component otherComponent
          (trans (sym inserted) same)))
      (Builtin.fst (Builtin.snd (o19SourcePairFacts nameEq keyEq protocol source earlier left right later decomposition premises)))
      (Builtin.snd (Builtin.snd (o19SourcePairFacts nameEq keyEq protocol source earlier left right later decomposition premises)))


||| Consume the FROZEN suffix producer for this same actual O/A diamond.
export
0 o19InsertActivationReplay :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (child : name) -> (parent : Parent name) -> (component : Component key value world error) ->
  {initial, first, middle, last, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) -> (earlier : Transitions initial first) ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  (later : Transitions last finalState) ->
  (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)) = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  (transitionAction left = OInsert child parent component) -> PaperActivationStep right ->
  Not (transitionActor right = child) ->
  ((licensor : name) -> (parent = ChildOf licensor) -> Not (transitionActor right = licensor)) ->
  CheckedEarlyApplication name key world error value nameEq keyEq first
    (transitionAction right) (transitionTag right) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right **
   AdjacentSwapResult name key world error value protocol nameEq keyEq source earlier left right later diamond)
o19InsertActivationReplay nameEq keyEq protocol child parent component
  source earlier left right later decomposition premises inserted activation childSafe parentSafe early =
    (o19InsertActivationDiamond nameEq keyEq protocol child parent component source earlier left right later
       decomposition premises inserted activation childSafe parentSafe early **
     adjacentSwapSuffixSpike nameEq keyEq protocol source earlier left right later decomposition premises
       (o19InsertActivationDiamond nameEq keyEq protocol child parent component source earlier left right later
         decomposition premises inserted activation childSafe parentSafe early)
       (o19InsertActivationExternal nameEq keyEq child parent component left right inserted activation
         (o19InsertActivationDiamond nameEq keyEq protocol child parent component source earlier left right later
           decomposition premises inserted activation childSafe parentSafe early)))


||| Simultaneous reached cursor/bundle/uniqueness/derivation/count at the
||| explicit produced O/A boundary. No computed existential is eliminated.
export
0 o19OrchestrationRowStepObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, sourceFinal, before, middle, rightBefore, rightAfter : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) -> (earlier : Transitions initial before) ->
  (left : Transition before middle) -> (sourceRight : Transition rightBefore rightAfter) ->
  (crossings : Nat) ->
  (previous : O19ActivationRow name key world error value protocol nameEq keyEq source
    (appendTransitions earlier (MoreTransitions left NoTransitions)) sourceRight crossings) ->
  (leftOrchestration : PaperOrchestrationStep left) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left (rowRight previous) **
    AdjacentSwapResult name key world error value protocol nameEq keyEq
      (cursorTrace (rowCursor previous)) earlier left (rowRight previous) (rowRest previous) diamond) ->
  O19ActivationRow name key world error value protocol nameEq keyEq source earlier sourceRight (S crossings)
o19OrchestrationRowStepObserved {name} {key} {world} {error} {value}
  nameEq keyEq protocol source earlier left sourceRight crossings previous
  leftOrchestration (diamond ** result) =
    MkO19ActivationRow
      (MkO19ReachedCursor (replayedFinal result) (swappedTrace result) (swappedPremises result)
        (uniqueInsertionsAfterFiniteDerivation name key world error value protocol nameEq keyEq
          (FiniteAdjacentSwapStep (cursorTrace (rowCursor previous)) earlier left
          (rowRight previous) (rowRest previous)
          (AdjacentOrchestrationActivation left (rowRight previous) leftOrchestration (rowActivation previous))
          diamond result (swappedTrace result) FiniteAdjacentSwapDone) (cursorUnique (rowCursor previous)))
        (o19AppendFinite (cursorDerivation (rowCursor previous)) (FiniteAdjacentSwapStep (cursorTrace (rowCursor previous)) earlier left
          (rowRight previous) (rowRest previous)
          (AdjacentOrchestrationActivation left (rowRight previous) leftOrchestration (rowActivation previous))
          diamond result (swappedTrace result) FiniteAdjacentSwapDone)))
      (swappedMiddle diamond) (movedRight diamond)
      (MoreTransitions (movedLeft diamond) (replayedSuffix result))
      (sym (swappedDecomposition result))
      (trans (movedRightAction diamond) (rowAction previous))
      (trans (movedRightTag diamond) (rowTag previous))
      (trans (o19TransitionActorOwner (movedRight diamond))
        (trans (cong actionOwner (trans (movedRightAction diamond) (rowAction previous)))
          (sym (o19TransitionActorOwner sourceRight))))
      (movedRightActivationBranch diamond (rowActivation previous))
      (trans (o19AppendFiniteCount (cursorDerivation (rowCursor previous)) (FiniteAdjacentSwapStep (cursorTrace (rowCursor previous)) earlier left
          (rowRight previous) (rowRest previous)
          (AdjacentOrchestrationActivation left (rowRight previous) leftOrchestration (rowActivation previous))
          diamond result (swappedTrace result) FiniteAdjacentSwapDone))
        (trans (cong (\count => count + 1) (rowNodeCount previous))
          (plusCommutative crossings 1)))


||| Produce the next actual insertion crossing at the observed row cut.
export
0 o19InsertionRowStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (child : name) -> (parent : Parent name) -> (component : Component key value world error) ->
  {initial, sourceFinal, before, middle, rightBefore, rightAfter : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) -> (earlier : Transitions initial before) ->
  (left : Transition before middle) -> (sourceRight : Transition rightBefore rightAfter) ->
  (crossings : Nat) ->
  (previous : O19ActivationRow name key world error value protocol nameEq keyEq source
    (appendTransitions earlier (MoreTransitions left NoTransitions)) sourceRight crossings) ->
  (transitionAction left = OInsert child parent component) ->
  Not (transitionActor sourceRight = child) ->
  ((licensor : name) -> (parent = ChildOf licensor) -> Not (transitionActor sourceRight = licensor)) ->
  CheckedEarlyApplication name key world error value nameEq keyEq before
    (transitionAction sourceRight) (transitionTag sourceRight) ->
  O19ActivationRow name key world error value protocol nameEq keyEq source earlier sourceRight (S crossings)
o19InsertionRowStep nameEq keyEq protocol child parent component source earlier left sourceRight
  crossings previous inserted childSafe parentSafe early =
    o19OrchestrationRowStepObserved nameEq keyEq protocol source earlier left sourceRight
      crossings previous (PaperInsertStep inserted)
      (o19InsertActivationReplay nameEq keyEq protocol child parent component
        (cursorTrace (rowCursor previous)) earlier left (rowRight previous) (rowRest previous)
        (trans (sym (appendTransitionsAssociative earlier (MoreTransitions left NoTransitions)
          (MoreTransitions (rowRight previous) (rowRest previous)))) (rowDecomposition previous))
        (cursorBundle (rowCursor previous)) inserted (rowActivation previous)
        (\same => childSafe (trans (sym (rowActor previous)) same))
        (\licensor, sameParent, sameActor => parentSafe licensor sameParent
          (trans (sym (rowActor previous)) sameActor))
        (o19EarlyLabels nameEq keyEq (transitionAction sourceRight) (transitionAction (rowRight previous))
          (transitionTag sourceRight) (transitionTag (rowRight previous))
          (rowAction previous) (rowTag previous) early))

||| Arbitrary-length O/A BEGIN row with EXPLICIT resolved target and observed
||| insertion spine. One recursion simultaneously derives cut applicability,
||| crossings, sealed replay bundles, uniqueness, finite derivation and count.
||| This is an insertion/Begin row, not yet a full mixed-block Cartesian proof.
export
0 o19BubbleResolvedInsertionRow :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) -> (actor : name) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (resolved : View name (dependencies (componentDependencies component))) ->
  {initial, sourceFinal, before, rightBefore, rightAfter : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) -> (earlier : Transitions initial before) ->
  (spine : Transitions before rightBefore) ->
  (opening : BeginStep nameEq keyEq actor rightBefore rightAfter) ->
  (later : Transitions rightAfter sourceFinal) ->
  (appendTransitions earlier (appendTransitions spine (MoreTransitions (beginTransition opening) later)) = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  (0 unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (observations : O19ObservedInsertions name key world error value nameEq keyEq actor
    (dependencies (componentDependencies component)) spine) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before) =
    Just (MkFiber component parent False table (Inactive Nothing))) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies component)) (registry before) = Just resolved) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} before = True) ->
  O19ActivationRow name key world error value protocol nameEq keyEq source earlier
    (beginTransition opening) (transitionCount spine)
o19BubbleResolvedInsertionRow nameEq keyEq protocol actor component parent table resolved
  source earlier _ opening later decomposition premises unique ObservedInsertionsEnd found resolution wellFormed =
    o19ActivationRowZero nameEq keyEq protocol source earlier (beginTransition opening) later
      decomposition premises unique (PaperBeginStep Refl Refl)
o19BubbleResolvedInsertionRow {before} nameEq keyEq protocol actor component parent table resolved
  source earlier _ opening later decomposition premises unique
  (ObservedInsertionsStep {middle} child childParent childComponent tag checked rest childSafe parentSafe observed remaining)
  found resolution wellFormed =
    o19InsertionRowStep nameEq keyEq protocol child childParent childComponent source earlier
      (Fired {before} {afterState = middle} nameEq keyEq (OInsert child childParent childComponent) tag checked)
      (beginTransition opening) (transitionCount rest)
      (o19BubbleResolvedInsertionRow nameEq keyEq protocol actor component parent table resolved source
        (appendTransitions earlier (MoreTransitions
          (Fired {before} {afterState = middle} nameEq keyEq (OInsert child childParent childComponent) tag checked) NoTransitions))
        rest opening later
        (trans (appendTransitionsAssociative earlier (MoreTransitions
          (Fired {before} {afterState = middle} nameEq keyEq (OInsert child childParent childComponent) tag checked) NoTransitions)
          (appendTransitions rest (MoreTransitions (beginTransition opening) later))) decomposition)
        premises unique remaining
        (trans (systemLocalUpdateForeign nameEq actor child childSafe before middle
          (applyActionLocalUpdate nameEq keyEq (OInsert child childParent childComponent) before middle tag
            (checkedActionProjects nameEq keyEq (OInsert child childParent childComponent) before middle tag checked))) found)
        (trans (resolutionAfter observed) (trans (sym (resolutionBefore observed)) resolution))
        (preservationTheoremProof nameEq keyEq (OInsert child childParent childComponent) before middle tag wellFormed
          (checkedActionProjects nameEq keyEq (OInsert child childParent childComponent) before middle tag checked)))
      Refl childSafe parentSafe
      (o19BeginAtResolvedState nameEq keyEq actor before component parent table resolved found resolution wellFormed)


||| Initial-guard specialization with the actual Begin observation EXPLICIT.
||| Source-prefix well-formedness is derived from the same full replay bundle.
export
0 o19BubbleObservedBeginRow :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) -> (actor : name) ->
  {initial, sourceFinal, before, rightBefore, rightAfter : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) -> (earlier : Transitions initial before) ->
  (spine : Transitions before rightBefore) -> (opening : BeginStep nameEq keyEq actor rightBefore rightAfter) ->
  (later : Transitions rightAfter sourceFinal) ->
  (appendTransitions earlier (appendTransitions spine (MoreTransitions (beginTransition opening) later)) = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  (0 unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (early : CheckedEarlyApplication name key world error value nameEq keyEq before (LBegin actor) LBeginTag) ->
  (initialObservation : O20BeginObservation name key world error value nameEq keyEq actor before
    (earlyApplicationFinal early)) ->
  (observations : O19ObservedInsertions name key world error value nameEq keyEq actor
    (dependencies (componentDependencies (beginObservedComponent initialObservation))) spine) ->
  O19ActivationRow name key world error value protocol nameEq keyEq source earlier
    (beginTransition opening) (transitionCount spine)
o19BubbleObservedBeginRow {name} {key} {world} {error} {value}
  nameEq keyEq protocol actor source earlier spine opening later decomposition premises unique
  early initialObservation observations =
    o19BubbleResolvedInsertionRow nameEq keyEq protocol actor
      (beginObservedComponent initialObservation) (beginObservedParent initialObservation)
      (beginObservedTable initialObservation) (beginObservedView initialObservation)
      source earlier spine opening later decomposition premises unique observations
      (beginObservedFound initialObservation) (beginObservedResolved initialObservation)
      (alignedTraceWellFormedEnd nameEq keyEq earlier
        (Builtin.fst (alignedAppendSplit earlier
          (appendTransitions spine (MoreTransitions (beginTransition opening) later))
          (replace {p = AlignedTransitions name key world error value nameEq keyEq}
            (sym decomposition) (replayAligned premises))))
        (replayInitialWellFormed premises))

||| Producer-owned observation constructor: obtain the exact resolver record
||| from the ACTUAL checked OInsert. Callers provide no resolver equations.
export
0 o19ObserveInsertionCons :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) -> (deps : List key) ->
  {before, middle, finalState : SystemState name key value world error} ->
  (child : name) -> (parent : Parent name) -> (component : Component key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (OInsert child parent component) before = Just (tag, middle)) ->
  (rest : Transitions middle finalState) ->
  Not (actor = child) ->
  ((licensor : name) -> (parent = ChildOf licensor) -> Not (actor = licensor)) ->
  O19ObservedInsertions name key world error value nameEq keyEq actor deps rest ->
  O19ObservedInsertions name key world error value nameEq keyEq actor deps
    (MoreTransitions (Fired {before} {afterState = middle} nameEq keyEq
      (OInsert child parent component) tag checked) rest)
o19ObserveInsertionCons {before} {middle} nameEq keyEq actor deps child parent component tag checked
  rest childSafe parentSafe remaining =
    ObservedInsertionsStep child parent component tag checked rest childSafe parentSafe
      (o19ResolutionAfterCheckedInsert nameEq keyEq deps child parent component before middle tag checked) remaining
