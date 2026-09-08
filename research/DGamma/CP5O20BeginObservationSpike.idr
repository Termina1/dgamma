module DGamma.CP5O20BeginObservationSpike

import DGamma.Core
import DGamma.Unified
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressProgramBound
import DGamma.CP4DeletionSelectedForeignLifecycleBegin
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionFrames
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20EpisodeSynchronizationSpike
import DGamma.CP5O20PairedPrefixProducerSpike
import DGamma.CP5O20CanonicalPairSelectionSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| An ACTUAL Begin observation owns the exact component, original fiber,
||| successfully resolved dependency view and resulting Reloading state. It
||| never takes a desired resolver result or destination equation as an oracle.
public export
record O20BeginObservation
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (actor : name)
  (before, afterState : SystemState name key value world error) where
  constructor MkO20BeginObservation
  beginObservedComponent : Component key value world error
  beginObservedParent : Parent name
  beginObservedTable : OwnedTable key value (componentProvisions beginObservedComponent)
  beginObservedView : View name (dependencies (componentDependencies beginObservedComponent))
  0 beginObservedFound : (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before) =
    Just (MkFiber beginObservedComponent beginObservedParent False beginObservedTable (Inactive Nothing)))
  0 beginObservedResolved : (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies beginObservedComponent)) (registry before) = Just beginObservedView)
  0 beginObservedAfter : (MkSystemState (worldState before)
    (replaceBinding @{nameEq} actor (MkFiber beginObservedComponent beginObservedParent False beginObservedTable
      (Reloading (componentProgram beginObservedComponent) id beginObservedView)) (registry before)) = afterState)

||| Eliminate an explicit actual Begin plan once. Its concrete False-retired
||| fiber already owns a successful target, so the resolver success is a direct
||| constructor projection, not a neutral targetFiber transport obligation.
export
0 o20BeginObservationFromPlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (owner : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor source = Just owner) ->
  (afterState : SystemState name key value world error) ->
  ForeignBeginPlanView name key world error value nameEq keyEq actor ambient source owner LBeginTag afterState ->
  O20BeginObservation name key world error value nameEq keyEq actor (MkSystemState ambient source) afterState
o20BeginObservationFromPlan nameEq keyEq actor ambient source owner found afterState
  (MkForeignBeginPlanView {component} {parent} {table} view ownerShape targetFound tagShape afterShape) =
    MkO20BeginObservation component parent table view
      (trans found (cong Just ownerShape)) targetFound afterShape

||| Observe the actual owner lookup result explicitly before invoking the
||| public Begin-plan producer. No computed existential is locally eliminated.
export
0 o20BeginObservationAtOwner :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (afterState : SystemState name key value world error) ->
  (applyAction @{nameEq} @{keyEq} (LBegin actor) (MkSystemState ambient source) = Just (LBeginTag, afterState)) ->
  (observed : (owner : Fiber name key value world error **
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor source = Just owner))) ->
  O20BeginObservation name key world error value nameEq keyEq actor (MkSystemState ambient source) afterState
o20BeginObservationAtOwner nameEq keyEq actor ambient source afterState raw (owner ** found) =
  o20BeginObservationFromPlan nameEq keyEq actor ambient source owner found afterState
    (foreignBeginPlanView nameEq keyEq actor ambient source owner found LBeginTag afterState raw)

||| Actual BeginStep alone PRODUCES its component and successful resolver
||| observation. No caller-supplied dependency list/view is required.
export
0 o20ObserveActualBegin :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  BeginStep nameEq keyEq actor before afterState ->
  O20BeginObservation name key world error value nameEq keyEq actor before afterState
o20ObserveActualBegin nameEq keyEq actor (MkSystemState ambient source) afterState opening =
  o20BeginObservationAtOwner nameEq keyEq actor ambient source afterState
    (checkedActionProjects nameEq keyEq (LBegin actor) (MkSystemState ambient source)
      afterState LBeginTag (beginEquation opening))
    (lifecycleActorPresent nameEq keyEq (LBegin actor) (MkSystemState ambient source)
      afterState LBeginTag (checkedActionProjects nameEq keyEq (LBegin actor)
        (MkSystemState ambient source) afterState LBeginTag (beginEquation opening)) Refl)

||| Produce BOTH actual resolver observations at the authoritative selected
||| cuts. Each list is its actual component's dependencies; equating those
||| components and whole-prefix effects is still a separate synchronization debt.
export
0 o20ObserveSelectedBegins :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {protocol : RegistrationProtocol key value world error} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} -> {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq leftTrace} ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq rightTrace} ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol nameEq keyEq leftTrace rightTrace
    (expectedBridgeBijection sameInputs) (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  {operational : CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital matching} ->
  {selected : name} ->
  (pair : SelectedCanonicalBlockPair name key world error value protocol nameEq keyEq leftTrace rightTrace
    sameInputs leftCapital rightCapital matching operational selected) ->
  (O20BeginObservation name key world error value nameEq keyEq selected
    (blockPreStart (pairLeftBlock pair)) (blockStart (pairLeftBlock pair)),
   O20BeginObservation name key world error value nameEq keyEq
    (renameForward (expectedBridgeBijection sameInputs) selected)
    (blockPreStart (pairRightBlock pair)) (blockStart (pairRightBlock pair)))
o20ObserveSelectedBegins {sameInputs} {selected} nameEq keyEq pair =
  (o20ObserveActualBegin nameEq keyEq selected
    (blockPreStart (pairLeftBlock pair)) (blockStart (pairLeftBlock pair)) (blockOpening (pairLeftBlock pair)),
   o20ObserveActualBegin nameEq keyEq (renameForward (expectedBridgeBijection sameInputs) selected)
    (blockPreStart (pairRightBlock pair)) (blockStart (pairRightBlock pair)) (blockOpening (pairRightBlock pair)))

||| Project the actual Begin frame: its captured effect map is the identity,
||| so PartialDefined directly owns the real before/after effect relation.
export
0 o20BeginFrameProjection :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  ActualEffectFrame nameEq keyEq (LBegin actor) LBeginTag before afterState ->
  EffectStateRelated keyEq
    (projectEffectState {name} {key} {value} {world} {error} @{nameEq} before)
    (projectEffectState {name} {key} {value} {world} {error} @{nameEq} afterState)
o20BeginFrameProjection nameEq keyEq actor before afterState
  (MkActualEffectFrame (PartialDefined related)) = related

||| Advance a real paired-prefix EFFECT hypothesis through the two actual
||| Begin executions. Both one-sided frames are produced from checked actions,
||| not supplied endpoint relations. Program-step synchronization is separate.
export
0 o20PairedBeginEffects :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (renaming : NameBijection name) -> (leftActor, rightActor : name) ->
  (leftBefore, leftAfter, rightBefore, rightAfter : SystemState name key value world error) ->
  BeginStep nameEq keyEq leftActor leftBefore leftAfter ->
  BeginStep nameEq keyEq rightActor rightBefore rightAfter ->
  RenamedRuntimeEffects name key world value renaming
    (projectEffectState {name} {key} {value} {world} {error} @{nameEq} leftBefore)
    (projectEffectState {name} {key} {value} {world} {error} @{nameEq} rightBefore) ->
  RenamedRuntimeEffects name key world value renaming
    (projectEffectState {name} {key} {value} {world} {error} @{nameEq} leftAfter)
    (projectEffectState {name} {key} {value} {world} {error} @{nameEq} rightAfter)
o20PairedBeginEffects {name} {key} {world} {error} {value} nameEq keyEq renaming
  leftActor rightActor leftBefore leftAfter rightBefore rightAfter leftOpening rightOpening effects =
    pairedEffectsAcrossFrames name key world value keyEq renaming
      (projectEffectState @{nameEq} leftBefore) (projectEffectState @{nameEq} leftAfter)
      (projectEffectState @{nameEq} rightBefore) (projectEffectState @{nameEq} rightAfter)
      (o20BeginFrameProjection nameEq keyEq leftActor leftBefore leftAfter
        (actualTransitionEffectFrame nameEq keyEq (LBegin leftActor) LBeginTag leftBefore leftAfter
          (beginEquation leftOpening))) effects
      (o20BeginFrameProjection nameEq keyEq rightActor rightBefore rightAfter
        (actualTransitionEffectFrame nameEq keyEq (LBegin rightActor) LBeginTag rightBefore rightAfter
          (beginEquation rightOpening)))

||| Actual authoritative paired-opening effect successor under the FIXED
||| accepted bijection. This consumes only the internal pre-cut effect invariant
||| and derives the post-cut invariant from the two actual Begin equations.
||| It does NOT derive that pre-cut invariant from entire canonical executions.
export
0 o20SelectedBeginEffects :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {protocol : RegistrationProtocol key value world error} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} -> {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq leftTrace} ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq rightTrace} ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol nameEq keyEq leftTrace rightTrace
    (expectedBridgeBijection sameInputs) (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  {operational : CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital matching} ->
  {selected : name} ->
  (pair : SelectedCanonicalBlockPair name key world error value protocol nameEq keyEq leftTrace rightTrace
    sameInputs leftCapital rightCapital matching operational selected) ->
  RenamedRuntimeEffects name key world value (expectedBridgeBijection sameInputs)
    (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (blockPreStart (pairLeftBlock pair)))
    (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (blockPreStart (pairRightBlock pair))) ->
  RenamedRuntimeEffects name key world value (expectedBridgeBijection sameInputs)
    (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (blockStart (pairLeftBlock pair)))
    (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (blockStart (pairRightBlock pair)))
o20SelectedBeginEffects {sameInputs} {selected} nameEq keyEq pair effects =
  o20PairedBeginEffects nameEq keyEq (expectedBridgeBijection sameInputs) selected
    (renameForward (expectedBridgeBijection sameInputs) selected)
    (blockPreStart (pairLeftBlock pair)) (blockStart (pairLeftBlock pair))
    (blockPreStart (pairRightBlock pair)) (blockStart (pairRightBlock pair))
    (blockOpening (pairLeftBlock pair)) (blockOpening (pairRightBlock pair)) effects
