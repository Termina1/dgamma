module DGamma.CP5O20CanonicalBlockComponentSpike

import DGamma.CP5O20BeginObservationSpike
import DGamma.CP5O20SharedBeginAdapterSpike
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O20SupportedReferenceSpike
import DGamma.CP5O20CanonicalPairSelectionSpike
import DGamma.CP5O20OwnCutSafetySpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| The components at both selected ACTUAL opening cuts agree, from original
||| supported metadata and the two authentic replay origins. The two fibers
||| and primitive lookup equations are explicit observations. No pre-cut
||| effects/control relation or component-equality premise is assumed.
export
0 o20SelectedOpeningComponents :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace} ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace} ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  {operational : CertifiedOperationalCanonicalPermutation name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital matching} ->
  (execution : PermutedCanonicalExecution name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital operational) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  {selected : name} ->
  (pair : SelectedCanonicalBlockPair name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital matching operational selected) ->
  (leftFiber, rightFiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry (blockPreStart (pairLeftBlock pair))) = Just leftFiber) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward (expectedBridgeBijection sameInputs) selected) (registry (blockPreStart (pairRightBlock pair))) = Just rightFiber) ->
  (fiberComponent leftFiber = fiberComponent rightFiber)
o20SelectedOpeningComponents {nameEq} {keyEq} {protocol} {leftTrace} {rightTrace}
  {sameInputs} {leftCapital} {rightCapital} {operational} {selected}
  execution leftUnique rightUnique pair leftFiber rightFiber leftFound rightFound =
    trans (o20ReplayCutReferenceComponent nameEq keyEq protocol leftTrace leftCapital leftUnique
      (operationalTargetTrace operational) (operationalTargetPremises operational)
      (permutationOccurrenceCorrespondence execution)
      (traceBeforeBlock (pairLeftBlock pair))
      (MoreTransitions (beginTransition (blockOpening (pairLeftBlock pair)))
        (appendTransitions (blockBody (pairLeftBlock pair)) (traceAfterBlock (pairLeftBlock pair))))
      (blockDecomposition (pairLeftBlock pair)) selected
      (presentFiber (o20OriginalSupportedLookup nameEq keyEq protocol leftTrace leftCapital selected (pairSelectedSupported pair))) leftFiber
      (presentFound (o20OriginalSupportedLookup nameEq keyEq protocol leftTrace leftCapital selected (pairSelectedSupported pair))) leftFound)
      (sym (trans (o20ReplayCutReferenceComponent nameEq keyEq protocol rightTrace rightCapital rightUnique
      (canonicalTrace (canonicalSchedule rightCapital)) (canonicalReplayPremises rightCapital)
      (identityActionRegistrationReplayCorrespondence (canonicalTrace (canonicalSchedule rightCapital)))
      (traceBeforeBlock (pairRightBlock pair))
      (MoreTransitions (beginTransition (blockOpening (pairRightBlock pair)))
        (appendTransitions (blockBody (pairRightBlock pair)) (traceAfterBlock (pairRightBlock pair))))
      (blockDecomposition (pairRightBlock pair)) (renameForward (expectedBridgeBijection sameInputs) selected)
      (imageFiber (o20OriginalSupportedImageForward nameEq keyEq protocol leftTrace rightTrace sameInputs leftCapital rightCapital leftUnique rightUnique selected (presentFiber (o20OriginalSupportedLookup nameEq keyEq protocol leftTrace leftCapital selected (pairSelectedSupported pair))) (presentFound (o20OriginalSupportedLookup nameEq keyEq protocol leftTrace leftCapital selected (pairSelectedSupported pair))) (pairSelectedSupported pair))) rightFiber
      (imageFound (o20OriginalSupportedImageForward nameEq keyEq protocol leftTrace rightTrace sameInputs leftCapital rightCapital leftUnique rightUnique selected (presentFiber (o20OriginalSupportedLookup nameEq keyEq protocol leftTrace leftCapital selected (pairSelectedSupported pair))) (presentFound (o20OriginalSupportedLookup nameEq keyEq protocol leftTrace leftCapital selected (pairSelectedSupported pair))) (pairSelectedSupported pair))) rightFound)
        (imageComponent (o20OriginalSupportedImageForward nameEq keyEq protocol leftTrace rightTrace sameInputs leftCapital rightCapital leftUnique rightUnique selected (presentFiber (o20OriginalSupportedLookup nameEq keyEq protocol leftTrace leftCapital selected (pairSelectedSupported pair))) (presentFound (o20OriginalSupportedLookup nameEq keyEq protocol leftTrace leftCapital selected (pairSelectedSupported pair))) (pairSelectedSupported pair)))))

||| Open just the RIGHT actual Begin observation, with left component-indexed
||| values explicit. Native original/replay metadata produces component
||| equality at this value boundary; the shared packet retains BOTH actual
||| views and endpoint equations, without an all-name pre-cut premise.
export
0 o20ShareCanonicalBeginRight :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace} ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace} ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  {operational : CertifiedOperationalCanonicalPermutation name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital matching} ->
  (execution : PermutedCanonicalExecution name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital operational) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  {selected : name} ->
  (pair : SelectedCanonicalBlockPair name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital matching operational selected) ->
  (leftComponent : Component key value world error) -> (leftParent : Parent name) ->
  (leftTable : OwnedTable key value (componentProvisions leftComponent)) ->
  (leftView : View name (dependencies (componentDependencies leftComponent))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected
    (registry (blockPreStart (pairLeftBlock pair))) =
    Just (MkFiber leftComponent leftParent False leftTable (Inactive Nothing))) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies leftComponent))
    (registry (blockPreStart (pairLeftBlock pair))) = Just leftView) ->
  (MkSystemState (worldState (blockPreStart (pairLeftBlock pair)))
    (replaceBinding @{nameEq} selected
      (MkFiber leftComponent leftParent False leftTable
        (Reloading (componentProgram leftComponent) id leftView))
      (registry (blockPreStart (pairLeftBlock pair)))) = (blockStart (pairLeftBlock pair))) ->
  O20BeginObservation name key world error value nameEq keyEq
    (renameForward (expectedBridgeBijection sameInputs) selected)
    (blockPreStart (pairRightBlock pair)) (blockStart (pairRightBlock pair)) ->
  O20SharedBeginObservations name key world error value nameEq keyEq
    (expectedBridgeBijection sameInputs) selected
    (blockPreStart (pairLeftBlock pair)) (blockStart (pairLeftBlock pair))
    (blockPreStart (pairRightBlock pair)) (blockStart (pairRightBlock pair))
o20ShareCanonicalBeginRight execution leftUnique rightUnique pair
  leftComponent leftParent leftTable leftView leftFound leftResolved leftExact
  (MkO20BeginObservation rightComponent rightParent rightTable rightView rightFound rightResolved rightExact) =
    o20ShareBeginValues leftComponent rightComponent
      (o20SelectedOpeningComponents execution leftUnique rightUnique pair
        (MkFiber leftComponent leftParent False leftTable (Inactive Nothing))
        (MkFiber rightComponent rightParent False rightTable (Inactive Nothing)) leftFound rightFound)
      leftParent rightParent leftTable rightTable leftView rightView
      leftFound rightFound leftResolved rightResolved leftExact rightExact

||| Open just the LEFT actual Begin observation and delegate the right
||| elimination to o20ShareCanonicalBeginRight. Both observations are native;
||| all component matching is produced from accepted original/replay capital.
export
0 o20ShareCanonicalBeginObservations :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace} ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace} ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  {operational : CertifiedOperationalCanonicalPermutation name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital matching} ->
  (execution : PermutedCanonicalExecution name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital operational) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  {selected : name} ->
  (pair : SelectedCanonicalBlockPair name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital matching operational selected) ->
  O20BeginObservation name key world error value nameEq keyEq selected
    (blockPreStart (pairLeftBlock pair)) (blockStart (pairLeftBlock pair)) ->
  O20BeginObservation name key world error value nameEq keyEq
    (renameForward (expectedBridgeBijection sameInputs) selected)
    (blockPreStart (pairRightBlock pair)) (blockStart (pairRightBlock pair)) ->
  O20SharedBeginObservations name key world error value nameEq keyEq
    (expectedBridgeBijection sameInputs) selected
    (blockPreStart (pairLeftBlock pair)) (blockStart (pairLeftBlock pair))
    (blockPreStart (pairRightBlock pair)) (blockStart (pairRightBlock pair))
o20ShareCanonicalBeginObservations execution leftUnique rightUnique pair
  (MkO20BeginObservation leftComponent leftParent leftTable leftView leftFound leftResolved leftExact) rightSeen =
    o20ShareCanonicalBeginRight execution leftUnique rightUnique pair
      leftComponent leftParent leftTable leftView leftFound leftResolved leftExact rightSeen

||| Accepted canonical/replay capital produces one SHARED component (hence one
||| initial program) and both actual Begin packets at EVERY selected supported
||| pair. Neither observation, component equality, nor pre-cut control/effects
||| is an input. This does not pair the remaining block role words.
export
0 o20SelectedCanonicalSharedBegins :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace} ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace} ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  {operational : CertifiedOperationalCanonicalPermutation name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital matching} ->
  (execution : PermutedCanonicalExecution name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital operational) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  {selected : name} ->
  (pair : SelectedCanonicalBlockPair name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital matching operational selected) ->
  O20SharedBeginObservations name key world error value nameEq keyEq
    (expectedBridgeBijection sameInputs) selected
    (blockPreStart (pairLeftBlock pair)) (blockStart (pairLeftBlock pair))
    (blockPreStart (pairRightBlock pair)) (blockStart (pairRightBlock pair))
o20SelectedCanonicalSharedBegins {nameEq} {keyEq} {sameInputs} {selected}
  execution leftUnique rightUnique pair =
    o20ShareCanonicalBeginObservations execution leftUnique rightUnique pair
      (o20ObserveActualBegin nameEq keyEq selected
        (blockPreStart (pairLeftBlock pair)) (blockStart (pairLeftBlock pair))
        (blockOpening (pairLeftBlock pair)))
      (o20ObserveActualBegin nameEq keyEq (renameForward (expectedBridgeBijection sameInputs) selected)
        (blockPreStart (pairRightBlock pair)) (blockStart (pairRightBlock pair))
        (blockOpening (pairRightBlock pair)))
