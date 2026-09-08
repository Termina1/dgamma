module DGamma.CP5O20CanonicalPairSelectionSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorOpen
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20EpisodeSynchronizationSpike
import DGamma.CP5O20PairedPrefixProducerSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Derive membership of the supported actor's image in the ACTUAL right
||| canonical enumeration, using the fixed accepted matching. No renaming or
||| replacement execution is selected by this helper.
export
0 canonicalPairRightMember :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) -> (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq rightTrace) ->
  MappedCanonicalSupportOrders name key world error value protocol nameEq keyEq leftTrace rightTrace
    (expectedBridgeBijection sameInputs) (canonicalSchedule leftCapital) (canonicalSchedule rightCapital) ->
  (selected : name) -> (isSupported @{nameEq} @{keyEq} selected leftFinal = True) ->
  Elem (renameForward (expectedBridgeBijection sameInputs) selected) (supportOrder (canonicalSchedule rightCapital))
canonicalPairRightMember nameEq keyEq protocol leftTrace rightTrace sameInputs
  leftCapital rightCapital matching selected supported =
    leftSupportMapped matching selected
      (orderComplete (supportLinearization (canonicalSchedule leftCapital)) selected supported)

||| Membership in the inverse-mapped operational target order, with the
||| selected name recovered using the same bijection's left inverse.
export
0 canonicalPairInverseMember :
  {name : Type} -> (renaming : NameBijection name) -> (selected : name) -> (order : List name) ->
  Elem (renameForward renaming selected) order ->
  Elem selected (map (renameBackward renaming) order)
canonicalPairInverseMember renaming selected (_ :: rest) Here =
  replace {p = \actor => Elem actor
    (map (renameBackward renaming) (renameForward renaming selected :: rest))}
    (renameLeftInverse renaming selected) Here
canonicalPairInverseMember renaming selected (head :: rest) (There later) =
  There (canonicalPairInverseMember renaming selected rest later)

||| Authoritative paired block SELECTION in the actual operational-left and
||| right-canonical executions. This asserts no effects/control/view agreement.
||| Equality fields pin both ranges to their original capital, not lookalikes.
public export
record SelectedCanonicalBlockPair
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, leftFinal, rightFinal : SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal) (rightTrace : Transitions initial rightFinal)
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace)
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq leftTrace)
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq rightTrace)
  (matching : MappedCanonicalSupportOrders name key world error value protocol nameEq keyEq leftTrace rightTrace
    (expectedBridgeBijection sameInputs) (canonicalSchedule leftCapital) (canonicalSchedule rightCapital))
  (operational : CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital matching)
  (selected : name) where
  constructor MkSelectedCanonicalBlockPair
  0 pairSelectedSupported : isSupported @{nameEq} @{keyEq} selected leftFinal = True
  0 pairRightInCanonicalOrder : Elem (renameForward (expectedBridgeBijection sameInputs) selected)
    (supportOrder (canonicalSchedule rightCapital))
  0 pairLeftInOperationalOrder : Elem selected
    (map (renameBackward (expectedBridgeBijection sameInputs)) (supportOrder (canonicalSchedule rightCapital)))
  pairLeftBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected
    (operationalTargetTrace operational)
  pairRightBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
    (renameForward (expectedBridgeBijection sameInputs) selected) (canonicalTrace (canonicalSchedule rightCapital))
  0 pairLeftBlockChosen : pairLeftBlock =
    decomposedBlock (operationalTargetBlocks operational) selected pairLeftInOperationalOrder
  0 pairRightBlockChosen : pairRightBlock =
    decomposedBlock (canonicalActorBlockDecomposition rightCapital)
      (renameForward (expectedBridgeBijection sameInputs) selected) pairRightInCanonicalOrder

||| Actually SELECT both authoritative ranges from existing accepted O19
||| operational capital and the right canonical schedule. Runtime agreement
||| between their prefixes is NOT assumed or produced here.
export
0 selectSupportedCanonicalBlockPair :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) -> (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq rightTrace) ->
  (matching : MappedCanonicalSupportOrders name key world error value protocol nameEq keyEq leftTrace rightTrace
    (expectedBridgeBijection sameInputs) (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)) ->
  (operational : CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital matching) ->
  (selected : name) -> (isSupported @{nameEq} @{keyEq} selected leftFinal = True) ->
  SelectedCanonicalBlockPair name key world error value protocol nameEq keyEq leftTrace rightTrace
    sameInputs leftCapital rightCapital matching operational selected
selectSupportedCanonicalBlockPair nameEq keyEq protocol leftTrace rightTrace sameInputs
  leftCapital rightCapital matching operational selected supported =
    MkSelectedCanonicalBlockPair supported (canonicalPairRightMember nameEq keyEq protocol leftTrace rightTrace sameInputs
        leftCapital rightCapital matching selected supported) (canonicalPairInverseMember (expectedBridgeBijection sameInputs) selected
        (supportOrder (canonicalSchedule rightCapital)) (canonicalPairRightMember nameEq keyEq protocol leftTrace rightTrace sameInputs
        leftCapital rightCapital matching selected supported))
      (decomposedBlock (operationalTargetBlocks operational) selected (canonicalPairInverseMember (expectedBridgeBijection sameInputs) selected
        (supportOrder (canonicalSchedule rightCapital)) (canonicalPairRightMember nameEq keyEq protocol leftTrace rightTrace sameInputs
        leftCapital rightCapital matching selected supported)))
      (decomposedBlock (canonicalActorBlockDecomposition rightCapital)
        (renameForward (expectedBridgeBijection sameInputs) selected) (canonicalPairRightMember nameEq keyEq protocol leftTrace rightTrace sameInputs
        leftCapital rightCapital matching selected supported))
      Refl Refl

||| Locate the actual opening action owned by a selected block, retaining
||| its genuine prefix and suffix. Applicable separately to either chosen
||| execution; no cross-execution equality is inferred.
export
0 canonicalPairOpeningOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {initial, finalState : SystemState name key value world error} ->
  {trace : Transitions initial finalState} ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected trace) ->
  LocatedActionOccurrence (LBegin selected) trace
canonicalPairOpeningOccurrence block =
  MkLocatedActionOccurrence (blockPreStart block) (blockStart block) (traceBeforeBlock block)
    (beginTransition (blockOpening block)) (appendTransitions (blockBody block) (traceAfterBlock block))
    Refl (blockDecomposition block)

||| Both actual pre-opening cuts are well formed, derived independently from
||| their OWN reached/canonical replay bundles and exact block occurrences.
export
0 canonicalPairCutsWellFormed :
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
  (registryWellFormed @{nameEq} @{keyEq} (blockPreStart (pairLeftBlock pair)) = True,
   registryWellFormed @{nameEq} @{keyEq} (blockPreStart (pairRightBlock pair)) = True)
canonicalPairCutsWellFormed {name} {key} {world} {error} {value} {operational} {rightCapital}
  nameEq keyEq pair =
    (alignedTraceWellFormedEnd nameEq keyEq (traceBeforeBlock (pairLeftBlock pair))
      (Builtin.fst (alignedAppendSplit (traceBeforeBlock (pairLeftBlock pair))
        (MoreTransitions (beginTransition (blockOpening (pairLeftBlock pair))) (appendTransitions (blockBody (pairLeftBlock pair)) (traceAfterBlock (pairLeftBlock pair))))
        (replace {p = AlignedTransitions name key world error value nameEq keyEq}
          (sym (blockDecomposition (pairLeftBlock pair))) (replayAligned (operationalTargetPremises operational)))))
      (replayInitialWellFormed (operationalTargetPremises operational)),
     alignedTraceWellFormedEnd nameEq keyEq (traceBeforeBlock (pairRightBlock pair))
      (Builtin.fst (alignedAppendSplit (traceBeforeBlock (pairRightBlock pair))
        (MoreTransitions (beginTransition (blockOpening (pairRightBlock pair))) (appendTransitions (blockBody (pairRightBlock pair)) (traceAfterBlock (pairRightBlock pair))))
        (replace {p = AlignedTransitions name key world error value nameEq keyEq}
          (sym (blockDecomposition (pairRightBlock pair))) (replayAligned (canonicalReplayPremises rightCapital)))))
      (replayInitialWellFormed (canonicalReplayPremises rightCapital)))

||| Adapt R181 D6 to two EXPLICIT observed system states. Effect agreement
||| remains an induction hypothesis; successful views are actual resolver
||| observations. Right pairwise provision uniqueness is derived from WF.
export
0 canonicalPairViewsAtStates :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (renaming : NameBijection name) -> (deps : List key) ->
  (left, right : SystemState name key value world error) ->
  RenamedRuntimeEffects name key world value renaming
    (projectEffectState {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} left) (projectEffectState {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} right) ->
  (registryWellFormed {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} right = True) ->
  (leftView, rightView : View name deps) ->
  (resolveView {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} deps (registry left) = Just leftView) ->
  (resolveView {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} deps (registry right) = Just rightView) ->
  ViewRelatedBy renaming leftView rightView
canonicalPairViewsAtStates {name} {key} {world} {error} {value}
  nameEq keyEq renaming deps (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry)
  effects wellFormed leftView rightView leftResolved rightResolved =
    pairedActualResolvedViews name key world error value nameEq keyEq renaming deps
      leftWorld rightWorld leftRegistry rightRegistry effects
      (registryWellFormedPairwiseOpenAnchor {name = name} {key = key} {value = value} {world = world} {error = error} nameEq keyEq (MkSystemState rightWorld rightRegistry) wellFormed)
      leftView rightView leftResolved rightResolved

||| Instantiate D6 at the SELECTED ACTUAL canonical opening cuts and the
||| FIXED accepted bijection. WF is derived from C6. Prefix effect agreement
||| and successful resolver observations are explicit INTERNAL induction
||| hypotheses; producing that agreement along all prefixes remains open.
export
0 canonicalPairSelectedViews :
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
  (deps : List key) ->
  RenamedRuntimeEffects name key world value (expectedBridgeBijection sameInputs)
    (projectEffectState {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} (blockPreStart (pairLeftBlock pair)))
    (projectEffectState {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} (blockPreStart (pairRightBlock pair))) ->
  (leftView, rightView : View name deps) ->
  (resolveView {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} deps (registry (blockPreStart (pairLeftBlock pair))) = Just leftView) ->
  (resolveView {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} deps (registry (blockPreStart (pairRightBlock pair))) = Just rightView) ->
  ViewRelatedBy (expectedBridgeBijection sameInputs) leftView rightView
canonicalPairSelectedViews {name} {key} {world} {error} {value} {sameInputs} nameEq keyEq pair deps effects leftView rightView leftResolved rightResolved =
  canonicalPairViewsAtStates {name = name} {key = key} {value = value} {world = world} {error = error} nameEq keyEq (expectedBridgeBijection sameInputs) deps
    (blockPreStart (pairLeftBlock pair)) (blockPreStart (pairRightBlock pair)) effects
    (Builtin.snd (canonicalPairCutsWellFormed nameEq keyEq pair)) leftView rightView leftResolved rightResolved
