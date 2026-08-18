module DGamma.CP4DeletionSelectedForeignLifecycleAnchorEndpoint

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4Support
import DGamma.CP4SupportSolution
import DGamma.CP4Lemma70
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorCore
import Decidable.Equality

%default total

0 precedencePathIsSupportPath :
  PrecedencePath nameEq state lower upper ->
  SupportPath nameEq state lower upper
precedencePathIsSupportPath (PrecedenceOne edge) =
  SupportPathOne (SupportPrecedence edge)
precedencePathIsSupportPath (PrecedenceMore edge rest) =
  SupportPathMore (SupportPrecedence edge)
    (precedencePathIsSupportPath rest)

||| Protocol ranks recovered from the reached disciplined trace are stronger
||| than the paper's separate precedence-acyclic hypothesis.  This local bridge
||| keeps Lemma 72's public statement unchanged while supplying Lemma 70 with
||| the acyclicity argument it requires.
public export
0 disciplinedEndpointPrecedenceAcyclic :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  (reached : ReachedFromEmpty name key world error value nameEq keyEq state) ->
  RegistrationDiscipline protocol nameEq (reachTrace reached) ->
  PrecedenceAcyclic nameEq state
disciplinedEndpointPrecedenceAcyclic protocol nameEq keyEq state reached
  discipline =
    let 0 provenance = registrationDisciplineProvenance protocol nameEq
          (reachTrace reached) discipline
        0 ranked = reachedRegistryProtocolRanked protocol nameEq keyEq reached
          provenance
        0 parentOrdered = reachedRegistryParentRanksIncrease protocol nameEq
          keyEq reached provenance
        0 combined = supportCombinedWellFounded protocol nameEq state ranked
          parentOrdered
    in \selected, path => combined selected
      (precedencePathIsSupportPath path)

||| Construct the exact Lemma-70 endpoint equation from Lemma 72's existing
||| public premises.  This is the open-at-quiescence lifecycle anchor input; no
||| support or acyclicity premise is added to `deletionTheorem`.
public export
0 deletionPremisesGiveSupportMatchesActive :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (initial, finalState : SystemState name key value world error) ->
  (global : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  RegistrationDiscipline protocol nameEq global ->
  registryWellFormed @{nameEq} @{keyEq} initial = True ->
  bindings (registry initial) = [] ->
  quiet @{nameEq} @{keyEq} finalState = True ->
  noFailedFibers finalState = True ->
  TraceComponentsTotal nameEq keyEq global ->
  SupportMatchesActive nameEq keyEq finalState
deletionPremisesGiveSupportMatchesActive {name} {key} {world} {error} {value}
  protocol nameEq keyEq initial finalState global aligned discipline
  initialWellFormed initialEmpty quietFinal noFailures totality =
    let reached : ReachedFromEmpty name key world error value nameEq keyEq
          finalState
        reached = MkReachedFromEmpty initial global aligned initialEmpty
          initialWellFormed
        0 acyclic : PrecedenceAcyclic nameEq finalState
        acyclic = disciplinedEndpointPrecedenceAcyclic protocol nameEq keyEq
          finalState reached discipline
    in supportAtQuiescenceTheoremProof name key value world error nameEq keyEq
      protocol finalState reached discipline acyclic quietFinal noFailures
      totality

||| Populate the open-at-quiescence anchor directly from Lemma 72's existing
||| premises.  The caller supplies only the trace-derived endpoint fiber facts;
||| the Lemma-70 equation itself is reconstructed internally above.
public export
0 openForeignLifecycleAnchorFromDeletionPremises :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (initial, finalState : SystemState name key value world error) ->
  (global : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  RegistrationDiscipline protocol nameEq global ->
  registryWellFormed @{nameEq} @{keyEq} initial = True ->
  bindings (registry initial) = [] ->
  quiet @{nameEq} @{keyEq} finalState = True ->
  noFailedFibers finalState = True ->
  TraceComponentsTotal nameEq keyEq global ->
  (selected, actor : name) ->
  (currentSelected, currentOwner : Fiber name key value world error) ->
  (finalSelected, finalOwner : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry finalState) = Just finalSelected ->
  lookupFiber @{nameEq} actor (registry finalState) = Just finalOwner ->
  fiberComponent finalSelected = fiberComponent currentSelected ->
  fiberComponent finalOwner = fiberComponent currentOwner ->
  isActive (fiberLifecycle finalSelected) = False ->
  isActive (fiberLifecycle finalOwner) = True ->
  ForeignLifecyclePrecedenceAnchor name key world error value nameEq keyEq
    global selected actor currentSelected currentOwner
openForeignLifecycleAnchorFromDeletionPremises protocol nameEq keyEq initial
  finalState global aligned discipline initialWellFormed initialEmpty quietFinal
  noFailures totality selected actor currentSelected currentOwner finalSelected
  finalOwner selectedFound ownerFound selectedComponent ownerComponent
  selectedInactive ownerActive =
    OpenForeignLifecyclePrecedenceAnchor finalSelected finalOwner selectedFound
      ownerFound selectedComponent ownerComponent selectedInactive ownerActive
      (alignedTraceWellFormedEnd nameEq keyEq global aligned initialWellFormed)
      (deletionPremisesGiveSupportMatchesActive protocol nameEq keyEq initial
        finalState global aligned discipline initialWellFormed initialEmpty
        quietFinal noFailures totality)
