module DGamma.CP4DeletionSelectedEpisodeAnchors

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionCommittedProviderPersistence
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedEpisodeReplay
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorClassify
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorReliance
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceSnapshot
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorTrace
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import DGamma.CP4DeletionSelectedForeignLifecycleCrossing
import DGamma.CP4DeletionSelectedForeignLifecycleProviderFrame
import Data.List.Elem
import Decidable.Equality

%default total

0 appendLeftOccursAnchors :
  (left : Transitions first middle) -> (right : Transitions middle finalState) ->
  OccursIn transition left -> OccursIn transition (appendTransitions left right)
appendLeftOccursAnchors NoTransitions right occurs impossible
appendLeftOccursAnchors (MoreTransitions head rest) right OccursHere = OccursHere
appendLeftOccursAnchors (MoreTransitions head rest) right (OccursLater later) =
  OccursLater (appendLeftOccursAnchors rest right later)

0 appendRightOccursAnchors :
  (left : Transitions first middle) -> (right : Transitions middle finalState) ->
  OccursIn transition right -> OccursIn transition (appendTransitions left right)
appendRightOccursAnchors NoTransitions right occurs = occurs
appendRightOccursAnchors (MoreTransitions head rest) right occurs =
  OccursLater (appendRightOccursAnchors rest right occurs)

0 transportOccursAnchors :
  {left, right : Transitions first finalState} ->
  {transition : Transition stepBefore stepAfter} ->
  left = right -> OccursIn transition left -> OccursIn transition right
transportOccursAnchors Refl occurs = occurs

0 selectedInteriorOccurrenceInGlobal :
  (located : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  (transition : Transition before afterState) ->
  OccursIn transition (closedInside (locatedEpisode located)) ->
  OccursIn transition global
selectedInteriorOccurrenceInGlobal located transition inside =
  let afterOpening = appendLeftOccursAnchors
        (closedInside (locatedEpisode located))
        (MoreTransitions (unloadTransition (closing (locatedEpisode located)))
          (traceAfterClosing located)) inside
      afterPrefix = appendRightOccursAnchors (traceBeforeOpening located)
        (MoreTransitions (beginTransition (closedOpening
          (locatedEpisode located)))
          (appendTransitions (closedInside (locatedEpisode located))
            (MoreTransitions
              (unloadTransition (closing (locatedEpisode located)))
              (traceAfterClosing located))))
        (OccursLater afterOpening)
      reassociated = cong
        (appendTransitions (traceBeforeOpening located) .
          MoreTransitions (beginTransition
            (closedOpening (locatedEpisode located))))
        (sym (appendTransitionsAssociative
          (closedInside (locatedEpisode located))
          (MoreTransitions
            (unloadTransition (closing (locatedEpisode located))) NoTransitions)
          (traceAfterClosing located)))
      decomposition = trans reassociated (locatedDecomposition located)
  in transportOccursAnchors decomposition afterPrefix

0 alignedFromInstalledAnchors :
  (trace : Transitions first finalState) ->
  InstalledTrace name key world error value nameEq keyEq selected trace ->
  AlignedTransitions name key world error value nameEq keyEq trace
alignedFromInstalledAnchors NoTransitions (InstalledEnd installed) = AlignedEnd
alignedFromInstalledAnchors
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
  (InstalledStep action tag checked rest source tail) =
    AlignedStep action tag checked rest (alignedFromInstalledAnchors rest tail)

0 installedAppendLeftAnchors :
  (left : Transitions first middle) -> (right : Transitions middle finalState) ->
  InstalledTrace name key world error value nameEq keyEq actor
    (appendTransitions left right) ->
  InstalledTrace name key world error value nameEq keyEq actor left
installedAppendLeftAnchors NoTransitions right installed =
  InstalledEnd (installedTraceStart installed)
installedAppendLeftAnchors
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest) right
  (InstalledStep action tag checked (appendTransitions rest right) source tail) =
    InstalledStep action tag checked rest source
      (installedAppendLeftAnchors rest right tail)

0 extendFirstClosingAnchors :
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  FirstClosingResult name key world error value nameEq keyEq actor left ->
  FirstClosingResult name key world error value nameEq keyEq actor
    (appendTransitions left right)
extendFirstClosingAnchors left right
  (MkFirstClosingResult closeBefore closeAfter beforeClosing installedBefore
    closing afterClosing decomposition) =
      MkFirstClosingResult closeBefore closeAfter beforeClosing installedBefore
        closing (appendTransitions afterClosing right)
        (trans
          (sym (appendTransitionsAssociative beforeClosing
            (MoreTransitions (unloadTransition closing) afterClosing) right))
          (cong (\trace => appendTransitions trace right) decomposition))

0 selectedSuffixAnchors :
  {initial, finalState : SystemState name key value world error} ->
  {global : Transitions initial finalState} ->
  (located : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  Transitions (lastInstalledState (locatedEpisode located)) finalState
selectedSuffixAnchors located = MoreTransitions
  (unloadTransition (closing (locatedEpisode located)))
  (traceAfterClosing located)

0 nonBeginInstalledAnchorAnchors :
  (located : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  (transition : Transition before afterState) ->
  (insidePrefix : Transitions
    (closedStartState (locatedEpisode located)) before) ->
  (rest : Transitions afterState
    (lastInstalledState (locatedEpisode located))) ->
  appendTransitions insidePrefix (MoreTransitions transition rest) =
    closedInside (locatedEpisode located) ->
  installedAt @{nameEq} actor before = True ->
  transitionAction transition = action ->
  actionOwner action = actor ->
  lifecycleOccurrenceAnchorState action before afterState = before ->
  ForeignLifecycleInstalledAnchor name key world error value nameEq keyEq actor
    transition global
nonBeginInstalledAnchorAnchors located transition insidePrefix rest insideSame
  sourceInstalled sameAction sameOwner stateIsBefore =
    let 0 decomposition : (appendTransitions
          (appendTransitions (traceBeforeOpening located)
            (MoreTransitions
              (beginTransition (closedOpening (locatedEpisode located)))
              insidePrefix))
          (appendTransitions (MoreTransitions transition rest)
            (selectedSuffixAnchors located)) = global)
        decomposition =
          rewrite appendTransitionsAssociative (traceBeforeOpening located)
            (MoreTransitions
              (beginTransition (closedOpening (locatedEpisode located)))
              insidePrefix)
            (appendTransitions (MoreTransitions transition rest)
              (selectedSuffixAnchors located)) in
          rewrite sym (appendTransitionsAssociative insidePrefix
            (MoreTransitions transition rest) (selectedSuffixAnchors located)) in
          rewrite insideSame in
          rewrite sym (appendTransitionsAssociative
            (closedInside (locatedEpisode located))
            (MoreTransitions
              (unloadTransition (closing (locatedEpisode located))) NoTransitions)
            (traceAfterClosing located)) in
          locatedDecomposition located
    in case sameAction of
      Refl => case sameOwner of
        Refl => MkForeignLifecycleInstalledAnchor before
          (appendTransitions (traceBeforeOpening located)
            (MoreTransitions
              (beginTransition (closedOpening (locatedEpisode located)))
              insidePrefix))
          (appendTransitions (MoreTransitions transition rest)
            (selectedSuffixAnchors located))
          sourceInstalled (sym stateIsBefore) decomposition

0 beginInstalledAnchorAnchors :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, finalState, before, afterState :
    SystemState name key value world error} ->
  {global : Transitions initial finalState} -> {selected : name} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (located : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  (actor : name) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LBegin actor) before =
    Just (tag, afterState)) ->
  (insidePrefix : Transitions
    (closedStartState (locatedEpisode located)) before) ->
  (rest : Transitions afterState
    (lastInstalledState (locatedEpisode located))) ->
  appendTransitions insidePrefix
    (MoreTransitions (Fired nameEq keyEq (LBegin actor) tag checked) rest) =
      closedInside (locatedEpisode located) ->
  installedAt @{nameEq} actor afterState = True ->
  ForeignLifecycleInstalledAnchor name key world error value nameEq keyEq actor
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq (LBegin actor) tag checked) global
beginInstalledAnchorAnchors nameEq keyEq located actor tag checked insidePrefix
  rest insideSame targetInstalled =
    let 0 beforeDecomposition : (appendTransitions
          (appendTransitions (traceBeforeOpening located)
            (MoreTransitions
              (beginTransition (closedOpening (locatedEpisode located)))
              insidePrefix))
          (appendTransitions (MoreTransitions (Fired nameEq keyEq (LBegin actor) tag checked) rest)
            (selectedSuffixAnchors located)) = global)
        beforeDecomposition =
          rewrite appendTransitionsAssociative (traceBeforeOpening located)
            (MoreTransitions
              (beginTransition (closedOpening (locatedEpisode located)))
              insidePrefix)
            (appendTransitions (MoreTransitions (Fired nameEq keyEq (LBegin actor) tag checked) rest)
              (selectedSuffixAnchors located)) in
          rewrite sym (appendTransitionsAssociative insidePrefix
            (MoreTransitions (Fired nameEq keyEq (LBegin actor) tag checked) rest) (selectedSuffixAnchors located)) in
          rewrite insideSame in
          rewrite sym (appendTransitionsAssociative
            (closedInside (locatedEpisode located))
            (MoreTransitions
              (unloadTransition (closing (locatedEpisode located))) NoTransitions)
            (traceAfterClosing located)) in
          locatedDecomposition located
    in MkForeignLifecycleInstalledAnchor afterState
      (appendTransitions
        (appendTransitions (traceBeforeOpening located)
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode located)))
            insidePrefix))
        (MoreTransitions (Fired nameEq keyEq (LBegin actor) tag checked) NoTransitions))
      (appendTransitions rest (selectedSuffixAnchors located)) targetInstalled
      Refl
      (trans (appendTransitionsAssociative
        (appendTransitions (traceBeforeOpening located)
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode located)))
            insidePrefix))
        (MoreTransitions (Fired nameEq keyEq (LBegin actor) tag checked) NoTransitions)
        (appendTransitions rest (selectedSuffixAnchors located)))
        beforeDecomposition)

0 appendOccurrenceTargetAnchors :
  (earlier : Transitions initial before) ->
  (transition : Transition before afterState) ->
  (suffix : Transitions afterState finalState) ->
  appendTransitions earlier (MoreTransitions transition suffix) = global ->
  appendTransitions
    (appendTransitions earlier (MoreTransitions transition NoTransitions))
    suffix = global
appendOccurrenceTargetAnchors earlier transition suffix decomposition =
  trans (appendTransitionsAssociative earlier
    (MoreTransitions transition NoTransitions) suffix) decomposition

0 stateEtaAnchors : (state : SystemState name key value world error) ->
  MkSystemState (worldState state) (registry state) = state
stateEtaAnchors (MkSystemState ambient fibers) = Refl

0 lifecycleNonBeginStateAnchors :
  (action : Action name key value world error) ->
  Not (action = LBegin (actionOwner action)) ->
  lifecycleOccurrenceAnchorState action before afterState = before
lifecycleNonBeginStateAnchors (OInsert actor parent component) notBegin = Refl
lifecycleNonBeginStateAnchors (ORetire actor) notBegin = Refl
lifecycleNonBeginStateAnchors (ORemove actor) notBegin = Refl
lifecycleNonBeginStateAnchors (LBegin actor) notBegin = void (notBegin Refl)
lifecycleNonBeginStateAnchors (LAdvance actor) notBegin = Refl
lifecycleNonBeginStateAnchors (LDivert actor) notBegin = Refl
lifecycleNonBeginStateAnchors (LLeave actor) notBegin = Refl
lifecycleNonBeginStateAnchors (LUnload actor) notBegin = Refl

0 lifecycleSourceInstalledAnchors :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  isLifecycleAction action = True ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  Not (action = LBegin (actionOwner action)) ->
  installedAt @{nameEq} (actionOwner action) before = True
lifecycleSourceInstalledAnchors nameEq keyEq (OInsert actor parent component)
  Refl before afterState tag checked notBegin impossible
lifecycleSourceInstalledAnchors nameEq keyEq (ORetire actor) Refl before
  afterState tag checked notBegin impossible
lifecycleSourceInstalledAnchors nameEq keyEq (ORemove actor) Refl before
  afterState tag checked notBegin impossible
lifecycleSourceInstalledAnchors nameEq keyEq (LBegin actor) lifecycle before
  afterState tag checked notBegin = void (notBegin Refl)
lifecycleSourceInstalledAnchors nameEq keyEq (LAdvance actor) lifecycle before
  afterState tag checked notBegin = lAdvanceStartsInstalled nameEq keyEq actor
    before afterState tag (checkedActionProjects nameEq keyEq (LAdvance actor)
      before afterState tag checked)
lifecycleSourceInstalledAnchors nameEq keyEq (LDivert actor) lifecycle before
  afterState tag checked notBegin =
    let raw = checkedActionProjects nameEq keyEq (LDivert actor) before
          afterState tag checked
        tagSame = successfulLDivertTag nameEq keyEq actor before afterState tag
          raw
        rawAt : (applyAction @{nameEq} @{keyEq} (LDivert actor) before =
          Just (LDivertTag, afterState))
        rawAt = replace
          {p = \observed => applyAction @{nameEq} @{keyEq} (LDivert actor)
            before = Just (observed, afterState)} tagSame raw
    in fst (lDivertInstalled nameEq keyEq actor before afterState rawAt)
lifecycleSourceInstalledAnchors nameEq keyEq (LLeave actor) lifecycle before
  afterState tag checked notBegin = fst (lLeaveInstalled nameEq keyEq actor
    before afterState tag (checkedActionProjects nameEq keyEq (LLeave actor)
      before afterState tag checked))
lifecycleSourceInstalledAnchors nameEq keyEq (LUnload actor) lifecycle before
  afterState tag checked notBegin = fst (snd (lUnloadBoundary nameEq keyEq actor
    before afterState tag (checkedActionProjects nameEq keyEq (LUnload actor)
      before afterState tag checked)))

||| Construct the complete occurrence-local provider-anchor callback from the
||| accepted Lemma-72 premises.  A foreign activation which closes is handled by
||| the committed-provider crossing theorem; one which survives to the selected
||| close is handled by the L-Unload reliance guard.
public export
0 selectedEpisodeLifecycleAnchorProvider :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (initial, finalState : SystemState name key value world error) ->
  (global : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  registryWellFormed @{nameEq} @{keyEq} initial = True ->
  bindings (registry initial) = [] ->
  (selected : name) ->
  (located : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  (registered : List (RegistrationGeneration name)) ->
  NoDependentClosingEpisode {nameEq = nameEq} {keyEq = keyEq} selected global ->
  SelectedEpisodeLifecycleAnchorProvider name key world error value nameEq keyEq
    selected registered global (locatedEpisode located)
selectedEpisodeLifecycleAnchorProvider {name} {key} {world} {error} {value}
  nameEq keyEq initial finalState global aligned initialWellFormed initialEmpty
  selected located registered noDependent =
    MkSelectedEpisodeLifecycleAnchorProvider provide
  where
  0 provide :
    (ordinal : Nat) -> (live : GenerationEnvironment name) ->
    (action : Action name key value world error) ->
    (lifecycle : isLifecycleAction action = True) ->
    (distinct : Not (actionOwner action = selected)) ->
    (before, afterState : SystemState name key value world error) ->
    (tag : RuleTag) ->
    (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
      Just (tag, afterState)) ->
    (rest : Transitions afterState
      (lastInstalledState (locatedEpisode located))) ->
    InstalledTrace name key world error value nameEq keyEq selected rest ->
    (occurs : OccursIn
      (Fired {before = before} {afterState = afterState}
        nameEq keyEq action tag checked) global) ->
    (insidePrefix : Transitions
      (closedStartState (locatedEpisode located)) before) ->
    appendTransitions insidePrefix
      (MoreTransitions (Fired nameEq keyEq action tag checked) rest) =
        closedInside (locatedEpisode located) ->
    {wholeFirst, wholeLast : SystemState name key value world error} ->
    {whole : Transitions wholeFirst wholeLast} ->
    {survivor : SystemState name key value world error} ->
    (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
      keyEq selected registered ordinal live whole before survivor) ->
    (leftSelected, leftOwner, rightOwner : Fiber name key value world error) ->
    lookupFiber @{nameEq} selected
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))) =
      Just leftSelected ->
    lookupFiber @{nameEq} (actionOwner action)
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))) =
      Just leftOwner ->
    lookupFiber @{nameEq} selected (registry before) = Just leftSelected ->
    lookupFiber @{nameEq} (actionOwner action) (registry before) =
      Just leftOwner ->
    lookupFiber @{nameEq} (actionOwner action) (registry survivor) =
      Just rightOwner ->
    FiberControlRelated leftOwner rightOwner ->
    ForeignLifecycleProviderFrameEvidence name key world error value nameEq keyEq
      global selected (actionOwner action)
      (MkSystemState (worldState before)
        (planTarget (completePlanResult (selectedBoundaryPlan boundary))))
      leftSelected leftOwner
  provide ordinal live action lifecycle distinct before afterState tag checked
    rest selectedRest occurs insidePrefix insideDecomposition boundary
    leftSelected leftOwner
    rightOwner planSelectedFound planOwnerFound originalSelectedFound
    originalOwnerFound rightFound controls = case action of
      OInsert actor parent component => case lifecycle of Refl impossible
      ORetire actor => case lifecycle of Refl impossible
      ORemove actor => case lifecycle of Refl impossible
      LBegin actor => beginEvidence actor distinct checked originalOwnerFound
        insideDecomposition
      LAdvance actor => classifyNonBegin (\same => case same of Refl impossible)
      LDivert actor => classifyNonBegin (\same => case same of Refl impossible)
      LLeave actor => classifyNonBegin (\same => case same of Refl impossible)
      LUnload actor => classifyNonBegin (\same => case same of Refl impossible)
    where
    0 directAtBefore :
      (actorInstalledToClose : InstalledTrace name key world error value nameEq
        keyEq (actionOwner action)
        (MoreTransitions
          (Fired {before = before} {afterState = afterState}
            nameEq keyEq action tag checked) rest)) ->
      ((wanted : key) -> Elem wanted (dependencies
        (componentDependencies (fiberComponent leftOwner))) ->
        providerCandidate @{keyEq} wanted leftSelected = False)
    directAtBefore actorInstalledToClose wanted ownerDeclares =
      let 0 reliance : SelectedUnloadRelianceAnchor name key world error value
            nameEq keyEq selected (actionOwner action) {current = before}
            (locatedEpisode located) leftOwner
          reliance = selectedUnloadRelianceAnchorFromInstalledTrace nameEq
            keyEq selected (actionOwner action) (locatedEpisode located) before
            (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
            actorInstalledToClose leftOwner originalOwnerFound
      in relianceAnchorProviderExcluded nameEq keyEq selected
        (actionOwner action) distinct (locatedEpisode located) before
        (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
        actorInstalledToClose leftSelected leftOwner originalSelectedFound
        originalOwnerFound (selectedOriginalWellFormed boundary) reliance wanted
        ownerDeclares

    0 classifyNonBegin :
      Not (action = LBegin (actionOwner action)) ->
      ForeignLifecycleProviderFrameEvidence name key world error value nameEq
        keyEq global selected (actionOwner action)
        (MkSystemState (worldState before)
          (planTarget (completePlanResult (selectedBoundaryPlan boundary))))
        leftSelected leftOwner
    classifyNonBegin notBegin =
      let 0 sourceInstalled = lifecycleSourceInstalledAnchors nameEq keyEq action
            lifecycle before afterState tag checked notBegin
          0 localAligned = AlignedStep action tag checked rest
            (alignedFromInstalledAnchors rest selectedRest)
      in case classifyInstalledContinuation nameEq keyEq (actionOwner action)
        (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
        localAligned sourceInstalled of
        ContinuationStaysInstalled actorInstalled =>
          DirectProviderFrameEvidence (directAtBefore actorInstalled)
        ContinuationCloses localClosing =>
          let globalClosing = extendFirstClosingAnchors
                (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
                (selectedSuffixAnchors located) localClosing
          in case closingOccurrenceGivesLocatedActivation nameEq keyEq
            (actionOwner action) (Fired nameEq keyEq action tag checked) global
            aligned initialEmpty
            (nonBeginInstalledAnchorAnchors located
              (Fired nameEq keyEq action tag checked) insidePrefix rest
              insideDecomposition sourceInstalled Refl Refl
              (lifecycleNonBeginStateAnchors action notBegin))
            globalClosing of
            locatedActivation => DirectProviderFrameEvidence
              (crossingActivationExcludesSelectedProvider nameEq keyEq selected
                (actionOwner action) global aligned initialWellFormed noDependent
                (closingActivationEpisode locatedActivation) before
                (activationToOccurrenceAnchor locatedActivation)
                (activationToOccurrenceInstalled locatedActivation) leftSelected
                leftOwner originalSelectedFound originalOwnerFound
                (selectedOriginalWellFormed boundary))

    0 installedFiberCrossingLocal :
      (actor : name) -> (state : SystemState name key value world error) ->
      installedAt @{nameEq} actor state = True ->
      (fiber : Fiber name key value world error **
        lookupFiber @{nameEq} actor (registry state) = Just fiber)
    installedFiberCrossingLocal actor state installed
      with (lookupFiber @{nameEq} actor (registry state)) proof found
      installedFiberCrossingLocal actor state installed | Nothing =
        case installed of Refl impossible
      installedFiberCrossingLocal actor state installed | Just fiber =
        (fiber ** Refl)

    0 beginEvidence : (actor : name) -> Not (actor = selected) ->
      (checkedAt : checkedApplyAction @{nameEq} @{keyEq} (LBegin actor) before =
        Just (tag, afterState)) ->
      lookupFiber @{nameEq} actor (registry before) = Just leftOwner ->
      appendTransitions insidePrefix
        (MoreTransitions (Fired nameEq keyEq (LBegin actor) tag checkedAt) rest) =
          closedInside (locatedEpisode located) ->
      ForeignLifecycleProviderFrameEvidence name key world error value nameEq
        keyEq global selected actor
        (MkSystemState (worldState before)
          (planTarget (completePlanResult (selectedBoundaryPlan boundary))))
        leftSelected leftOwner
    beginEvidence actor actorDistinct checkedAt ownerFoundAt
      insideDecompositionAt =
      let 0 raw = checkedActionProjects nameEq keyEq (LBegin actor) before
            afterState tag checkedAt
          0 targetInstalled = snd (snd
            (lBeginBoundary nameEq keyEq actor before afterState tag checkedAt))
      in case installedFiberCrossingLocal actor afterState targetInstalled of
        (afterOwner ** afterOwnerFound) =>
          let 0 selectedAfterFound : (lookupFiber @{nameEq} selected
                (registry afterState) = Just leftSelected)
              selectedAfterFound = trans
                (systemLocalUpdateForeign nameEq selected actor
                  (\same => actorDistinct (sym same)) before
                  afterState (applyActionLocalUpdate nameEq keyEq
                    (LBegin actor) before afterState tag raw))
                originalSelectedFound
              0 ownerComponent : (fiberComponent afterOwner =
                fiberComponent leftOwner)
              ownerComponent = checkedStepPreservesPresentComponent nameEq keyEq
                actor (LBegin actor) tag before afterState checkedAt leftOwner
                afterOwner ownerFoundAt afterOwnerFound
              0 afterWellFormed : (registryWellFormed @{nameEq} @{keyEq}
                afterState = True)
              afterWellFormed = preservationTheoremProof nameEq keyEq
                (LBegin actor) before afterState tag
                (selectedOriginalWellFormed boundary) raw
              0 restAligned : AlignedTransitions name key world error value
                nameEq keyEq rest
              restAligned = alignedFromInstalledAnchors rest selectedRest
              transfer : ((wanted : key) -> Elem wanted (dependencies
                (componentDependencies (fiberComponent afterOwner))) ->
                providerCandidate @{keyEq} wanted leftSelected = False) ->
                ((wanted : key) -> Elem wanted (dependencies
                  (componentDependencies (fiberComponent leftOwner))) ->
                  providerCandidate @{keyEq} wanted leftSelected = False)
              transfer excluded wanted ownerDeclares = excluded wanted
                (replace
                  {p = \component => Elem wanted
                    (dependencies (componentDependencies component))}
                  (sym ownerComponent) ownerDeclares)
          in case classifyInstalledContinuation nameEq keyEq actor rest
            restAligned targetInstalled of
            ContinuationStaysInstalled actorInstalled =>
              let 0 reliance : SelectedUnloadRelianceAnchor name key world error
                    value nameEq keyEq selected actor {current = afterState}
                    (locatedEpisode located) afterOwner
                  reliance = selectedUnloadRelianceAnchorFromInstalledTrace
                    nameEq keyEq selected actor (locatedEpisode located)
                    afterState rest actorInstalled afterOwner afterOwnerFound
                  0 excluded : (wanted : key) -> Elem wanted (dependencies
                    (componentDependencies (fiberComponent afterOwner))) ->
                    providerCandidate @{keyEq} wanted leftSelected = False
                  excluded = relianceAnchorProviderExcluded nameEq keyEq selected
                    actor actorDistinct (locatedEpisode located) afterState rest
                    actorInstalled leftSelected afterOwner selectedAfterFound
                    afterOwnerFound afterWellFormed reliance
              in DirectProviderFrameEvidence (transfer excluded)
            ContinuationCloses localClosing =>
              let globalClosing = extendFirstClosingAnchors rest
                    (selectedSuffixAnchors located) localClosing
              in case closingOccurrenceGivesLocatedActivation nameEq keyEq actor
                (Fired nameEq keyEq (LBegin actor) tag checkedAt) global aligned initialEmpty
                (beginInstalledAnchorAnchors nameEq keyEq located actor tag checkedAt
                  insidePrefix rest insideDecompositionAt targetInstalled)
                globalClosing of
                locatedActivation => DirectProviderFrameEvidence (transfer
                  (crossingActivationExcludesSelectedProvider nameEq keyEq
                    selected actor global aligned initialWellFormed noDependent
                    (closingActivationEpisode locatedActivation) afterState
                    (activationToOccurrenceAnchor locatedActivation)
                    (activationToOccurrenceInstalled locatedActivation)
                    leftSelected afterOwner selectedAfterFound afterOwnerFound
                    afterWellFormed))
