module DGamma.CP4DeletionSelectedForeignLifecycleAnchorClassify

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorTrace
import Decidable.Equality

%default total

0 falseNotTrueAnchorClassify : False = True -> Void
falseNotTrueAnchorClassify Refl impossible

||| An exact occurrence locator which, unlike `LocatedActionOccurrence`, retains
||| the transition's proof dictionaries and checked equation definitionally.
||| This is the right input for action-specific evaluator inversion.
public export
record LocatedTransitionOccurrence
  {initial, finalState, stepBefore, stepAfter :
    SystemState name key value world error}
  (transition : Transition stepBefore stepAfter)
  (global : Transitions initial finalState) where
  constructor MkLocatedTransitionOccurrence
  transitionOccurrencePrefix : Transitions initial stepBefore
  transitionOccurrenceSuffix : Transitions stepAfter finalState
  0 transitionOccurrenceDecomposition :
    appendTransitions transitionOccurrencePrefix
      (MoreTransitions transition transitionOccurrenceSuffix) = global

public export
0 locateTransitionOccurrence :
  (transition : Transition stepBefore stepAfter) ->
  (global : Transitions initial finalState) ->
  OccursIn transition global ->
  LocatedTransitionOccurrence transition global
locateTransitionOccurrence transition
  (MoreTransitions transition rest) OccursHere =
    MkLocatedTransitionOccurrence NoTransitions rest Refl
locateTransitionOccurrence transition
  (MoreTransitions head rest) (OccursLater later) =
    case locateTransitionOccurrence transition rest later of
      MkLocatedTransitionOccurrence earlier suffix decomposition =>
        MkLocatedTransitionOccurrence (MoreTransitions head earlier) suffix
          (cong (MoreTransitions head) decomposition)

||| Forward, episode-local classification from an installed point.  It stops at
||| the *first* L-Unload of this activation; a later L-Begin or raw-name reuse is
||| therefore never mistaken for continuation of the old episode merely because
||| the raw endpoint is installed again.
public export
data InstalledContinuation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  ContinuationCloses :
    FirstClosingResult name key world error value nameEq keyEq actor trace ->
    InstalledContinuation name key world error value nameEq keyEq actor trace
  ContinuationStaysInstalled :
    InstalledTrace name key world error value nameEq keyEq actor trace ->
    InstalledContinuation name key world error value nameEq keyEq actor trace

||| Constructively find the first close, or prove that the complete remaining
||| trace stays in the same installed interval.  This is deliberately not a
||| case split on the final installed bit: close/reopen and remove/reinsert
||| suffixes are classified by their first boundary.
public export
0 classifyInstalledContinuation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (trace : Transitions first finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  installedAt @{nameEq} actor first = True ->
  InstalledContinuation name key world error value nameEq keyEq actor trace
classifyInstalledContinuation nameEq keyEq actor NoTransitions AlignedEnd
  sourceInstalled =
    ContinuationStaysInstalled (InstalledEnd sourceInstalled)
classifyInstalledContinuation nameEq keyEq actor
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
  (AlignedStep action tag checked rest alignedRest) sourceInstalled =
    case installationEvolutionStep nameEq keyEq actor action tag _ _ checked of
      ClosedInstallation =>
        ContinuationCloses
          (MkFirstClosingResult _ _ NoTransitions
            (InstalledEnd sourceInstalled) (MkUnloadStep checked) rest Refl)
      RemainedInstalled stepSource stepTarget =>
        case classifyInstalledContinuation nameEq keyEq actor rest alignedRest
          stepTarget of
          ContinuationCloses
            (MkFirstClosingResult closeBefore closeAfter beforeClosing
              installedBefore closing afterClosing split) =>
                ContinuationCloses
                  (MkFirstClosingResult closeBefore closeAfter
                    (MoreTransitions
                      (Fired nameEq keyEq action tag checked) beforeClosing)
                    (InstalledStep action tag checked beforeClosing stepSource
                      installedBefore)
                    closing afterClosing
                    (cong
                      (MoreTransitions (Fired nameEq keyEq action tag checked))
                      split))
          ContinuationStaysInstalled installedRest =>
            ContinuationStaysInstalled
              (InstalledStep action tag checked rest stepSource installedRest)
      RemainedUninstalled stepSource stepTarget =>
        void (falseNotTrueAnchorClassify
          (trans (sym stepSource) sourceInstalled))
      OpenedInstallation =>
        case lBeginBoundary nameEq keyEq actor _ _ LBeginTag checked of
          (tagShape, stepSource, stepTarget) =>
            void (falseNotTrueAnchorClassify
              (trans (sym stepSource) sourceInstalled))

public export
lifecycleOccurrenceAnchorState :
  Action name key value world error ->
  SystemState name key value world error ->
  SystemState name key value world error ->
  SystemState name key value world error
lifecycleOccurrenceAnchorState (LBegin actor) before afterState = afterState
lifecycleOccurrenceAnchorState action before afterState = before

||| Every retained lifecycle occurrence has a canonical installed anchor.
||| L-Begin anchors immediately after itself; all other lifecycle rules anchor
||| immediately before themselves.  The two traces still compose to the exact
||| original global trace, so the activation can subsequently be classified
||| without erasing occurrence identity.
public export
record ForeignLifecycleInstalledAnchor
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (actor : name)
  {initial, finalState, stepBefore, stepAfter :
    SystemState name key value world error}
  (transition : Transition stepBefore stepAfter)
  (global : Transitions initial finalState) where
  constructor MkForeignLifecycleInstalledAnchor
  lifecycleInstalledState : SystemState name key value world error
  lifecycleBeforeInstalled : Transitions initial lifecycleInstalledState
  lifecycleAfterInstalled : Transitions lifecycleInstalledState finalState
  0 lifecycleAnchorInstalled :
    installedAt @{nameEq} actor lifecycleInstalledState = True
  0 lifecycleAnchorState : lifecycleInstalledState =
    lifecycleOccurrenceAnchorState (transitionAction transition) stepBefore
      stepAfter
  0 lifecycleAnchorDecomposition :
    appendTransitions lifecycleBeforeInstalled lifecycleAfterInstalled = global

0 alignedAppendSplitAnchorClassify :
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  AlignedTransitions name key world error value nameEq keyEq
    (appendTransitions left right) ->
  (AlignedTransitions name key world error value nameEq keyEq left,
   AlignedTransitions name key world error value nameEq keyEq right)
alignedAppendSplitAnchorClassify NoTransitions right aligned =
  (AlignedEnd, aligned)
alignedAppendSplitAnchorClassify
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest) right
  (AlignedStep action tag checked (appendTransitions rest right) alignedTail) =
    case alignedAppendSplitAnchorClassify rest right alignedTail of
      (leftAligned, rightAligned) =>
        (AlignedStep action tag checked rest leftAligned, rightAligned)

0 appendOccurrenceAtTarget :
  (earlier : Transitions initial before) ->
  (transition : Transition before afterState) ->
  (suffix : Transitions afterState finalState) ->
  (global : Transitions initial finalState) ->
  appendTransitions earlier (MoreTransitions transition suffix) = global ->
  appendTransitions
    (appendTransitions earlier (MoreTransitions transition NoTransitions))
    suffix = global
appendOccurrenceAtTarget earlier transition suffix global decomposition =
  trans
    (appendTransitionsAssociative earlier
      (MoreTransitions transition NoTransitions) suffix)
    decomposition

||| Action-specific construction of the installed point for one exact retained
||| occurrence.  Orchestration cases are eliminated by `isLifecycleAction`;
||| every lifecycle branch uses its checked evaluator boundary theorem.
public export
0 foreignLifecycleOccurrenceInstalledAnchor :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (action : Action name key value world error) ->
  actionOwner action = actor ->
  isLifecycleAction action = True ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action stepBefore =
    Just (tag, stepAfter)) ->
  (global : Transitions initial finalState) ->
  OccursIn (Fired {before = stepBefore} {afterState = stepAfter}
    nameEq keyEq action tag checked) global ->
  ForeignLifecycleInstalledAnchor name key world error value nameEq keyEq actor
    (Fired {before = stepBefore} {afterState = stepAfter}
      nameEq keyEq action tag checked) global
foreignLifecycleOccurrenceInstalledAnchor nameEq keyEq actor
  (OInsert owner parent component) ownerSame lifecycle tag checked global occurs =
    case lifecycle of Refl impossible
foreignLifecycleOccurrenceInstalledAnchor nameEq keyEq actor
  (ORetire owner) ownerSame lifecycle tag checked global occurs =
    case lifecycle of Refl impossible
foreignLifecycleOccurrenceInstalledAnchor nameEq keyEq actor
  (ORemove owner) ownerSame lifecycle tag checked global occurs =
    case lifecycle of Refl impossible
foreignLifecycleOccurrenceInstalledAnchor nameEq keyEq actor
  (LBegin actor) Refl lifecycle tag checked global occurs =
    case locateTransitionOccurrence (Fired nameEq keyEq (LBegin actor) tag checked)
      global occurs of
      MkLocatedTransitionOccurrence earlier suffix decomposition =>
        case lBeginBoundary nameEq keyEq actor _ _ tag checked of
          (tagShape, sourceUninstalled, targetInstalled) =>
            MkForeignLifecycleInstalledAnchor _
              (appendTransitions earlier
                (MoreTransitions
                  (Fired nameEq keyEq (LBegin actor) tag checked) NoTransitions))
              suffix targetInstalled Refl
              (appendOccurrenceAtTarget earlier
                (Fired nameEq keyEq (LBegin actor) tag checked) suffix global
                decomposition)
foreignLifecycleOccurrenceInstalledAnchor nameEq keyEq actor
  (LAdvance actor) Refl lifecycle tag checked global occurs =
    case locateTransitionOccurrence
      (Fired nameEq keyEq (LAdvance actor) tag checked) global occurs of
      MkLocatedTransitionOccurrence earlier suffix decomposition =>
        let 0 raw = checkedActionProjects nameEq keyEq (LAdvance actor) _ _ tag
              checked
            0 sourceInstalled = lAdvanceStartsInstalled nameEq keyEq actor _ _
              tag raw
        in MkForeignLifecycleInstalledAnchor _ earlier
          (MoreTransitions (Fired nameEq keyEq (LAdvance actor) tag checked)
            suffix)
          sourceInstalled Refl decomposition
foreignLifecycleOccurrenceInstalledAnchor nameEq keyEq actor
  (LDivert actor) Refl lifecycle tag checked global occurs =
    case locateTransitionOccurrence
      (Fired nameEq keyEq (LDivert actor) tag checked) global occurs of
      MkLocatedTransitionOccurrence earlier suffix decomposition =>
        let 0 raw = checkedActionProjects nameEq keyEq (LDivert actor) _ _ tag
              checked
            0 evolution = installationEvolutionStep nameEq keyEq actor
              (LDivert actor) tag _ _ checked
        in case evolution of
          RemainedInstalled sourceInstalled targetInstalled =>
            MkForeignLifecycleInstalledAnchor _ earlier
              (MoreTransitions (Fired nameEq keyEq (LDivert actor) tag checked)
                suffix)
              sourceInstalled Refl decomposition
          RemainedUninstalled sourceUninstalled targetUninstalled =>
            case successfulLDivertTag nameEq keyEq actor _ _ tag raw of
              Refl => case lDivertInstalled nameEq keyEq actor _ _ raw of
                (sourceInstalled, targetInstalled) =>
                  void (falseNotTrueAnchorClassify
                    (trans (sym sourceUninstalled) sourceInstalled))
foreignLifecycleOccurrenceInstalledAnchor nameEq keyEq actor
  (LLeave actor) Refl lifecycle tag checked global occurs =
    case locateTransitionOccurrence
      (Fired nameEq keyEq (LLeave actor) tag checked) global occurs of
      MkLocatedTransitionOccurrence earlier suffix decomposition =>
        let 0 raw = checkedActionProjects nameEq keyEq (LLeave actor) _ _ tag
              checked
            0 sourceInstalled = fst
              (lLeaveInstalled nameEq keyEq actor _ _ tag raw)
        in MkForeignLifecycleInstalledAnchor _ earlier
          (MoreTransitions (Fired nameEq keyEq (LLeave actor) tag checked)
            suffix)
          sourceInstalled Refl decomposition
foreignLifecycleOccurrenceInstalledAnchor nameEq keyEq actor
  (LUnload actor) Refl lifecycle tag checked global occurs =
    case locateTransitionOccurrence
      (Fired nameEq keyEq (LUnload actor) tag checked) global occurs of
      MkLocatedTransitionOccurrence earlier suffix decomposition =>
        let 0 raw = checkedActionProjects nameEq keyEq (LUnload actor) _ _ tag
              checked
            0 sourceInstalled = fst (snd
              (lUnloadBoundary nameEq keyEq actor _ _ tag raw))
        in MkForeignLifecycleInstalledAnchor _ earlier
          (MoreTransitions (Fired nameEq keyEq (LUnload actor) tag checked)
            suffix)
          sourceInstalled Refl decomposition

||| The trace-level join: locate the occurrence, select its action-specific
||| installed point, split aligned evidence there, and classify the *current
||| activation* by its first future close.  In particular, a later installed
||| endpoint never licenses the unsound inference that this episode stayed open.
public export
0 classifyForeignLifecycleOccurrence :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (action : Action name key value world error) ->
  actionOwner action = actor ->
  isLifecycleAction action = True ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action stepBefore =
    Just (tag, stepAfter)) ->
  (global : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  OccursIn (Fired {before = stepBefore} {afterState = stepAfter}
    nameEq keyEq action tag checked) global ->
  (anchor : ForeignLifecycleInstalledAnchor name key world error value nameEq
      keyEq actor
      (Fired {before = stepBefore} {afterState = stepAfter}
        nameEq keyEq action tag checked) global **
    InstalledContinuation name key world error value nameEq keyEq actor
      (lifecycleAfterInstalled anchor))
classifyForeignLifecycleOccurrence nameEq keyEq actor action owner lifecycle tag
  checked global aligned occurs =
    let anchor = foreignLifecycleOccurrenceInstalledAnchor nameEq keyEq actor
          action owner lifecycle tag checked global occurs
        alignedAtAnchor : AlignedTransitions name key world error value nameEq
          keyEq
          (appendTransitions (lifecycleBeforeInstalled anchor)
            (lifecycleAfterInstalled anchor))
        alignedAtAnchor = rewrite lifecycleAnchorDecomposition anchor in aligned
        0 alignedParts :
          (AlignedTransitions name key world error value nameEq keyEq
            (lifecycleBeforeInstalled anchor),
           AlignedTransitions name key world error value nameEq keyEq
            (lifecycleAfterInstalled anchor))
        alignedParts = alignedAppendSplitAnchorClassify
          (lifecycleBeforeInstalled anchor)
          (lifecycleAfterInstalled anchor) alignedAtAnchor
    in (anchor ** classifyInstalledContinuation nameEq keyEq actor
      (lifecycleAfterInstalled anchor) (snd alignedParts)
      (lifecycleAnchorInstalled anchor))

0 spanningOccurrenceDecomposition :
  (beforeOpening : Transitions initial preStart) ->
  (opening : BeginStep nameEq keyEq actor preStart opened) ->
  (afterOpening : Transitions opened anchorState) ->
  (beforeClosing : Transitions anchorState closeBefore) ->
  (closing : UnloadStep nameEq keyEq actor closeBefore closeAfter) ->
  (afterClosing : Transitions closeAfter finalState) ->
  (leftTrace : Transitions initial anchorState) ->
  (rightTrace : Transitions anchorState finalState) ->
  appendTransitions beforeOpening
    (MoreTransitions (beginTransition opening) afterOpening) = leftTrace ->
  appendTransitions beforeClosing
    (MoreTransitions (unloadTransition closing) afterClosing) = rightTrace ->
  appendTransitions beforeOpening
    (MoreTransitions (beginTransition opening)
      (appendTransitions (appendTransitions afterOpening beforeClosing)
        (MoreTransitions (unloadTransition closing) afterClosing))) =
  appendTransitions leftTrace rightTrace
spanningOccurrenceDecomposition beforeOpening opening afterOpening beforeClosing
  closing afterClosing leftTrace rightTrace openingSplit closingSplit =
    rewrite appendTransitionsAssociative afterOpening beforeClosing
      (MoreTransitions (unloadTransition closing) afterClosing) in
    rewrite closingSplit in
    rewrite sym (appendTransitionsAssociative beforeOpening
      (MoreTransitions (beginTransition opening) afterOpening) rightTrace) in
    rewrite openingSplit in Refl

||| A closing activation located around the installed anchor chosen for one
||| lifecycle occurrence.  In addition to the public located episode, this
||| retains the installed prefix from the activation's L-Begin target to the
||| occurrence anchor; crossing-activation exclusion needs precisely this
||| prefix to transport the committed provider observation backwards.
public export
record LocatedClosingActivationAtAnchor
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (actor : name)
  {initial, finalState, stepBefore, stepAfter :
    SystemState name key value world error}
  (transition : Transition stepBefore stepAfter)
  (global : Transitions initial finalState)
  (anchor : ForeignLifecycleInstalledAnchor name key world error value nameEq
    keyEq actor transition global) where
  constructor MkLocatedClosingActivationAtAnchor
  closingActivationEpisode : LocatedClosedEpisode name key world error value
    nameEq keyEq actor global
  activationToOccurrenceAnchor : Transitions
    (closedStartState (locatedEpisode closingActivationEpisode))
    (lifecycleInstalledState anchor)
  0 activationToOccurrenceInstalled : InstalledTrace name key world error value
    nameEq keyEq actor activationToOccurrenceAnchor

||| Promote a first-close result while retaining the exact activation prefix.
public export
0 closingOccurrenceGivesLocatedActivation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (transition : Transition stepBefore stepAfter) ->
  (global : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  bindings (registry initial) = [] ->
  (anchor : ForeignLifecycleInstalledAnchor name key world error value nameEq
    keyEq actor transition global) ->
  FirstClosingResult name key world error value nameEq keyEq actor
    (lifecycleAfterInstalled anchor) ->
  LocatedClosingActivationAtAnchor name key world error value nameEq keyEq actor
    transition global anchor
closingOccurrenceGivesLocatedActivation nameEq keyEq actor transition global
  aligned initialEmpty anchor
  (MkFirstClosingResult closeBefore closeAfter beforeClosing installedBefore
    closing afterClosing closingSplit) =
    let 0 alignedAtAnchor : AlignedTransitions name key world error value nameEq
          keyEq
          (appendTransitions (lifecycleBeforeInstalled anchor)
            (lifecycleAfterInstalled anchor))
        alignedAtAnchor = rewrite lifecycleAnchorDecomposition anchor in aligned
        0 alignedParts :
          (AlignedTransitions name key world error value nameEq keyEq
            (lifecycleBeforeInstalled anchor),
           AlignedTransitions name key world error value nameEq keyEq
            (lifecycleAfterInstalled anchor))
        alignedParts = alignedAppendSplitAnchorClassify
          (lifecycleBeforeInstalled anchor)
          (lifecycleAfterInstalled anchor) alignedAtAnchor
        0 initialUninstalled : installedAt @{nameEq} actor initial = False
        initialUninstalled = emptyRegistryUninstalled nameEq actor initial
          initialEmpty
    in case extractLastOpening nameEq keyEq actor
      (lifecycleBeforeInstalled anchor) (fst alignedParts) initialUninstalled
      (lifecycleAnchorInstalled anchor) of
      MkLastOpeningResult preStart opened beforeOpening opening afterOpening
        openingSplit installedAfterOpening =>
          let 0 insideInstalled = appendInstalledTrace afterOpening beforeClosing
                installedAfterOpening installedBefore
              0 decompositionForAppend = spanningOccurrenceDecomposition
                beforeOpening opening afterOpening beforeClosing closing
                afterClosing (lifecycleBeforeInstalled anchor)
                (lifecycleAfterInstalled anchor) openingSplit closingSplit
              0 locatedDecomposition = trans
                (rewrite appendTransitionsAssociative
                  (appendTransitions afterOpening beforeClosing)
                  (MoreTransitions (unloadTransition closing) NoTransitions)
                  afterClosing in decompositionForAppend)
                (lifecycleAnchorDecomposition anchor)
          in MkLocatedClosingActivationAtAnchor
            (MkLocatedClosedEpisode preStart closeAfter beforeOpening
              (MkClosedEpisode opened closeBefore opening
                (appendTransitions afterOpening beforeClosing) insideInstalled
                closing)
              afterClosing locatedDecomposition)
            afterOpening installedAfterOpening

||| A closing result is promoted to the exact located episode containing this
||| occurrence.  The first-close classifier makes this valid even when the same
||| raw name is later removed, reinserted, or activated again.
public export
0 closingOccurrenceGivesLocatedEpisode :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (transition : Transition stepBefore stepAfter) ->
  (global : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  bindings (registry initial) = [] ->
  (anchor : ForeignLifecycleInstalledAnchor name key world error value nameEq
    keyEq actor transition global) ->
  FirstClosingResult name key world error value nameEq keyEq actor
    (lifecycleAfterInstalled anchor) ->
  LocatedClosedEpisode name key world error value nameEq keyEq actor global
closingOccurrenceGivesLocatedEpisode nameEq keyEq actor transition global aligned
  initialEmpty anchor
  (MkFirstClosingResult closeBefore closeAfter beforeClosing installedBefore
    closing afterClosing closingSplit) =
    let 0 alignedAtAnchor : AlignedTransitions name key world error value nameEq
          keyEq
          (appendTransitions (lifecycleBeforeInstalled anchor)
            (lifecycleAfterInstalled anchor))
        alignedAtAnchor = rewrite lifecycleAnchorDecomposition anchor in aligned
        0 alignedParts :
          (AlignedTransitions name key world error value nameEq keyEq
            (lifecycleBeforeInstalled anchor),
           AlignedTransitions name key world error value nameEq keyEq
            (lifecycleAfterInstalled anchor))
        alignedParts = alignedAppendSplitAnchorClassify
          (lifecycleBeforeInstalled anchor)
          (lifecycleAfterInstalled anchor) alignedAtAnchor
        0 initialUninstalled : installedAt @{nameEq} actor initial = False
        initialUninstalled = emptyRegistryUninstalled nameEq actor initial
          initialEmpty
    in case extractLastOpening nameEq keyEq actor
      (lifecycleBeforeInstalled anchor) (fst alignedParts) initialUninstalled
      (lifecycleAnchorInstalled anchor) of
      MkLastOpeningResult preStart opened beforeOpening opening afterOpening
        openingSplit installedAfterOpening =>
          let 0 insideInstalled : InstalledTrace name key world error value
                nameEq keyEq actor
                (appendTransitions afterOpening beforeClosing)
              insideInstalled = appendInstalledTrace afterOpening beforeClosing
                installedAfterOpening installedBefore
              0 decompositionForAppend :
                (appendTransitions beforeOpening
                  (MoreTransitions (beginTransition opening)
                    (appendTransitions
                      (appendTransitions afterOpening beforeClosing)
                      (MoreTransitions (unloadTransition closing) afterClosing))) =
                 appendTransitions (lifecycleBeforeInstalled anchor)
                   (lifecycleAfterInstalled anchor))
              decompositionForAppend = spanningOccurrenceDecomposition
                beforeOpening opening afterOpening beforeClosing closing
                afterClosing (lifecycleBeforeInstalled anchor)
                (lifecycleAfterInstalled anchor) openingSplit closingSplit
              0 locatedDecomposition :
                (appendTransitions beforeOpening
                  (MoreTransitions (beginTransition opening)
                    (appendTransitions
                      (appendTransitions
                        (appendTransitions afterOpening beforeClosing)
                        (MoreTransitions (unloadTransition closing) NoTransitions))
                      afterClosing)) = global)
              locatedDecomposition = trans
                (rewrite appendTransitionsAssociative
                  (appendTransitions afterOpening beforeClosing)
                  (MoreTransitions (unloadTransition closing) NoTransitions)
                  afterClosing in decompositionForAppend)
                (lifecycleAnchorDecomposition anchor)
          in MkLocatedClosedEpisode preStart closeAfter beforeOpening
            (MkClosedEpisode opened closeBefore opening
              (appendTransitions afterOpening beforeClosing) insideInstalled
              closing)
            afterClosing locatedDecomposition

0 boolOrFalseLeftAnchorClassify :
  (left, right : Bool) -> left || right = False -> left = False
boolOrFalseLeftAnchorClassify False right same = Refl
boolOrFalseLeftAnchorClassify True right same = case same of Refl impossible

0 boolOrFalseRightAnchorClassify :
  (left, right : Bool) -> left || right = False -> right = False
boolOrFalseRightAnchorClassify False right same = same
boolOrFalseRightAnchorClassify True right same = case same of Refl impossible

0 installedTraceEndAnchorClassify :
  (trace : Transitions first finalState) ->
  InstalledTrace name key world error value nameEq keyEq actor trace ->
  installedAt @{nameEq} actor finalState = True
installedTraceEndAnchorClassify NoTransitions (InstalledEnd installed) = installed
installedTraceEndAnchorClassify
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
  (InstalledStep action tag checked rest sourceInstalled tailInstalled) =
    installedTraceEndAnchorClassify rest tailInstalled

0 installedFiberAtAnchorClassify :
  (nameEq : DecEq name) -> (actor : name) ->
  (state : SystemState name key value world error) ->
  installedAt @{nameEq} actor state = True ->
  (fiber : Fiber name key value world error **
    lookupFiber @{nameEq} actor (registry state) = Just fiber)
installedFiberAtAnchorClassify nameEq actor state installed
  with (lookupFiber @{nameEq} actor (registry state)) proof found
  installedFiberAtAnchorClassify nameEq actor state installed | Nothing =
    case installed of Refl impossible
  installedFiberAtAnchorClassify nameEq actor state installed | Just fiber =
    (fiber ** Refl)

0 reliedHeadAtLookupFalse :
  (nameEq : DecEq name) -> (provider, actor : name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (fiber : Fiber name key value world error) ->
  lookupEntries @{nameEq} actor entries = Just fiber ->
  reliedOnBy @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provider provider entries = False ->
  reliedHead @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provider provider
    (Bind actor fiber) = False
reliedHeadAtLookupFalse nameEq provider actor [] fiber found totalFalse =
  case found of Refl impossible
reliedHeadAtLookupFalse nameEq provider actor
  (Bind current observed :: rest) fiber found totalFalse
  with (decEq @{nameEq} actor current)
  reliedHeadAtLookupFalse nameEq provider current
    (Bind current observed :: rest) fiber found totalFalse | Yes Refl =
      case justInjective found of
        Refl => boolOrFalseLeftAnchorClassify
          (reliedHead @{nameEq} provider provider (Bind current observed))
          (reliedOnBy @{nameEq} provider provider rest) totalFalse
  reliedHeadAtLookupFalse nameEq provider actor
    (Bind current observed :: rest) fiber found totalFalse | No distinct =
      reliedHeadAtLookupFalse nameEq provider actor rest fiber found
        (boolOrFalseRightAnchorClassify
          (reliedHead @{nameEq} provider provider (Bind current observed))
          (reliedOnBy @{nameEq} provider provider rest) totalFalse)

||| The later-reactivation/raw-name-reuse branch is anchored at the selected
||| episode's own L-Unload source, not at the raw final endpoint.  It records the
||| exact surviving owner cell and the L-Unload reliance guard which says that
||| this still-installed activation cannot commit to the selected provider.
public export
record SelectedUnloadRelianceAnchor
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (selected, actor : name)
  {selectedPre, selectedAfter, current :
    SystemState name key value world error}
  (episode : ClosedEpisode name key world error value nameEq keyEq selected
    selectedPre selectedAfter)
  (currentOwner : Fiber name key value world error) where
  constructor MkSelectedUnloadRelianceAnchor
  selectedUnloadOwner : Fiber name key value world error
  0 selectedUnloadOwnerFound :
    lookupFiber @{nameEq} actor
      (registry (lastInstalledState episode)) = Just selectedUnloadOwner
  0 selectedUnloadOwnerComponent :
    fiberComponent selectedUnloadOwner = fiberComponent currentOwner
  0 selectedUnloadOwnerDoesNotRely :
    reliedHead @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} selected selected
      (Bind actor selectedUnloadOwner) = False

||| Build the critical reliance anchor whenever the retained foreign activation
||| stays installed from the occurrence boundary through the selected close.
||| No statement about the selected raw name in the global endpoint is made.
public export
0 selectedUnloadRelianceAnchorFromInstalledTrace :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) ->
  (episode : ClosedEpisode name key world error value nameEq keyEq selected
    selectedPre selectedAfter) ->
  (current : SystemState name key value world error) ->
  (toSelectedClose : Transitions current (lastInstalledState episode)) ->
  InstalledTrace name key world error value nameEq keyEq actor toSelectedClose ->
  (currentOwner : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor (registry current) = Just currentOwner ->
  SelectedUnloadRelianceAnchor name key world error value nameEq keyEq selected
    actor episode currentOwner
selectedUnloadRelianceAnchorFromInstalledTrace nameEq keyEq selected actor
  episode current toSelectedClose ownerInstalled currentOwner currentOwnerFound =
    case installedFiberAtAnchorClassify nameEq actor
      (lastInstalledState episode)
      (installedTraceEndAnchorClassify toSelectedClose ownerInstalled) of
      (closingOwner ** closingOwnerFound) =>
        let 0 selectedNotRelied :
              (relied @{nameEq} {name = name} {key = key} {value = value}
                {world = world} {error = error} selected
                (registry (lastInstalledState episode)) = False)
            selectedNotRelied = unloadGuardTheorem nameEq keyEq selected
              (lastInstalledState episode) selectedAfter (closing episode)
            0 closingHeadFalse :
              (reliedHead @{nameEq} {name = name} {key = key} {value = value}
                {world = world} {error = error} selected selected
                (Bind actor closingOwner) = False)
            closingHeadFalse = reliedHeadAtLookupFalse nameEq selected actor
              (bindings (registry (lastInstalledState episode))) closingOwner
              (lookupFiberEntries nameEq actor closingOwner
                (registry (lastInstalledState episode)) closingOwnerFound)
              selectedNotRelied
        in MkSelectedUnloadRelianceAnchor closingOwner closingOwnerFound
          (installedTracePreservesComponent nameEq keyEq actor toSelectedClose
            ownerInstalled currentOwner closingOwner currentOwnerFound
            closingOwnerFound)
          closingHeadFalse
