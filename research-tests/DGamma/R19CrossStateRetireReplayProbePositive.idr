module DGamma.R19CrossStateRetireReplayProbePositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Metatheory
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionFrameRetire
import DGamma.CP5ConfluenceLocalDiamondSpike
import Data.Nat
import Decidable.Equality

%default total

0 relatedEffectsSymmetric :
  EffectStateRelated keyEq left right -> EffectStateRelated keyEq right left
relatedEffectsSymmetric (MkEffectStateRelated ambient tables) =
  MkEffectStateRelated (sym ambient) (\selected => sym (tables selected))

0 relatedEffectsTransitive :
  EffectStateRelated keyEq first middle ->
  EffectStateRelated keyEq middle finalState ->
  EffectStateRelated keyEq first finalState
relatedEffectsTransitive (MkEffectStateRelated firstAmbient firstTables)
  (MkEffectStateRelated secondAmbient secondTables) =
    MkEffectStateRelated (trans firstAmbient secondAmbient)
      (\selected => trans (firstTables selected) (secondTables selected))

0 retireFiberControlRelated :
  FiberControlRelated left right ->
  FiberControlRelated (retireFiber left) (retireFiber right)
retireFiberControlRelated
  (FibersControlRelated {component} leftParent rightParent leftRetired rightRetired
    leftTable rightTable leftLifecycle rightLifecycle parentSame retiredSame
    lifecycleSame) =
      FibersControlRelated {component = component} leftParent rightParent True True
        leftTable rightTable
        leftLifecycle rightLifecycle parentSame Refl lifecycleSame

0 someNoControlImpossible :
  FiberControlMaybeRelated (Just fiber) Nothing -> Void
someNoControlImpossible relation impossible

0 controlEquivalentLookupFound :
  (nameEq : DecEq name) ->
  (actor : name) ->
  (left, right : SystemState name key value world error) ->
  ControlEquivalent name key world error value nameEq left right ->
  (leftFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor (registry left) = Just leftFiber ->
  (rightFiber : Fiber name key value world error **
    (lookupFiber @{nameEq} actor (registry right) = Just rightFiber,
     FiberControlRelated leftFiber rightFiber))
controlEquivalentLookupFound nameEq actor left right controls leftFiber leftFound
  with (lookupFiber @{nameEq} actor (registry right)) proof rightFound
  controlEquivalentLookupFound nameEq actor left right controls leftFiber
    leftFound | Nothing =
      let 0 leftRelation : FiberControlMaybeRelated (Just leftFiber)
              (lookupFiber @{nameEq} actor (registry right))
          leftRelation = replace
            {p = \observed => FiberControlMaybeRelated observed
              (lookupFiber @{nameEq} actor (registry right))}
            leftFound (controlPointwise controls actor)
          0 relation : FiberControlMaybeRelated (Just leftFiber) Nothing
          relation = replace
            {p = \observed => FiberControlMaybeRelated (Just leftFiber) observed}
            rightFound leftRelation
      in void (someNoControlImpossible relation)
  controlEquivalentLookupFound nameEq actor left right controls leftFiber
    leftFound | Just rightFiber =
      let 0 leftRelation : FiberControlMaybeRelated (Just leftFiber)
              (lookupFiber @{nameEq} actor (registry right))
          leftRelation = replace
            {p = \observed => FiberControlMaybeRelated observed
              (lookupFiber @{nameEq} actor (registry right))}
            leftFound (controlPointwise controls actor)
          0 relation : FiberControlMaybeRelated (Just leftFiber)
              (Just rightFiber)
          relation = replace
            {p = \observed => FiberControlMaybeRelated (Just leftFiber) observed}
            rightFound leftRelation
      in case relation of
        SomeControlFibers fibersRelated =>
          (rightFiber ** (Refl, fibersRelated))

0 controlEquivalentAfterRelatedRetire :
  (nameEq : DecEq name) ->
  (actor : name) ->
  (leftWorld, rightWorld : world) ->
  (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftFiber, rightFiber : Fiber name key value world error) ->
  (leftFound : lookupFiber @{nameEq} actor leftRegistry = Just leftFiber) ->
  (rightFound : lookupFiber @{nameEq} actor rightRegistry = Just rightFiber) ->
  FiberControlRelated leftFiber rightFiber ->
  ControlEquivalent name key world error value nameEq
    (MkSystemState leftWorld leftRegistry)
    (MkSystemState rightWorld rightRegistry) ->
  ControlEquivalent name key world error value nameEq
    (MkSystemState leftWorld
      (the (Registry name key value world error)
        (replaceBinding @{nameEq} actor (retireFiber leftFiber) leftRegistry)))
    (MkSystemState rightWorld
      (the (Registry name key value world error)
        (replaceBinding @{nameEq} actor (retireFiber rightFiber) rightRegistry)))
controlEquivalentAfterRelatedRetire nameEq actor leftWorld rightWorld leftRegistry
  rightRegistry leftFiber rightFiber leftFound rightFound fibersRelated controls =
    MkControlEquivalent pointwise
  where
  0 pointwise : (selected : name) -> FiberControlMaybeRelated
    {name = name} {key = key} {value = value} {world = world} {error = error}
    (lookupFiber @{nameEq} selected
      (the (Registry name key value world error)
        (replaceBinding @{nameEq} actor (retireFiber leftFiber) leftRegistry)))
    (lookupFiber @{nameEq} selected
      (the (Registry name key value world error)
        (replaceBinding @{nameEq} actor (retireFiber rightFiber) rightRegistry)))
  pointwise selected with (decEq @{nameEq} selected actor)
    pointwise selected | Yes same = case same of
      Refl => rewrite lookupReplacedFiber actor leftFiber (retireFiber leftFiber)
        leftRegistry leftFound in
        rewrite lookupReplacedFiber actor rightFiber (retireFiber rightFiber)
          rightRegistry rightFound in
            SomeControlFibers (retireFiberControlRelated fibersRelated)
    pointwise selected | No distinct =
      rewrite lookupReplaceOther selected actor distinct (retireFiber leftFiber)
        leftRegistry in
      rewrite lookupReplaceOther selected actor distinct (retireFiber rightFiber)
        rightRegistry in controlPointwise controls selected

0 retireSourceIngredients :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (ambient : world) ->
  (source : Registry name key value world error) ->
  (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (ORetire actor)
    (MkSystemState ambient source) = Just (ORetireTag, afterState) ->
  (oldFiber : Fiber name key value world error **
    (lookupFiber @{nameEq} actor source = Just oldFiber,
     MkSystemState ambient
       (replaceBinding @{nameEq} actor (retireFiber oldFiber) source) =
       afterState))
retireSourceIngredients nameEq keyEq actor ambient source afterState raw =
  case retireSuccessView nameEq keyEq actor ambient source ORetireTag afterState
    raw of
    MkRetireSuccessView oldFiber found => (oldFiber ** (found, Refl))

0 retireFrameRelated :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (ORetire actor) before =
    Just (ORetireTag, afterState) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} before)
    (projectEffectState @{nameEq} afterState)
retireFrameRelated nameEq keyEq actor before afterState raw =
  case retireActualEffectFrame nameEq keyEq actor before afterState ORetireTag raw of
    MkActualEffectFrame (PartialDefined related) => related

0 oneNodePrefixTooLong :
  (prefixStep : Transition first point) ->
  (prefixRest : Transitions point beforeLocated) ->
  (located : Transition beforeLocated afterLocated) ->
  (suffix : Transitions afterLocated finalState) ->
  (only : Transition first finalState) ->
  appendTransitions (MoreTransitions prefixStep prefixRest)
    (MoreTransitions located suffix) = MoreTransitions only NoTransitions -> Void
oneNodePrefixTooLong prefixStep prefixRest located suffix only decomposition =
  appendedTraceCountNonZero prefixRest located suffix
    (succCountInjective (cong transitionCount decomposition))
  where
  0 succCountInjective : S count = S Z -> count = Z
  succCountInjective Refl = Refl

  0 appendedTraceCountNonZero :
    {start, splitPoint, afterStep, end :
      SystemState name key value world error} ->
    (tracePrefix : Transitions start splitPoint) ->
    (step : Transition splitPoint afterStep) ->
    (rest : Transitions afterStep end) ->
    transitionCount (appendTransitions tracePrefix
      (MoreTransitions step rest)) = Z -> Void
  appendedTraceCountNonZero NoTransitions step rest Refl impossible
  appendedTraceCountNonZero (MoreTransitions head tail) step rest Refl impossible

0 singletonRetireActionOrigin :
  (source : Transition sourceBefore sourceAfter) ->
  (replayed : Transition replayedBefore replayedAfter) ->
  transitionAction source = ORetire actor ->
  transitionAction replayed = ORetire actor ->
  (occurrence : LocatedActionOccurrence action
    (MoreTransitions replayed NoTransitions)) ->
  LocatedActionOccurrence action (MoreTransitions source NoTransitions)
singletonRetireActionOrigin source replayed sourceAction replayedAction
  (MkLocatedActionOccurrence before after NoTransitions replayed NoTransitions
    same Refl) =
      MkLocatedActionOccurrence _ _ NoTransitions source NoTransitions
        (trans sourceAction (trans (sym replayedAction) same)) Refl
singletonRetireActionOrigin source replayed sourceAction replayedAction
  (MkLocatedActionOccurrence before after (MoreTransitions prefixStep prefixRest)
    located suffix same decomposition) =
      void (oneNodePrefixTooLong prefixStep prefixRest located suffix replayed
        decomposition)

0 singletonRetireTagPreserved :
  (source : Transition sourceBefore sourceAfter) ->
  (replayed : Transition replayedBefore replayedAfter) ->
  (sourceAction : transitionAction source = ORetire actor) ->
  (replayedAction : transitionAction replayed = ORetire actor) ->
  transitionTag source = ORetireTag ->
  transitionTag replayed = ORetireTag ->
  (occurrence : LocatedActionOccurrence action
    (MoreTransitions replayed NoTransitions)) ->
  transitionTag (locatedTransition
    (singletonRetireActionOrigin source replayed sourceAction replayedAction
      occurrence)) = transitionTag (locatedTransition occurrence)
singletonRetireTagPreserved source replayed sourceAction replayedAction sourceTag
  replayedTag
  (MkLocatedActionOccurrence before after NoTransitions replayed NoTransitions
    same Refl) = trans sourceTag (sym replayedTag)
singletonRetireTagPreserved source replayed sourceAction replayedAction sourceTag
  replayedTag
  (MkLocatedActionOccurrence before after (MoreTransitions prefixStep prefixRest)
    located suffix same decomposition) =
      void (oneNodePrefixTooLong prefixStep prefixRest located suffix replayed
        decomposition)

0 singletonRetireOccurrenceAction :
  (replayed : Transition replayedBefore replayedAfter) ->
  (replayedAction : transitionAction replayed = ORetire actor) ->
  (occurrence : LocatedActionOccurrence action
    (MoreTransitions replayed NoTransitions)) ->
  action = ORetire actor
singletonRetireOccurrenceAction replayed replayedAction
  (MkLocatedActionOccurrence before after NoTransitions replayed NoTransitions
    same Refl) = trans (sym same) replayedAction
singletonRetireOccurrenceAction replayed replayedAction
  (MkLocatedActionOccurrence before after (MoreTransitions prefixStep prefixRest)
    located suffix same decomposition) =
      void (oneNodePrefixTooLong prefixStep prefixRest located suffix replayed
        decomposition)

0 singletonRetireNoGenerated :
  (replayed : Transition replayedBefore replayedAfter) ->
  (replayedAction : transitionAction replayed = ORetire actor) ->
  LocatedGeneratedRegistration child parent component
    (MoreTransitions replayed NoTransitions) -> Void
singletonRetireNoGenerated replayed replayedAction generated =
  case singletonRetireOccurrenceAction replayed replayedAction
    (generatedRegistrationActionOccurrence generated) of Refl impossible

0 singletonRetireOccurrenceCorrespondence :
  (source : Transition sourceBefore sourceAfter) ->
  (replayed : Transition replayedBefore replayedAfter) ->
  (sourceAction : transitionAction source = ORetire actor) ->
  (replayedAction : transitionAction replayed = ORetire actor) ->
  (sourceTag : transitionTag source = ORetireTag) ->
  (replayedTag : transitionTag replayed = ORetireTag) ->
  ActionRegistrationReplayCorrespondence name key world error value
    (MoreTransitions source NoTransitions)
    (MoreTransitions replayed NoTransitions)
singletonRetireOccurrenceCorrespondence source replayed sourceAction
  replayedAction sourceTag replayedTag =
    MkActionRegistrationReplayCorrespondence
      identityRegistrationGenerationBijection
      (singletonRetireActionOrigin source replayed sourceAction replayedAction)
      (singletonRetireTagPreserved source replayed sourceAction replayedAction
        sourceTag replayedTag)
      (\generated => void
        (singletonRetireNoGenerated replayed replayedAction generated))
      (\generated => void
        (singletonRetireNoGenerated replayed replayedAction generated))
      (\generated => void
        (singletonRetireNoGenerated replayed replayedAction generated))

0 singletonOccursSelected :
  {selected : Transition selectedBefore selectedAfter} ->
  {only : Transition first finalState} ->
  OccursIn selected (MoreTransitions only NoTransitions) -> selected = only
singletonOccursSelected OccursHere = Refl
singletonOccursSelected (OccursLater occurrence) impossible

0 noIteratorStageInSingletonRetire :
  (replayed : Transition replayedBefore replayedAfter) ->
  transitionAction replayed = ORetire actor ->
  IteratorStage name key world error value selected
    (MoreTransitions replayed NoTransitions) -> Void
noIteratorStageInSingletonRetire replayed replayedAction
  (StageFromAdvance nameEq keyEq selected tag equation occurs fiber found
    remaining accumulator view lifecycle step rest suffix) =
      case singletonOccursSelected occurs of Refl impossible

0 singletonRetireGeneratorOrigin :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) ->
  (sourceBefore, sourceAfter, replayedBefore, replayedAfter :
    SystemState name key value world error) ->
  (sourceChecked : checkedApplyAction @{nameEq} @{keyEq} (ORetire actor)
    sourceBefore = Just (ORetireTag, sourceAfter)) ->
  (replayedChecked : checkedApplyAction @{nameEq} @{keyEq} (ORetire actor)
    replayedBefore = Just (ORetireTag, replayedAfter)) ->
  (selected : name) ->
  TraceEffectGenerator name key world error value selected
    (MoreTransitions
      (Fired {before = replayedBefore} {afterState = replayedAfter} nameEq keyEq
              (ORetire actor) ORetireTag replayedChecked)
      NoTransitions) ->
  TraceEffectGenerator name key world error value selected
    (MoreTransitions
      (Fired {before = sourceBefore} {afterState = sourceAfter} nameEq keyEq
              (ORetire actor) ORetireTag sourceChecked)
      NoTransitions)
singletonRetireGeneratorOrigin nameEq keyEq actor sourceBefore sourceAfter
  replayedBefore replayedAfter sourceChecked replayedChecked selected
  (ActualForwardGenerator before afterState storedNameEq storedKeyEq action tag
    checked occurs actorMatches) = case singletonOccursSelected occurs of
      Refl => ActualForwardGenerator sourceBefore sourceAfter nameEq keyEq
        (ORetire actor) ORetireTag sourceChecked OccursHere actorMatches
singletonRetireGeneratorOrigin nameEq keyEq actor sourceBefore sourceAfter
  replayedBefore replayedAfter sourceChecked replayedChecked selected
  (IteratorForwardGenerator stage) =
    void (noIteratorStageInSingletonRetire
      (Fired {before = replayedBefore} {afterState = replayedAfter} nameEq keyEq
              (ORetire actor) ORetireTag replayedChecked) Refl stage)
singletonRetireGeneratorOrigin nameEq keyEq actor sourceBefore sourceAfter
  replayedBefore replayedAfter sourceChecked replayedChecked selected
  (IteratorYieldedGenerator stage state) =
    void (noIteratorStageInSingletonRetire
      (Fired {before = replayedBefore} {afterState = replayedAfter} nameEq keyEq
              (ORetire actor) ORetireTag replayedChecked) Refl stage)

0 singletonRetireGeneratorRunsIdentity :
  (retire : Transition before afterState) ->
  (actionExact : transitionAction retire = ORetire actor) ->
  (tagExact : transitionTag retire = ORetireTag) ->
  (generator : TraceEffectGenerator name key world error value selected
    (MoreTransitions retire NoTransitions)) ->
  (state : EffectState name key value world) ->
  traceGeneratorMap generator state = Just state
singletonRetireGeneratorRunsIdentity retire actionExact tagExact
  (ActualForwardGenerator before afterState storedNameEq storedKeyEq action tag
    checked occurs actorMatches) state =
      case singletonOccursSelected occurs of
        Refl => case retire of
          Fired actualNameEq actualKeyEq actualAction actualTag actualChecked =>
            rewrite actionExact in Refl
singletonRetireGeneratorRunsIdentity retire actionExact tagExact
  (IteratorForwardGenerator stage) state =
    void (noIteratorStageInSingletonRetire retire actionExact stage)
singletonRetireGeneratorRunsIdentity retire actionExact tagExact
  (IteratorYieldedGenerator stage origin) state =
    void (noIteratorStageInSingletonRetire retire actionExact stage)

0 singletonRetireRAR :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) ->
  (sourceBefore, sourceAfter, replayedBefore, replayedAfter :
    SystemState name key value world error) ->
  (sourceChecked : checkedApplyAction @{nameEq} @{keyEq} (ORetire actor)
    sourceBefore = Just (ORetireTag, sourceAfter)) ->
  (replayedChecked : checkedApplyAction @{nameEq} @{keyEq} (ORetire actor)
    replayedBefore = Just (ORetireTag, replayedAfter)) ->
  RelationalReplayCorrespondence name key world error value
    (MoreTransitions
      (Fired {before = sourceBefore} {afterState = sourceAfter} nameEq keyEq
              (ORetire actor) ORetireTag sourceChecked)
      NoTransitions)
    (MoreTransitions
      (Fired {before = replayedBefore} {afterState = replayedAfter} nameEq keyEq
              (ORetire actor) ORetireTag replayedChecked)
      NoTransitions)
singletonRetireRAR nameEq keyEq actor sourceBefore sourceAfter replayedBefore
  replayedAfter sourceChecked replayedChecked =
    MkRelationalReplayCorrespondence
      (singletonRetireGeneratorOrigin nameEq keyEq actor sourceBefore sourceAfter
        replayedBefore replayedAfter sourceChecked replayedChecked)
      mapsRelated
      (\selected, stage => void
        (noIteratorStageInSingletonRetire
          (Fired {before = replayedBefore} {afterState = replayedAfter} nameEq keyEq
              (ORetire actor) ORetireTag replayedChecked)
          Refl stage))
      (\selected, stage, state => void
        (noIteratorStageInSingletonRetire
          (Fired {before = replayedBefore} {afterState = replayedAfter} nameEq keyEq
              (ORetire actor) ORetireTag replayedChecked)
          Refl stage))
  where
  0 mapsRelated : (observedKeyEq : DecEq key) -> (selected : name) ->
    (generator : TraceEffectGenerator name key world error value selected
      (MoreTransitions
        (Fired {before = replayedBefore} {afterState = replayedAfter}
          nameEq keyEq (ORetire actor) ORetireTag replayedChecked)
        NoTransitions)) ->
    PartialMapsRelated (EffectStateEquivalence observedKeyEq)
      (traceGeneratorMap
        (singletonRetireGeneratorOrigin nameEq keyEq actor sourceBefore
          sourceAfter replayedBefore replayedAfter sourceChecked replayedChecked
          selected generator))
      (traceGeneratorMap generator)
  mapsRelated observedKeyEq selected generator {x} {y} inputs =
    let 0 exactAtSource : (traceGeneratorMap
          (singletonRetireGeneratorOrigin nameEq keyEq actor sourceBefore
            sourceAfter replayedBefore replayedAfter sourceChecked
            replayedChecked selected generator) x =
          traceGeneratorMap generator x)
        exactAtSource = trans
          (singletonRetireGeneratorRunsIdentity
            (Fired {before = sourceBefore} {afterState = sourceAfter}
              nameEq keyEq (ORetire actor) ORetireTag sourceChecked)
            Refl Refl
            (singletonRetireGeneratorOrigin nameEq keyEq actor sourceBefore
              sourceAfter replayedBefore replayedAfter sourceChecked
              replayedChecked selected generator) x)
          (sym (singletonRetireGeneratorRunsIdentity
            (Fired {before = replayedBefore} {afterState = replayedAfter}
              nameEq keyEq (ORetire actor) ORetireTag replayedChecked)
            Refl Refl generator x))
        0 targetRelated : PartialRelated
          (EffectState name key value world) (EffectStateRelated observedKeyEq)
          (traceGeneratorMap generator x) (traceGeneratorMap generator y)
        targetRelated = replayTraceGeneratorMapRespects observedKeyEq generator
          inputs
    in replace
      {p = \leftOutput => PartialRelated
        (EffectState name key value world)
        (EffectStateRelated observedKeyEq) leftOutput
        (traceGeneratorMap generator y)}
      (sym exactAtSource) targetRelated

public export
record CheckedCrossStateRetireReplay
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (actor : name)
  (sourceBefore, sourceAfter, replayedBefore :
    SystemState name key value world error)
  (sourceChecked : checkedApplyAction @{nameEq} @{keyEq} (ORetire actor)
    sourceBefore = Just (ORetireTag, sourceAfter)) where
  constructor MkCheckedCrossStateRetireReplay
  replayedAfter : SystemState name key value world error
  0 replayedChecked : checkedApplyAction @{nameEq} @{keyEq} (ORetire actor)
    replayedBefore = Just (ORetireTag, replayedAfter)
  replayedTransition : Transition replayedBefore replayedAfter
  0 replayedActionExact : transitionAction replayedTransition = ORetire actor
  0 replayedTagExact : transitionTag replayedTransition = ORetireTag
  0 perStepRAR : RelationalReplayCorrespondence name key world error value
    (MoreTransitions
      (Fired {before = sourceBefore} {afterState = sourceAfter} nameEq keyEq
              (ORetire actor) ORetireTag sourceChecked)
      NoTransitions)
    (MoreTransitions replayedTransition NoTransitions)
  0 perStepEndpoint : RelationalReplayEndpoint name key world error value nameEq
    keyEq sourceAfter replayedAfter
  0 perStepOccurrence : ActionRegistrationReplayCorrespondence name key world
    error value
    (MoreTransitions
      (Fired {before = sourceBefore} {afterState = sourceAfter} nameEq keyEq
              (ORetire actor) ORetireTag sourceChecked)
      NoTransitions)
    (MoreTransitions replayedTransition NoTransitions)
  0 perStepRelativeOrdinal :
    {action : Action name key value world error} ->
    (occurrence : LocatedActionOccurrence action
      (MoreTransitions replayedTransition NoTransitions)) ->
    locatedActionOrdinal occurrence = locatedActionOrdinal
      (replayActionOrigin perStepOccurrence occurrence)

0 produceCheckedCrossStateRetireReplay :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) ->
  (sourceBefore, sourceAfter, replayedBefore :
    SystemState name key value world error) ->
  (sourceChecked : checkedApplyAction @{nameEq} @{keyEq} (ORetire actor)
    sourceBefore = Just (ORetireTag, sourceAfter)) ->
  registryWellFormed @{nameEq} @{keyEq} sourceBefore = True ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} sourceBefore)
    (projectEffectState @{nameEq} replayedBefore) ->
  ControlEquivalent name key world error value nameEq sourceBefore replayedBefore ->
  registryWellFormed @{nameEq} @{keyEq} replayedBefore = True ->
  CheckedCrossStateRetireReplay name key world error value nameEq keyEq actor
    sourceBefore sourceAfter replayedBefore sourceChecked
produceCheckedCrossStateRetireReplay nameEq keyEq actor
  (MkSystemState sourceWorld sourceRegistry) sourceAfter
  (MkSystemState replayedWorld replayedRegistry) sourceChecked
  sourceWellFormed beforeEffects beforeControls replayedWellFormed =
    let 0 sourceState : SystemState name key value world error
        sourceState = MkSystemState sourceWorld sourceRegistry
        0 replayedState : SystemState name key value world error
        replayedState = MkSystemState replayedWorld replayedRegistry
        0 sourceRaw : applyAction @{nameEq} @{keyEq} (ORetire actor)
          sourceState = Just (ORetireTag, sourceAfter)
        sourceRaw = checkedActionProjects nameEq keyEq (ORetire actor)
          sourceState sourceAfter ORetireTag sourceChecked
    in case retireSourceIngredients nameEq keyEq actor sourceWorld sourceRegistry
      sourceAfter sourceRaw of
      (sourceFiber ** (sourceFound, sourceAfterExact)) =>
        case controlEquivalentLookupFound nameEq actor
          sourceState
          replayedState beforeControls
          sourceFiber sourceFound of
          (replayedFiber ** (replayedFound, fibersRelated)) =>
            let targetFiber : Fiber name key value world error
                targetFiber = retireFiber replayedFiber
                targetRegistry : Registry name key value world error
                targetRegistry = replaceBinding @{nameEq} actor targetFiber
                  replayedRegistry
                targetState : SystemState name key value world error
                targetState = MkSystemState replayedWorld targetRegistry
                0 replayedRaw : applyAction @{nameEq} @{keyEq} (ORetire actor)
                  replayedState =
                    Just (ORetireTag, targetState)
                replayedRaw = rewrite replayedFound in Refl
                0 targetWellFormed : registryWellFormed @{nameEq} @{keyEq}
                  targetState = True
                targetWellFormed = preservationTheoremProof nameEq keyEq
                  (ORetire actor)
                  replayedState targetState
                  ORetireTag replayedWellFormed replayedRaw
                0 targetChecked : checkedApplyAction @{nameEq} @{keyEq}
                  (ORetire actor) replayedState =
                    Just (ORetireTag, targetState)
                targetChecked = rewrite replayedRaw in
                  rewrite targetWellFormed in Refl
                0 sourceFrame : EffectStateRelated keyEq
                  (projectEffectState @{nameEq} sourceState)
                  (projectEffectState @{nameEq} sourceAfter)
                sourceFrame = retireFrameRelated nameEq keyEq actor sourceState
                  sourceAfter sourceRaw
                0 replayedFrame : EffectStateRelated keyEq
                  (projectEffectState @{nameEq} replayedState)
                  (projectEffectState @{nameEq} targetState)
                replayedFrame = retireFrameRelated nameEq keyEq actor
                  replayedState targetState
                  replayedRaw
                0 afterEffects : EffectStateRelated keyEq
                  (projectEffectState @{nameEq} sourceAfter)
                  (projectEffectState @{nameEq} targetState)
                afterEffects = relatedEffectsTransitive
                  (relatedEffectsSymmetric sourceFrame)
                  (relatedEffectsTransitive beforeEffects replayedFrame)
                0 afterControlsConcrete : ControlEquivalent name key world error
                  value nameEq
                  (MkSystemState sourceWorld
                    (replaceBinding @{nameEq} actor (retireFiber sourceFiber)
                      sourceRegistry)) targetState
                afterControlsConcrete = controlEquivalentAfterRelatedRetire
                  nameEq actor sourceWorld replayedWorld sourceRegistry
                  replayedRegistry sourceFiber replayedFiber sourceFound
                  replayedFound fibersRelated beforeControls
                0 afterControls : ControlEquivalent name key world error value
                  nameEq sourceAfter targetState
                afterControls = replace
                  {p = \observed => ControlEquivalent name key world error value
                    nameEq observed targetState}
                  sourceAfterExact afterControlsConcrete
                sourceTransition : Transition sourceState sourceAfter
                sourceTransition = Fired nameEq keyEq (ORetire actor) ORetireTag
                  sourceChecked
                targetTransition : Transition replayedState targetState
                targetTransition = Fired nameEq keyEq (ORetire actor) ORetireTag
                  targetChecked
                0 occurrence : ActionRegistrationReplayCorrespondence name key
                  world error value (MoreTransitions sourceTransition NoTransitions)
                  (MoreTransitions targetTransition NoTransitions)
                occurrence = singletonRetireOccurrenceCorrespondence
                  sourceTransition targetTransition Refl Refl Refl Refl
                0 ordinal :
                  (located : LocatedActionOccurrence action
                    (MoreTransitions targetTransition NoTransitions)) ->
                  locatedActionOrdinal located = locatedActionOrdinal
                    (replayActionOrigin occurrence located)
                ordinal
                  (MkLocatedActionOccurrence _ _ NoTransitions _ NoTransitions
                    same Refl) = Refl
                ordinal
                  (MkLocatedActionOccurrence before after
                    (MoreTransitions prefixStep prefixRest) located suffix same
                    decomposition) =
                      void (oneNodePrefixTooLong prefixStep prefixRest located
                        suffix targetTransition decomposition)
            in MkCheckedCrossStateRetireReplay targetState targetChecked
              targetTransition Refl Refl
              (singletonRetireRAR nameEq keyEq actor sourceState sourceAfter
                replayedState targetState sourceChecked targetChecked)
              (MkRelationalReplayEndpoint afterEffects afterControls
                targetWellFormed)
              occurrence ordinal

||| The exact probe requested for revision 19: the source suffix head starts at
||| the local diamond's original final state and is re-evaluated at the distinct
||| swapped-state index.  The moved transition and all per-step proof fields are
||| derived from the diamond endpoint plus the checked source transition.
public export
0 checkedRetireReplayAcrossLocalSwap :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  (sourceAfter : SystemState name key value world error) ->
  (sourceChecked : checkedApplyAction @{nameEq} @{keyEq} (ORetire actor)
    originalFinal = Just (ORetireTag, sourceAfter)) ->
  registryWellFormed @{nameEq} @{keyEq} originalFinal = True ->
  CheckedCrossStateRetireReplay name key world error value nameEq keyEq actor
    originalFinal sourceAfter (swappedFinal diamond) sourceChecked
checkedRetireReplayAcrossLocalSwap nameEq keyEq actor left right diamond sourceAfter
  sourceChecked sourceWellFormed =
    produceCheckedCrossStateRetireReplay nameEq keyEq actor originalFinal
      sourceAfter (swappedFinal diamond) sourceChecked sourceWellFormed
      (swappedEffects diamond) (swappedControlEquivalent diamond)
      (swappedWellFormed diamond)

||| `ReplayInvariantBundle` is a global-from-empty trace package, not a local
||| suffix package.  Any attempt to store it on an empty suffix at a nonempty
||| swapped state immediately contradicts its `replayInitialEmpty` field.  This
||| is the checked bundle-boundary mismatch reached after the per-step replay
||| above succeeds.
public export
0 emptySuffixReplayBundleRequiresEmptyRegistry :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq
    (the (Transitions state state) NoTransitions) ->
  bindings (registry state) = []
emptySuffixReplayBundleRequiresEmptyRegistry protocol nameEq keyEq state bundle =
  replayInitialEmpty bundle
