module DGamma.CP4DeletionSelectedForeignLifecycleAdvanceDispatch

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedForeignLifecycleAdvance
import DGamma.CP4DeletionSelectedForeignLifecycleAdvanceDispatchCore
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import DGamma.CP4DeletionSelectedForeignLifecycleGuards
import DGamma.CP4DeletionSelectedForeignLifecycleReplayCore
import Decidable.Equality

%default total

||| Final control constructor for a retained foreign L-Advance once the
||| occurrence layer has supplied repaired Equation-55 agreement at the two
||| concrete evaluator sources.  The function is exhaustive over empty,
||| failure, finish, iteration, and landing-divert outcomes.  It does not compare
||| erased table certificates or accumulator functions by equality.
public export
0 replayForeignAdvanceControlsFromOutcome :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> Not (actor = selected) ->
  (planAmbient, survivorAmbient : world) ->
  (plan, survivor : Registry name key value world error) ->
  (leftOwner, rightOwner : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor plan = Just leftOwner ->
  lookupFiber @{nameEq} actor survivor = Just rightOwner ->
  (frame : ForeignLifecycleGuardFrame name key world error value nameEq keyEq
    selected actor (dependencies
      (componentDependencies (fiberComponent leftOwner)))
    leftOwner rightOwner plan survivor) ->
  (tag : RuleTag) -> (planAfter : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (LAdvance actor)
    (MkSystemState planAmbient plan) = Just (tag, planAfter) ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (MkSystemState survivorAmbient survivor) = True ->
  ((component : Component key value world error) ->
    (leftTable, rightTable : OwnedTable key value
      (componentProvisions component)) ->
    (step : StepEffect key value world error
      (dependencies (componentDependencies component))
      (componentProvisions component)) ->
    (rest : List (StepEffect key value world error
      (dependencies (componentDependencies component))
      (componentProvisions component))) ->
    (view : View name (dependencies (componentDependencies component))) ->
    IteratorOutcomeAgreement name key value world error keyEq
      (runtimeAdvanceOutcome nameEq keyEq actor component step rest view
        survivorAmbient rightTable survivor)
      (runtimeAdvanceOutcome nameEq keyEq actor component step rest view
        planAmbient leftTable plan)) ->
  ForeignLifecycleControlReplay name key world error value nameEq keyEq
    selected (LAdvance actor) tag planAfter
    (MkSystemState survivorAmbient survivor)
replayForeignAdvanceControlsFromOutcome {name} {key} {world} {error} {value}
  nameEq keyEq selected actor actorDistinct planAmbient survivorAmbient plan
  survivor leftOwner rightOwner leftFound rightFound frame tag planAfter planRaw
  survivorWellFormed outcomes =
    case frame of
      MkForeignLifecycleGuardFrame sources
        (FibersControlRelated {component} leftParent rightParent retiredFlag
          rightRetired leftTable rightTable leftLifecycle rightLifecycle parentSame
          retiredSame lifecycleSame)
        relianceFrame =>
          case retiredSame of
            Refl => case leftLifecycle of
              Inactive outcome => void (nothingNotJustAdvanceDispatch
                (trans (sym (advanceInactiveIsNothing nameEq keyEq actor
                  planAmbient plan component leftParent retiredFlag leftTable
                  outcome leftFound)) planRaw))
              Active accumulator view =>
                void (nothingNotJustAdvanceDispatch
                  (trans (sym (advanceActiveIsNothing nameEq keyEq actor
                    planAmbient plan component leftParent retiredFlag leftTable
                    accumulator view leftFound)) planRaw))
              Unloading accumulator view outcome =>
                void (nothingNotJustAdvanceDispatch
                  (trans (sym (advanceUnloadingIsNothing nameEq keyEq actor
                    planAmbient plan component leftParent retiredFlag leftTable
                    accumulator view outcome leftFound)) planRaw))
              Reloading leftRemaining leftAccumulator leftView =>
                case reloadingRightAdvance lifecycleSame of
                  MkReloadingRightAdvance rightRemaining rightAccumulator
                    rightView rightLifecycleShape remainingSame accumulatorsSame
                    viewsSame =>
                      case rightLifecycleShape of
                        Refl => case remainingSame of
                          Refl => case viewsSame of
                            Refl => dispatchRemaining sources leftParent
                              rightParent retiredFlag leftTable rightTable
                              leftRemaining leftAccumulator rightAccumulator
                              leftView parentSame accumulatorsSame leftFound
                              rightFound
  where
  0 dispatchRemaining :
    {component : Component key value world error} ->
    (sources : ForeignLifecycleOrderedSourcesRelated name key world error value
      nameEq keyEq selected
      (dependencies (componentDependencies component))
      (bindings plan) (bindings survivor)) ->
    (leftParent, rightParent : Parent name) ->
    (retiredFlag : Bool) ->
    (leftTable, rightTable : OwnedTable key value
      (componentProvisions component)) ->
    (remaining : List (StepEffect key value world error
      (dependencies (componentDependencies component))
      (componentProvisions component))) ->
    (leftAccumulator, rightAccumulator : LocalState key value world
      (componentProvisions component) -> LocalState key value world
      (componentProvisions component)) ->
    (view : View name (dependencies (componentDependencies component))) ->
    leftParent = rightParent ->
    AccumulatorRelated leftAccumulator rightAccumulator ->
    lookupFiber @{nameEq} actor plan = Just
      (MkFiber component leftParent retiredFlag leftTable
        (Reloading remaining leftAccumulator view)) ->
    lookupFiber @{nameEq} actor survivor = Just
      (MkFiber component rightParent retiredFlag rightTable
        (Reloading remaining rightAccumulator view)) ->
    ForeignLifecycleControlReplay name key world error value nameEq keyEq
      selected (LAdvance actor) tag planAfter
      (MkSystemState survivorAmbient survivor)
  dispatchRemaining sources leftParent rightParent retiredFlag leftTable
    rightTable [] leftAccumulator rightAccumulator view parentsSame
    accumulatorsSame concreteLeftFound concreteRightFound =
      let 0 resolvedSame = foreignLifecycleResolveViewSame nameEq keyEq
            (dependencies (componentDependencies component)) plan survivor
            sources
          0 targetsSame :
            (targetFiber @{nameEq} @{keyEq}
              (MkFiber component leftParent retiredFlag leftTable
                (Reloading [] leftAccumulator view)) plan =
             targetFiber @{nameEq} @{keyEq}
              (MkFiber component rightParent retiredFlag rightTable
                (Reloading [] rightAccumulator view)) survivor)
          targetsSame = targetFiberSameFromResolve nameEq keyEq component
            leftParent rightParent retiredFlag leftTable rightTable
            (Reloading [] leftAccumulator view)
            (Reloading [] rightAccumulator view) plan survivor resolvedSame
          matches : Bool
          matches = targetMatches @{nameEq}
            (targetFiber @{nameEq} @{keyEq}
              (MkFiber component leftParent retiredFlag leftTable
                (Reloading [] leftAccumulator view)) plan) view
          0 leftMatches : (targetMatches @{nameEq}
              (targetFiber @{nameEq} @{keyEq}
                (MkFiber component leftParent retiredFlag leftTable
                  (Reloading [] leftAccumulator view)) plan) view = matches)
          leftMatches = Refl
          0 rightMatches : (targetMatches @{nameEq}
              (targetFiber @{nameEq} @{keyEq}
                (MkFiber component rightParent retiredFlag rightTable
                  (Reloading [] rightAccumulator view)) survivor) view = matches)
          rightMatches = sym (cong (\target => targetMatches @{nameEq} target view)
            targetsSame)
          0 ordered : SelectedOrderedRegistryControlsRelated name key world error
            value selected (bindings plan) (bindings survivor)
          ordered = foreignLifecycleSourcesGiveSelectedOrdered sources
      in replayForeignAdvanceEmptyControls nameEq keyEq selected actor
        actorDistinct planAmbient survivorAmbient plan survivor component
        leftParent rightParent retiredFlag leftTable rightTable leftAccumulator
        rightAccumulator view parentsSame accumulatorsSame concreteLeftFound
        concreteRightFound ordered matches leftMatches rightMatches tag planAfter planRaw
        survivorWellFormed
  dispatchRemaining sources leftParent rightParent retiredFlag leftTable
    rightTable (step :: rest) leftAccumulator rightAccumulator view parentsSame
    accumulatorsSame concreteLeftFound concreteRightFound =
      let agreement = outcomes component leftTable rightTable step rest view
          0 resolvedSame = foreignLifecycleResolveViewSame nameEq keyEq
            (dependencies (componentDependencies component)) plan survivor
            sources
          0 targetsSame :
            (targetFiber @{nameEq} @{keyEq}
              (MkFiber component leftParent retiredFlag leftTable
                (Reloading (step :: rest) leftAccumulator view)) plan =
             targetFiber @{nameEq} @{keyEq}
              (MkFiber component rightParent retiredFlag rightTable
                (Reloading (step :: rest) rightAccumulator view)) survivor)
          targetsSame = targetFiberSameFromResolve nameEq keyEq component
            leftParent rightParent retiredFlag leftTable rightTable
            (Reloading (step :: rest) leftAccumulator view)
            (Reloading (step :: rest) rightAccumulator view) plan survivor
            resolvedSame
          matches : Bool
          matches = targetMatches @{nameEq}
            (targetFiber @{nameEq} @{keyEq}
              (MkFiber component leftParent retiredFlag leftTable
                (Reloading (step :: rest) leftAccumulator view)) plan) view
          0 leftMatches : (targetMatches @{nameEq}
              (targetFiber @{nameEq} @{keyEq}
                (MkFiber component leftParent retiredFlag leftTable
                  (Reloading (step :: rest) leftAccumulator view)) plan) view =
              matches)
          leftMatches = Refl
          0 rightMatches : (targetMatches @{nameEq}
              (targetFiber @{nameEq} @{keyEq}
                (MkFiber component rightParent retiredFlag rightTable
                  (Reloading (step :: rest) rightAccumulator view)) survivor)
              view = matches)
          rightMatches = sym (cong (\target => targetMatches @{nameEq} target view)
            targetsSame)
          0 ordered : SelectedOrderedRegistryControlsRelated name key world error
            value selected (bindings plan) (bindings survivor)
          ordered = foreignLifecycleSourcesGiveSelectedOrdered sources
      in dispatchDefined agreement ordered matches leftMatches rightMatches
    where
    0 dispatchDefined :
      IteratorOutcomeAgreement name key value world error keyEq
        (runtimeAdvanceOutcome nameEq keyEq actor component step rest view
          survivorAmbient rightTable survivor)
        (runtimeAdvanceOutcome nameEq keyEq actor component step rest view
          planAmbient leftTable plan) ->
      SelectedOrderedRegistryControlsRelated name key world error value selected
        (bindings plan) (bindings survivor) ->
      (matches : Bool) ->
      (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq}
          (MkFiber component leftParent retiredFlag leftTable
            (Reloading (step :: rest) leftAccumulator view)) plan) view =
        matches) ->
      (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq}
          (MkFiber component rightParent retiredFlag rightTable
            (Reloading (step :: rest) rightAccumulator view)) survivor) view =
        matches) ->
      ForeignLifecycleControlReplay name key world error value nameEq keyEq
        selected (LAdvance actor) tag planAfter
        (MkSystemState survivorAmbient survivor)
    dispatchDefined agreement ordered matches leftMatches rightMatches
      with (resolveCommittedValues @{nameEq} @{keyEq}
        (dependencies (componentDependencies component)) view plan)
      proof leftResolved
      dispatchDefined agreement ordered matches leftMatches rightMatches |
        Nothing = void (nothingNotJustAdvanceDispatch
          (trans (sym (advanceMissingCapabilityIsNothing nameEq keyEq actor
            planAmbient plan component leftParent retiredFlag leftTable step rest
            leftAccumulator view concreteLeftFound leftResolved)) planRaw))
      dispatchDefined agreement ordered matches leftMatches rightMatches |
        Just leftCapability
        with (resolveCommittedValues @{nameEq} @{keyEq}
          (dependencies (componentDependencies component)) view survivor)
        proof rightResolved
        dispatchDefined agreement ordered matches leftMatches rightMatches |
          Just leftCapability | Nothing
          with (runStepEffect step leftCapability
            (MkLocalState planAmbient
              (restrictOwnedPreservingOrder @{keyEq}
                (componentProvisions component) (ownedValues leftTable))))
          proof leftDefinedRun
          dispatchDefined agreement ordered matches leftMatches rightMatches |
            Just leftCapability | Nothing | Left leftError =
              void (undefinedDefinedOutcomeImpossible agreement)
          dispatchDefined agreement ordered matches leftMatches rightMatches |
            Just leftCapability | Nothing | Right (leftAfter, leftUndo) =
              void (undefinedDefinedOutcomeImpossible agreement)
        dispatchDefined agreement ordered matches leftMatches rightMatches |
          Just leftCapability | Just rightCapability
          with (runStepEffect step leftCapability
            (MkLocalState planAmbient
              (restrictOwnedPreservingOrder @{keyEq}
                (componentProvisions component) (ownedValues leftTable))))
          proof leftRan
          dispatchDefined agreement ordered matches leftMatches rightMatches |
            Just leftCapability | Just rightCapability | Left leftError
            with (runStepEffect step rightCapability
              (MkLocalState survivorAmbient
                (restrictOwnedPreservingOrder @{keyEq}
                  (componentProvisions component) (ownedValues rightTable))))
            proof rightRan
            dispatchDefined agreement ordered matches leftMatches rightMatches |
              Just leftCapability | Just rightCapability | Left leftError |
              Left rightError = case agreement of
                IteratorFailuresAgree errorsSame =>
                  replayForeignAdvanceRaisedControls nameEq keyEq selected actor
                    actorDistinct planAmbient survivorAmbient plan survivor
                    component leftParent rightParent retiredFlag leftTable
                    rightTable step rest leftAccumulator rightAccumulator view
                    parentsSame accumulatorsSame concreteLeftFound
                    concreteRightFound ordered leftCapability rightCapability leftResolved rightResolved
                    leftError rightError (sym errorsSame) leftRan rightRan tag
                    planAfter planRaw survivorWellFormed
            dispatchDefined agreement ordered matches leftMatches rightMatches |
              Just leftCapability | Just rightCapability | Left leftError |
              Right (rightAfter, rightUndo) =
                void (successFailureOutcomeImpossible agreement)
          dispatchDefined agreement ordered matches leftMatches rightMatches |
            Just leftCapability | Just rightCapability |
            Right (leftAfter, leftUndo)
            with (runStepEffect step rightCapability
              (MkLocalState survivorAmbient
                (restrictOwnedPreservingOrder @{keyEq}
                  (componentProvisions component) (ownedValues rightTable))))
            proof rightRan
            dispatchDefined agreement ordered matches leftMatches rightMatches |
              Just leftCapability | Just rightCapability |
              Right (leftAfter, leftUndo) | Left rightError =
                void (failureSuccessOutcomeImpossible agreement)
            dispatchDefined agreement ordered matches leftMatches rightMatches |
              Just leftCapability | Just rightCapability |
              Right (leftAfter, leftUndo) | Right (rightAfter, rightUndo) =
                case agreement of
                  IteratorSuccessfulYieldsAgree continuationSame undoMaps =>
                    replayForeignAdvanceSuccessfulControls nameEq keyEq selected
                      actor actorDistinct planAmbient survivorAmbient plan
                      survivor component leftParent rightParent retiredFlag
                      leftTable rightTable step rest leftAccumulator
                      rightAccumulator view parentsSame accumulatorsSame
                      concreteLeftFound concreteRightFound ordered leftCapability
                      rightCapability leftResolved rightResolved leftAfter rightAfter leftUndo
                      rightUndo leftRan rightRan undoMaps matches leftMatches
                      rightMatches tag planAfter planRaw survivorWellFormed
