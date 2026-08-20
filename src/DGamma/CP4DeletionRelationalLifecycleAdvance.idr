module DGamma.CP4DeletionRelationalLifecycleAdvance

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionRelationalActionCore
import DGamma.CP4DeletionRelationalActionOrchestration
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionRelationalLifecycleAdvanceCases
import DGamma.CP4DeletionRelationalLifecycleAdvanceDispatch
import DGamma.CP4DeletionRelationalLifecycleCore
import DGamma.CP4DeletionRelationalLifecycleSources
import DGamma.CP4DeletionRelationalSuffixFold
import DGamma.CP4DeletionSelectedForeignLifecycleAdvanceDispatchCore
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import DGamma.CP4RecoveryEffectRespect
import DGamma.Unified
import Decidable.Equality

%default total

||| Exact full-boundary observations make the concrete iterator invocation
||| identical: committed values, ambient input, and canonical owned table all
||| coincide.  The repaired failure/success agreement therefore follows without
||| a separate cross-actor independence premise.
public export
0 runtimeAdvanceOutcomeRelated :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (component : Component key value world error) ->
  (step : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (rest : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (leftWorld, rightWorld : world) ->
  (leftTable, rightTable : OwnedTable key value
    (componentProvisions component)) ->
  (left, right : Registry name key value world error) ->
  (leftParent, rightParent : Parent name) ->
  (leftRetired, rightRetired : Bool) ->
  (leftLifecycle, rightLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  lookupFiber @{nameEq} actor left = Just
    (MkFiber component leftParent leftRetired leftTable leftLifecycle) ->
  lookupFiber @{nameEq} actor right = Just
    (MkFiber component rightParent rightRetired rightTable rightLifecycle) ->
  EffectStateRelated keyEq
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState leftWorld left)))
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState rightWorld right))) ->
  RuntimeIteratorOutcomeAgreement name key value world error keyEq
    (runtimeAdvanceOutcome nameEq keyEq actor component step rest view
      rightWorld rightTable right)
    (runtimeAdvanceOutcome nameEq keyEq actor component step rest view
      leftWorld leftTable left)
runtimeAdvanceOutcomeRelated {name} {key} {world} {error} {value}
  nameEq keyEq actor component step rest view leftWorld rightWorld leftTable
  rightTable left right leftParent rightParent leftRetired rightRetired
  leftLifecycle rightLifecycle leftFound rightFound effects =
    let leftState : SystemState name key value world error
        leftState = MkSystemState leftWorld left
        rightState : SystemState name key value world error
        rightState = MkSystemState rightWorld right
        leftEffects : EffectState name key value world
        leftEffects = projectEffectState @{nameEq} leftState
        rightEffects : EffectState name key value world
        rightEffects = projectEffectState @{nameEq} rightState
        0 resolvedSame :
          resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
            {value = value} {world = world} {error = error}
            (dependencies (componentDependencies component)) view left =
          resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
            {value = value} {world = world} {error = error}
            (dependencies (componentDependencies component)) view right
        resolvedSame = trans
          (sym (resolveEffectValuesProjected nameEq keyEq
            (dependencies (componentDependencies component)) view leftState))
          (trans (resolveEffectValuesRelated keyEq
            (dependencies (componentDependencies component)) view effects)
            (resolveEffectValuesProjected nameEq keyEq
              (dependencies (componentDependencies component)) view rightState))
        0 locatedTablesSame : bindings (ownedValues leftTable) =
          bindings (ownedValues rightTable)
        locatedTablesSame = relatedLocatedFiberTablesSame nameEq actor
          leftState rightState
          (MkFiber component leftParent leftRetired leftTable leftLifecycle)
          (MkFiber component rightParent rightRetired rightTable rightLifecycle)
          leftFound rightFound effects
        0 normalizedTablesSame :
          restrictOwnedPreservingOrder @{keyEq}
            (componentProvisions component) (ownedValues leftTable) =
          restrictOwnedPreservingOrder @{keyEq}
            (componentProvisions component) (ownedValues rightTable)
        normalizedTablesSame = canonicalNormalizationFromEqualBindings
          (componentProvisions component) (ownedValues leftTable)
          (ownedValues rightTable) locatedTablesSame
        0 localInputSame :
          MkLocalState leftWorld
            (restrictOwnedPreservingOrder @{keyEq}
              (componentProvisions component) (ownedValues leftTable)) =
          MkLocalState rightWorld
            (restrictOwnedPreservingOrder @{keyEq}
              (componentProvisions component) (ownedValues rightTable))
        localInputSame = rewrite ambientExact effects in
          rewrite normalizedTablesSame in Refl
    in outcomeByResolution resolvedSame localInputSame
  where
  0 outcomeByResolution :
    (resolvedSame :
      resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
        {value = value} {world = world} {error = error}
        (dependencies (componentDependencies component)) view left =
      resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
        {value = value} {world = world} {error = error}
        (dependencies (componentDependencies component)) view right) ->
    (localInputSame :
      MkLocalState leftWorld
        (restrictOwnedPreservingOrder @{keyEq}
          (componentProvisions component) (ownedValues leftTable)) =
      MkLocalState rightWorld
        (restrictOwnedPreservingOrder @{keyEq}
          (componentProvisions component) (ownedValues rightTable))) ->
    RuntimeIteratorOutcomeAgreement name key value world error keyEq
      (runtimeAdvanceOutcome nameEq keyEq actor component step rest view
        rightWorld rightTable right)
      (runtimeAdvanceOutcome nameEq keyEq actor component step rest view
        leftWorld leftTable left)
  outcomeByResolution resolvedSame localInputSame
    with (resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
      {value = value} {world = world} {error = error}
      (dependencies (componentDependencies component)) view left) proof leftRun
    outcomeByResolution resolvedSame localInputSame | Nothing =
      let 0 rightRun = sym resolvedSame
      in rewrite rightRun in RuntimeOutcomesUndefined
    outcomeByResolution resolvedSame localInputSame | Just capability
      with (runStepEffect step capability
        (MkLocalState leftWorld
          (restrictOwnedPreservingOrder @{keyEq}
            (componentProvisions component) (ownedValues leftTable))))
        proof stepRun
      outcomeByResolution resolvedSame localInputSame | Just capability |
        Left failure =
          let 0 rightResolve = sym resolvedSame
              0 runSame = cong (runStepEffect step capability) localInputSame
              0 rightStep = trans (sym runSame) stepRun
          in rewrite rightResolve in rewrite rightStep in
            RuntimeFailuresAgree Refl
      outcomeByResolution resolvedSame localInputSame | Just capability |
        Right (after, undo) =
          let 0 rightResolve = sym resolvedSame
              0 runSame = cong (runStepEffect step capability) localInputSame
              0 rightStep = trans (sym runSame) stepRun
              0 ambientRelated : EffectStateRelated keyEq
                (setEffectAmbient (localWorld after)
                  (projectEffectState @{nameEq}
                    (the (SystemState name key value world error)
                      (MkSystemState leftWorld left))))
                (setEffectAmbient (localWorld after)
                  (projectEffectState @{nameEq}
                    (the (SystemState name key value world error)
                      (MkSystemState rightWorld right))))
              ambientRelated = setRelatedEffectAmbient keyEq
                (localWorld after) (localWorld after) Refl effects
              0 outputRelated : EffectStateRelated keyEq
                (setEffectTable @{nameEq} actor
                  (ownedValues (localTable after))
                  (setEffectAmbient (localWorld after)
                    (projectEffectState @{nameEq}
                      (the (SystemState name key value world error)
                        (MkSystemState leftWorld left)))))
                (setEffectTable @{nameEq} actor
                  (ownedValues (localTable after))
                  (setEffectAmbient (localWorld after)
                    (projectEffectState @{nameEq}
                      (the (SystemState name key value world error)
                        (MkSystemState rightWorld right)))))
              outputRelated = setRelatedEffectTables nameEq keyEq actor
                (ownedValues (localTable after))
                (ownedValues (localTable after)) Refl ambientRelated
          in rewrite rightResolve in rewrite rightStep in
            RuntimeYieldsAgree outputRelated
              (effectPartialMapReflexive {name = name} {key = key}
                {value = value} {world = world} keyEq
                (yieldedInverseEffectMap nameEq keyEq actor
                  (componentProvisions component) undo))

||| Full relational replay for every retained L-Advance branch.  The control
||| dispatcher consumes the strengthened runtime outcome agreement; its effect
||| payload is then packaged with the concrete survivor transition.
public export
0 replayRelatedAdvance :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (leftBefore, rightBefore : SystemState name key value world error) ->
  (leftNamed : NamedTransition name key world error value (LAdvance actor)
    leftBefore) ->
  applyAction @{nameEq} @{keyEq} (LAdvance actor) leftBefore =
    Just (namedTag leftNamed, namedAfter leftNamed) ->
  registryWellFormed @{nameEq} @{keyEq} leftBefore = True ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} leftBefore)
    (projectEffectState @{nameEq} rightBefore) ->
  OrderedRegistryControlsRelated name key world error value
    (bindings (registry leftBefore)) (bindings (registry rightBefore)) ->
  registryWellFormed @{nameEq} @{keyEq} rightBefore = True ->
  RelatedNamedActionReplay name key world error value nameEq keyEq
    (LAdvance actor) leftBefore rightBefore leftNamed
replayRelatedAdvance nameEq keyEq actor
  (MkSystemState leftWorld leftRegistry)
  (MkSystemState rightWorld rightRegistry)
  leftNamed leftRaw leftWellFormed effects ordered rightWellFormed =
    case relatedLifecycleOwnersAt nameEq keyEq (LAdvance actor) Refl
      (MkSystemState leftWorld leftRegistry)
      (MkSystemState rightWorld rightRegistry)
      (namedTag leftNamed) (namedAfter leftNamed) leftRaw effects ordered of
      MkRelatedLifecycleOwners leftOwner rightOwner leftFound rightFound
        ownersRelated sources =>
          case replayRelatedAdvanceControlsFromOutcome nameEq keyEq actor
            leftWorld rightWorld leftRegistry rightRegistry leftOwner rightOwner
            leftFound rightFound sources ownersRelated ordered effects
            (namedTag leftNamed) (namedAfter leftNamed) leftRaw
            (\component, leftTable, rightTable, step, rest, view,
              leftParent, rightParent, retiredFlag, leftAccumulator,
              rightAccumulator, concreteLeftFound, concreteRightFound =>
                runtimeAdvanceOutcomeRelated nameEq keyEq actor component step
                  rest view leftWorld rightWorld leftTable rightTable
                  leftRegistry rightRegistry leftParent rightParent retiredFlag
                  retiredFlag
                  (Reloading (step :: rest) leftAccumulator view)
                  (Reloading (step :: rest) rightAccumulator view)
                  concreteLeftFound concreteRightFound effects) of
            replay@(MkFullLifecycleControlReplay rightAfter rightRaw
              finalEffects finalControls) =>
                packageRelatedReplay nameEq keyEq (LAdvance actor)
                  (MkSystemState leftWorld leftRegistry)
                  (MkSystemState rightWorld rightRegistry) leftNamed rightAfter
                  rightRaw rightWellFormed finalEffects finalControls
