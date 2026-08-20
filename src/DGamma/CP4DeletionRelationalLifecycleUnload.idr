module DGamma.CP4DeletionRelationalLifecycleUnload

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionCommuteCore
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionRelationalActionCore
import DGamma.CP4DeletionRelationalActionOrchestration
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionRelationalLifecycleCore
import DGamma.CP4DeletionRelationalLifecycleSources
import DGamma.CP4DeletionRelationalSuffixFold
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import DGamma.CP4DeletionSelectedForeignLifecycleUnload
import Decidable.Equality

%default total

public export
0 replayRelatedUnload :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (leftBefore, rightBefore : SystemState name key value world error) ->
  (leftNamed : NamedTransition name key world error value (LUnload actor)
    leftBefore) ->
  applyAction @{nameEq} @{keyEq} (LUnload actor) leftBefore =
    Just (namedTag leftNamed, namedAfter leftNamed) ->
  registryWellFormed @{nameEq} @{keyEq} leftBefore = True ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} leftBefore)
    (projectEffectState @{nameEq} rightBefore) ->
  OrderedRegistryControlsRelated name key world error value
    (bindings (registry leftBefore)) (bindings (registry rightBefore)) ->
  registryWellFormed @{nameEq} @{keyEq} rightBefore = True ->
  RelatedNamedActionReplay name key world error value nameEq keyEq
    (LUnload actor) leftBefore rightBefore leftNamed
replayRelatedUnload nameEq keyEq actor
  (MkSystemState leftWorld leftRegistry)
  (MkSystemState rightWorld rightRegistry)
  leftNamed leftRaw leftWellFormed effects ordered rightWellFormed =
    case relatedLifecycleOwnersAt nameEq keyEq (LUnload actor) Refl
      (MkSystemState leftWorld leftRegistry)
      (MkSystemState rightWorld rightRegistry)
      (namedTag leftNamed) (namedAfter leftNamed) leftRaw effects ordered of
      MkRelatedLifecycleOwners leftOwner rightOwner leftFound rightFound
        ownersRelated sources =>
          let 0 outerLeftShape = fiberControlRelatedLeftIsLeft ownersRelated
              0 outerRightShape = fiberControlRelatedRightIsRight ownersRelated
          in case foreignUnloadPlanView nameEq keyEq actor leftWorld leftRegistry
            (namedTag leftNamed) (namedAfter leftNamed) leftRaw of
            MkLocatedForeignUnloadPlanView observedOwner observedFound planView =>
              let 0 ownerSame : (observedOwner = leftOwner)
                  ownerSame = justInjective (trans (sym observedFound) leftFound)
              in case ownerSame of
                Refl => case planView of
                  MkForeignUnloadPlanView component leftParent leftRetired
                    leftTable leftAccumulator leftView leftOutcome ownerShape
                    leftUnrelied =>
                      case ownerShape of
                        Refl => case ownersRelated of
                          FibersControlRelated leftParent rightParent leftRetired
                            rightRetired leftTable rightTable
                            (Unloading leftAccumulator leftView leftOutcome)
                            rightLifecycle parentSame retiredSame lifecycleSame =>
                              case unloadingRightControls lifecycleSame of
                                MkUnloadingRightControls rightAccumulator rightView
                                  rightOutcome rightLifecycleShape accumulatorsSame
                                  viewsSame outcomesSame =>
                                    case rightLifecycleShape of
                                      Refl => case viewsSame of
                                        Refl =>
                                          let 0 exactLeftFound :
                                              (lookupFiber @{nameEq} actor
                                                leftRegistry = Just
                                                (MkFiber component leftParent
                                                  leftRetired leftTable
                                                  (Unloading leftAccumulator
                                                    leftView leftOutcome)))
                                              exactLeftFound = trans leftFound
                                                (cong Just (sym outerLeftShape))
                                              0 exactRightFound :
                                                (lookupFiber @{nameEq} actor
                                                  rightRegistry = Just
                                                  (MkFiber component rightParent
                                                    rightRetired rightTable
                                                    (Unloading rightAccumulator
                                                      leftView rightOutcome)))
                                              exactRightFound = trans rightFound
                                                (cong Just (sym outerRightShape))
                                              0 relianceSame : relied @{nameEq}
                                                {name = name} {key = key}
                                                {value = value} {world = world}
                                                {error = error} actor leftRegistry =
                                                relied @{nameEq} {name = name}
                                                  {key = key} {value = value}
                                                  {world = world} {error = error}
                                                  actor rightRegistry
                                              relianceSame = orderedRuntimeReliedSame
                                                nameEq actor leftRegistry rightRegistry
                                                sources
                                              0 rightUnrelied : relied @{nameEq}
                                                {name = name} {key = key}
                                                {value = value} {world = world}
                                                {error = error} actor rightRegistry =
                                                False
                                              rightUnrelied = trans (sym relianceSame)
                                                leftUnrelied
                                              leftInput : LocalState key value world
                                                (componentProvisions component)
                                              leftInput = MkLocalState leftWorld
                                                (restrictOwnedPreservingOrder @{keyEq}
                                                  (componentProvisions component)
                                                  (ownedValues leftTable))
                                              rightInput : LocalState key value world
                                                (componentProvisions component)
                                              rightInput = MkLocalState rightWorld
                                                (restrictOwnedPreservingOrder @{keyEq}
                                                  (componentProvisions component)
                                                  (ownedValues rightTable))
                                              0 locatedTablesSame : bindings
                                                (ownedValues leftTable) = bindings
                                                  (ownedValues rightTable)
                                              locatedTablesSame =
                                                relatedLocatedFiberTablesSame nameEq
                                                  actor
                                                  (MkSystemState leftWorld leftRegistry)
                                                  (MkSystemState rightWorld rightRegistry)
                                                  (MkFiber component leftParent
                                                    leftRetired leftTable
                                                    (Unloading leftAccumulator
                                                      leftView leftOutcome))
                                                  (MkFiber component rightParent
                                                    rightRetired rightTable
                                                    (Unloading rightAccumulator
                                                      leftView rightOutcome))
                                                  exactLeftFound exactRightFound effects
                                              0 normalizedTablesSame :
                                                restrictOwnedPreservingOrder @{keyEq}
                                                  (componentProvisions component)
                                                  (ownedValues leftTable) =
                                                restrictOwnedPreservingOrder @{keyEq}
                                                  (componentProvisions component)
                                                  (ownedValues rightTable)
                                              normalizedTablesSame =
                                                canonicalNormalizationFromEqualBindings
                                                  (componentProvisions component)
                                                  (ownedValues leftTable)
                                                  (ownedValues rightTable)
                                                  locatedTablesSame
                                              0 inputSame : leftInput = rightInput
                                              inputSame = rewrite ambientExact effects in
                                                rewrite normalizedTablesSame in Refl
                                              leftRestored : LocalState key value world
                                                (componentProvisions component)
                                              leftRestored = leftAccumulator leftInput
                                              rightRestored : LocalState key value world
                                                (componentProvisions component)
                                              rightRestored = rightAccumulator rightInput
                                              0 rightRestoredSame :
                                                rightAccumulator leftInput = rightRestored
                                              rightRestoredSame =
                                                cong rightAccumulator inputSame
                                              0 restoredRelated :
                                                LocalStateRuntimeRelated leftRestored
                                                  rightRestored
                                              restoredRelated = replace
                                                {p = \observed =>
                                                  LocalStateRuntimeRelated leftRestored
                                                    observed}
                                                rightRestoredSame
                                                (accumulatorsSame leftInput)
                                              leftNext : Fiber name key value world error
                                              leftNext = MkFiber component leftParent
                                                leftRetired (localTable leftRestored)
                                                (Inactive leftOutcome)
                                              rightNext : Fiber name key value world error
                                              rightNext = MkFiber component rightParent
                                                rightRetired (localTable rightRestored)
                                                (Inactive rightOutcome)
                                              0 nextLifecycle :
                                                LifecycleControlRelated
                                                  (Inactive {key = key}
                                                    {value = value} {world = world}
                                                    {error = error} {name = name}
                                                    leftOutcome)
                                                  (Inactive {key = key}
                                                    {value = value} {world = world}
                                                    {error = error} {name = name}
                                                    rightOutcome)
                                              nextLifecycle =
                                                InactiveControls outcomesSame
                                              0 nextRelated : FiberControlRelated
                                                leftNext rightNext
                                              nextRelated = FibersControlRelated
                                                leftParent rightParent leftRetired
                                                rightRetired (localTable leftRestored)
                                                (localTable rightRestored)
                                                (Inactive leftOutcome)
                                                (Inactive rightOutcome) parentSame
                                                retiredSame nextLifecycle
                                              leftAfterConcrete : SystemState name key
                                                value world error
                                              leftAfterConcrete = MkSystemState
                                                (localWorld leftRestored)
                                                (replaceBinding @{nameEq} actor leftNext
                                                  leftRegistry)
                                              rightAfter : SystemState name key value
                                                world error
                                              rightAfter = MkSystemState
                                                (localWorld rightRestored)
                                                (replaceBinding @{nameEq} actor rightNext
                                                  rightRegistry)
                                              0 leftConcreteRaw : applyAction @{nameEq}
                                                @{keyEq} (LUnload actor)
                                                (MkSystemState leftWorld leftRegistry) =
                                                  Just (LUnloadTag, leftAfterConcrete)
                                              leftConcreteRaw = rewrite exactLeftFound in
                                                rewrite leftUnrelied in Refl
                                              0 pairSame : (LUnloadTag,
                                                  leftAfterConcrete) =
                                                (namedTag leftNamed,
                                                  namedAfter leftNamed)
                                              pairSame = justInjective
                                                (trans (sym leftConcreteRaw) leftRaw)
                                              0 tagSame : namedTag leftNamed = LUnloadTag
                                              tagSame = sym (cong fst pairSame)
                                              0 leftAfterShape : leftAfterConcrete =
                                                namedAfter leftNamed
                                              leftAfterShape = cong snd pairSame
                                              0 rightRawTag : applyAction @{nameEq}
                                                @{keyEq} (LUnload actor)
                                                (MkSystemState rightWorld rightRegistry) =
                                                  Just (LUnloadTag, rightAfter)
                                              rightRawTag = rewrite exactRightFound in
                                                rewrite rightUnrelied in Refl
                                              0 rightRaw : applyAction @{nameEq}
                                                @{keyEq} (LUnload actor)
                                                (MkSystemState rightWorld rightRegistry) =
                                                  Just (namedTag leftNamed, rightAfter)
                                              rightRaw = rewrite tagSame in rightRawTag
                                              0 rawControls :
                                                RelatedLifecycleRawControlReplay name key
                                                  world error value nameEq keyEq
                                                  (LUnload actor)
                                                  (MkSystemState leftWorld leftRegistry)
                                                  (MkSystemState rightWorld rightRegistry)
                                                  leftNamed
                                              rawControls =
                                                packageRelatedLifecycleReplacementControls
                                                  nameEq (LUnload actor) actor leftWorld
                                                  rightWorld leftRegistry rightRegistry
                                                  leftNamed leftNext rightNext nextRelated
                                                  ordered (localWorld leftRestored)
                                                  leftAfterShape
                                                  (localWorld rightRestored) rightRaw
                                              leftEffects : EffectState name key value world
                                              leftEffects = projectEffectState @{nameEq}
                                                (the (SystemState name key value world error)
                                                  (MkSystemState leftWorld leftRegistry))
                                              rightEffects : EffectState name key value world
                                              rightEffects = projectEffectState @{nameEq}
                                                (the (SystemState name key value world error)
                                                  (MkSystemState rightWorld rightRegistry))
                                              0 ambientUpdated : EffectStateRelated keyEq
                                                (setEffectAmbient
                                                  (localWorld leftRestored) leftEffects)
                                                (setEffectAmbient
                                                  (localWorld rightRestored) rightEffects)
                                              ambientUpdated = setRelatedEffectAmbient
                                                keyEq (localWorld leftRestored)
                                                (localWorld rightRestored)
                                                (localAmbientExact restoredRelated) effects
                                              0 runtimeUpdated : EffectStateRelated keyEq
                                                (setEffectTable @{nameEq} actor
                                                  (ownedValues (localTable leftRestored))
                                                  (setEffectAmbient
                                                    (localWorld leftRestored) leftEffects))
                                                (setEffectTable @{nameEq} actor
                                                  (ownedValues (localTable rightRestored))
                                                  (setEffectAmbient
                                                    (localWorld rightRestored) rightEffects))
                                              runtimeUpdated = setRelatedEffectTables
                                                nameEq keyEq actor
                                                (ownedValues (localTable leftRestored))
                                                (ownedValues (localTable rightRestored))
                                                (localBindingsExact restoredRelated)
                                                ambientUpdated
                                              0 leftUpdateToTarget : EffectStateRelated
                                                keyEq
                                                (setEffectTable @{nameEq} actor
                                                  (ownedValues (localTable leftRestored))
                                                  (setEffectAmbient
                                                    (localWorld leftRestored) leftEffects))
                                                (projectEffectState @{nameEq}
                                                  (namedAfter leftNamed))
                                              leftUpdateToTarget = replace
                                                {p = \state => EffectStateRelated keyEq
                                                  (setEffectTable @{nameEq} actor
                                                    (ownedValues
                                                      (localTable leftRestored))
                                                    (setEffectAmbient
                                                      (localWorld leftRestored)
                                                      leftEffects))
                                                  (projectEffectState @{nameEq} state)}
                                                leftAfterShape
                                                (projectRuntimeReplace nameEq keyEq actor
                                                  leftWorld (localWorld leftRestored)
                                                  (MkFiber component leftParent
                                                    leftRetired leftTable
                                                    (Unloading leftAccumulator leftView
                                                      leftOutcome))
                                                  leftNext leftRegistry exactLeftFound
                                                  (ownedValues (localTable leftRestored))
                                                  Refl)
                                              0 rightUpdateToTarget : EffectStateRelated
                                                keyEq
                                                (setEffectTable @{nameEq} actor
                                                  (ownedValues (localTable rightRestored))
                                                  (setEffectAmbient
                                                    (localWorld rightRestored)
                                                    rightEffects))
                                                (projectEffectState @{nameEq} rightAfter)
                                              rightUpdateToTarget = projectRuntimeReplace
                                                nameEq keyEq actor rightWorld
                                                (localWorld rightRestored)
                                                (MkFiber component rightParent
                                                  rightRetired rightTable
                                                  (Unloading rightAccumulator leftView
                                                    rightOutcome))
                                                rightNext rightRegistry exactRightFound
                                                (ownedValues (localTable rightRestored))
                                                Refl
                                              0 finalEffects : EffectStateRelated keyEq
                                                (projectEffectState @{nameEq}
                                                  (namedAfter leftNamed))
                                                (projectEffectState @{nameEq} rightAfter)
                                              finalEffects = effectTransitive
                                                (effectSymmetric leftUpdateToTarget)
                                                (effectTransitive runtimeUpdated
                                                  rightUpdateToTarget)
                                          in packageRelatedReplay nameEq keyEq
                                            (LUnload actor)
                                            (MkSystemState leftWorld leftRegistry)
                                            (MkSystemState rightWorld rightRegistry)
                                            leftNamed rightAfter rightRaw rightWellFormed
                                            finalEffects
                                            (relatedLifecycleControls rawControls)
