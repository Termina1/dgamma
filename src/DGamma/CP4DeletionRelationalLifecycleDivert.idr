module DGamma.CP4DeletionRelationalLifecycleDivert

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
import DGamma.CP4DeletionSelectedForeignLifecycleDivert
import Decidable.Equality

%default total

public export
0 replayRelatedDivert :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (leftBefore, rightBefore : SystemState name key value world error) ->
  (leftNamed : NamedTransition name key world error value (LDivert actor)
    leftBefore) ->
  applyAction @{nameEq} @{keyEq} (LDivert actor) leftBefore =
    Just (namedTag leftNamed, namedAfter leftNamed) ->
  registryWellFormed @{nameEq} @{keyEq} leftBefore = True ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} leftBefore)
    (projectEffectState @{nameEq} rightBefore) ->
  OrderedRegistryControlsRelated name key world error value
    (bindings (registry leftBefore)) (bindings (registry rightBefore)) ->
  registryWellFormed @{nameEq} @{keyEq} rightBefore = True ->
  RelatedNamedActionReplay name key world error value nameEq keyEq
    (LDivert actor) leftBefore rightBefore leftNamed
replayRelatedDivert nameEq keyEq actor
  (MkSystemState leftWorld leftRegistry)
  (MkSystemState rightWorld rightRegistry)
  leftNamed leftRaw leftWellFormed effects ordered rightWellFormed =
    case relatedLifecycleOwnersAt nameEq keyEq (LDivert actor) Refl
      (MkSystemState leftWorld leftRegistry)
      (MkSystemState rightWorld rightRegistry)
      (namedTag leftNamed) (namedAfter leftNamed) leftRaw effects ordered of
      MkRelatedLifecycleOwners leftOwner rightOwner leftFound rightFound
        ownersRelated sources =>
          let 0 outerLeftShape = fiberControlRelatedLeftIsLeft ownersRelated
              0 outerRightShape = fiberControlRelatedRightIsRight ownersRelated
          in case foreignDivertPlanView nameEq keyEq actor leftWorld leftRegistry
            (namedTag leftNamed) (namedAfter leftNamed) leftRaw of
            MkLocatedForeignDivertPlanView observedOwner observedFound planView =>
              let 0 ownerSame : (observedOwner = leftOwner)
                  ownerSame = justInjective (trans (sym observedFound) leftFound)
              in case ownerSame of
                Refl => case foreignDivertReplayData planView of
                  MkForeignDivertReplayData component leftParent leftRetired
                    leftTable remaining leftAccumulator leftView ownerShape
                    leftMismatch observedTag observedAfter =>
                      case ownerShape of
                        Refl => case ownersRelated of
                          FibersControlRelated leftParent rightParent leftRetired
                            rightRetired leftTable rightTable
                            (Reloading remaining leftAccumulator leftView)
                            rightLifecycle parentSame retiredSame lifecycleSame =>
                              case reloadingRightControls lifecycleSame of
                                MkReloadingRightControls rightRemaining
                                  rightAccumulator rightView rightLifecycleShape
                                  remainingSame accumulatorsSame viewsSame =>
                                    case rightLifecycleShape of
                                      Refl => case remainingSame of
                                        Refl => case viewsSame of
                                          Refl =>
                                            let 0 exactLeftFound :
                                                  (lookupFiber @{nameEq} actor
                                                    leftRegistry = Just
                                                    (MkFiber component leftParent
                                                      leftRetired leftTable
                                                      (Reloading remaining
                                                        leftAccumulator leftView)))
                                                exactLeftFound = trans leftFound
                                                  (cong Just (sym outerLeftShape))
                                                0 exactRightFound :
                                                  (lookupFiber @{nameEq} actor
                                                    rightRegistry = Just
                                                    (MkFiber component rightParent
                                                      rightRetired rightTable
                                                      (Reloading remaining
                                                        rightAccumulator leftView)))
                                                exactRightFound = trans rightFound
                                                  (cong Just (sym outerRightShape))
                                                0 targetsSame :
                                                  (targetFiber @{nameEq} @{keyEq}
                                                    (MkFiber component leftParent
                                                      leftRetired leftTable
                                                      (Reloading remaining
                                                        leftAccumulator leftView))
                                                    leftRegistry =
                                                   targetFiber @{nameEq} @{keyEq}
                                                    (MkFiber component rightParent
                                                      rightRetired rightTable
                                                      (Reloading remaining
                                                        rightAccumulator leftView))
                                                    rightRegistry)
                                                targetsSame =
                                                  orderedRuntimeTargetFiberSame nameEq
                                                    keyEq component leftParent
                                                    rightParent leftRetired rightRetired
                                                    leftTable rightTable
                                                    (Reloading remaining leftAccumulator
                                                      leftView)
                                                    (Reloading remaining rightAccumulator
                                                      leftView)
                                                    leftRegistry rightRegistry
                                                    retiredSame sources
                                                0 rightMismatch :
                                                  targetMatches @{nameEq}
                                                    (targetFiber @{nameEq} @{keyEq}
                                                      (MkFiber component rightParent
                                                        rightRetired rightTable
                                                        (Reloading remaining
                                                          rightAccumulator leftView))
                                                      rightRegistry) leftView = False
                                                rightMismatch = trans
                                                  (cong (\target => targetMatches
                                                    @{nameEq} target leftView)
                                                    (sym targetsSame)) leftMismatch
                                                leftNext : Fiber name key value world error
                                                leftNext = MkFiber component leftParent
                                                  leftRetired leftTable
                                                  (Unloading leftAccumulator leftView
                                                    Nothing)
                                                rightNext : Fiber name key value world error
                                                rightNext = MkFiber component rightParent
                                                  rightRetired rightTable
                                                  (Unloading rightAccumulator leftView
                                                    Nothing)
                                                0 nextRelated : FiberControlRelated
                                                  leftNext rightNext
                                                nextRelated = FibersControlRelated
                                                  leftParent rightParent leftRetired
                                                  rightRetired leftTable rightTable
                                                  (Unloading leftAccumulator leftView
                                                    Nothing)
                                                  (Unloading rightAccumulator leftView
                                                    Nothing)
                                                  parentSame retiredSame
                                                  (divertLifecycleControlRelated
                                                    {leftRemaining = remaining}
                                                    {rightRemaining = remaining}
                                                    (ReloadingControls Refl
                                                      accumulatorsSame Refl))
                                                rightAfter : SystemState name key value
                                                  world error
                                                rightAfter = MkSystemState rightWorld
                                                  (replaceBinding @{nameEq} actor
                                                    rightNext rightRegistry)
                                                0 rightRawTag : applyAction @{nameEq}
                                                  @{keyEq} (LDivert actor)
                                                  (MkSystemState rightWorld
                                                    rightRegistry) =
                                                  Just (LDivertTag, rightAfter)
                                                rightRawTag = rewrite exactRightFound in
                                                  rewrite rightMismatch in Refl
                                                0 leftConcreteRaw : applyAction
                                                  @{nameEq} @{keyEq} (LDivert actor)
                                                  (MkSystemState leftWorld
                                                    leftRegistry) =
                                                  Just (LDivertTag,
                                                    the (SystemState name key value
                                                      world error)
                                                      (MkSystemState leftWorld
                                                        (replaceBinding @{nameEq} actor
                                                          (MkFiber component leftParent
                                                            leftRetired leftTable
                                                            (Unloading leftAccumulator
                                                              leftView Nothing))
                                                          leftRegistry)))
                                                leftConcreteRaw = rewrite observedFound in
                                                  rewrite leftMismatch in Refl
                                                0 pairSame :
                                                  (LDivertTag,
                                                    the (SystemState name key value
                                                      world error)
                                                      (MkSystemState leftWorld
                                                        (replaceBinding @{nameEq} actor
                                                          (MkFiber component leftParent
                                                            leftRetired leftTable
                                                            (Unloading leftAccumulator
                                                              leftView Nothing))
                                                          leftRegistry))) =
                                                  (namedTag leftNamed,
                                                    namedAfter leftNamed)
                                                pairSame = justInjective
                                                  (trans (sym leftConcreteRaw) leftRaw)
                                                0 tagSame : namedTag leftNamed = LDivertTag
                                                tagSame = sym (cong fst pairSame)
                                                0 rightRaw : applyAction @{nameEq}
                                                  @{keyEq} (LDivert actor)
                                                  (MkSystemState rightWorld
                                                    rightRegistry) =
                                                  Just (namedTag leftNamed, rightAfter)
                                                rightRaw = rewrite tagSame in rightRawTag
                                                0 leftAfterShape : MkSystemState leftWorld
                                                  (replaceBinding @{nameEq} actor
                                                    (MkFiber component leftParent
                                                      leftRetired leftTable
                                                      (Unloading leftAccumulator
                                                        leftView Nothing))
                                                    leftRegistry) =
                                                  namedAfter leftNamed
                                                leftAfterShape = cong snd pairSame
                                                0 rawControls :
                                                  RelatedLifecycleRawControlReplay name
                                                    key world error value nameEq keyEq
                                                    (LDivert actor)
                                                    (MkSystemState leftWorld leftRegistry)
                                                    (MkSystemState rightWorld rightRegistry)
                                                    leftNamed
                                                rawControls =
                                                  packageRelatedLifecycleReplacementControls
                                                    nameEq (LDivert actor) actor
                                                    leftWorld rightWorld leftRegistry
                                                    rightRegistry leftNamed leftNext
                                                    rightNext nextRelated ordered
                                                    leftWorld leftAfterShape rightWorld
                                                    rightRaw
                                                0 leftSourceToTarget : EffectStateRelated
                                                  keyEq
                                                  (projectEffectState @{nameEq}
                                                    (the (SystemState name key value
                                                      world error)
                                                      (MkSystemState leftWorld
                                                        leftRegistry)))
                                                  (projectEffectState @{nameEq}
                                                    (namedAfter leftNamed))
                                                leftSourceToTarget = replace
                                                  {p = \state => EffectStateRelated keyEq
                                                    (projectEffectState @{nameEq}
                                                      (the (SystemState name key value
                                                        world error)
                                                        (MkSystemState leftWorld
                                                          leftRegistry)))
                                                    (projectEffectState @{nameEq} state)}
                                                  leftAfterShape
                                                  (projectTablePreservingReplace nameEq
                                                    keyEq actor leftWorld
                                                    (MkFiber component leftParent
                                                      leftRetired leftTable
                                                      (Reloading remaining
                                                        leftAccumulator leftView))
                                                    leftNext leftRegistry exactLeftFound
                                                    Refl)
                                                0 rightSourceToTarget : EffectStateRelated
                                                  keyEq
                                                  (projectEffectState @{nameEq}
                                                    (the (SystemState name key value
                                                      world error)
                                                      (MkSystemState rightWorld
                                                        rightRegistry)))
                                                  (projectEffectState @{nameEq}
                                                    rightAfter)
                                                rightSourceToTarget =
                                                  projectTablePreservingReplace nameEq
                                                    keyEq actor rightWorld
                                                    (MkFiber component rightParent
                                                      rightRetired rightTable
                                                      (Reloading remaining
                                                        rightAccumulator leftView))
                                                    rightNext rightRegistry
                                                    exactRightFound Refl
                                                0 finalEffects : EffectStateRelated
                                                  keyEq
                                                  (projectEffectState @{nameEq}
                                                    (namedAfter leftNamed))
                                                  (projectEffectState @{nameEq}
                                                    rightAfter)
                                                finalEffects = effectTransitive
                                                  (effectSymmetric leftSourceToTarget)
                                                  (effectTransitive effects
                                                    rightSourceToTarget)
                                            in packageRelatedReplay nameEq keyEq
                                              (LDivert actor)
                                              (MkSystemState leftWorld leftRegistry)
                                              (MkSystemState rightWorld rightRegistry)
                                              leftNamed rightAfter rightRaw
                                              rightWellFormed finalEffects
                                              (relatedLifecycleControls rawControls)
