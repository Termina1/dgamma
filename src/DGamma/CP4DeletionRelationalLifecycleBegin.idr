module DGamma.CP4DeletionRelationalLifecycleBegin

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
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedForeignLifecycleBegin
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import DGamma.CP4RuntimeBindings
import Decidable.Equality

%default total

||| Full-boundary L-Begin replay.  Unlike the selected quotient proof, the
||| complete ordered source relation already compares every provider cell, so
||| target resolution is transported directly with no selected-provider anchor.
public export
0 replayRelatedBegin :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (leftBefore, rightBefore : SystemState name key value world error) ->
  (leftNamed : NamedTransition name key world error value (LBegin actor)
    leftBefore) ->
  applyAction @{nameEq} @{keyEq} (LBegin actor) leftBefore =
    Just (namedTag leftNamed, namedAfter leftNamed) ->
  registryWellFormed @{nameEq} @{keyEq} leftBefore = True ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} leftBefore)
    (projectEffectState @{nameEq} rightBefore) ->
  OrderedRegistryControlsRelated name key world error value
    (bindings (registry leftBefore)) (bindings (registry rightBefore)) ->
  registryWellFormed @{nameEq} @{keyEq} rightBefore = True ->
  RelatedNamedActionReplay name key world error value nameEq keyEq
    (LBegin actor) leftBefore rightBefore leftNamed
replayRelatedBegin nameEq keyEq actor
  (MkSystemState leftWorld leftRegistry)
  (MkSystemState rightWorld rightRegistry)
  leftNamed leftRaw leftWellFormed effects ordered rightWellFormed =
    case relatedLifecycleOwnersAt nameEq keyEq (LBegin actor) Refl
      (MkSystemState leftWorld leftRegistry)
      (MkSystemState rightWorld rightRegistry)
      (namedTag leftNamed) (namedAfter leftNamed) leftRaw effects
      ordered of
      MkRelatedLifecycleOwners leftOwner rightOwner leftFound rightFound
        ownersRelated sources =>
          case foreignBeginPlanView nameEq keyEq actor leftWorld leftRegistry
            leftOwner leftFound (namedTag leftNamed) (namedAfter leftNamed)
            leftRaw of
            beginView@(MkForeignBeginPlanView {component} {parent = leftParent}
              {table = leftTable} view ownerShape leftTarget tagShape
              afterShape) =>
                let 0 outerRightShape =
                      fiberControlRelatedRightIsRight ownersRelated
                in case ownerShape of
                  Refl => case ownersRelated of
                    FibersControlRelated leftParent rightParent False rightRetired
                      leftTable rightTable (Inactive Nothing) rightLifecycle
                      parentSame retiredSame lifecycleSame =>
                      case retiredSame of
                        Refl => case lifecycleSame of
                          InactiveControls outcomeSame => case outcomeSame of
                            Refl =>
                              let 0 exactRightFound : (lookupFiber @{nameEq} actor
                                    rightRegistry = Just
                                      (MkFiber component rightParent False
                                        rightTable (Inactive Nothing)))
                                  exactRightFound = trans rightFound
                                    (cong Just (sym outerRightShape))
                                  0 targetSame :
                                    (targetFiber @{nameEq} @{keyEq}
                                      (MkFiber component leftParent False
                                        leftTable (Inactive Nothing))
                                      leftRegistry =
                                     targetFiber @{nameEq} @{keyEq}
                                      (MkFiber component rightParent False
                                        rightTable (Inactive Nothing))
                                      rightRegistry)
                                  targetSame = orderedRuntimeTargetFiberSame
                                    nameEq keyEq component leftParent rightParent
                                    False False leftTable rightTable
                                    (Inactive Nothing) (Inactive Nothing)
                                    leftRegistry rightRegistry Refl sources
                                  0 rightTarget : (targetFiber @{nameEq} @{keyEq}
                                    (MkFiber component rightParent False rightTable
                                      (Inactive Nothing)) rightRegistry = Just view)
                                  rightTarget = trans (sym targetSame) leftTarget
                                  leftNext : Fiber name key value world error
                                  leftNext = MkFiber component leftParent False
                                    leftTable (Reloading (componentProgram component)
                                      (\local => local) view)
                                  rightNext : Fiber name key value world error
                                  rightNext = MkFiber component rightParent False
                                    rightTable (Reloading (componentProgram component)
                                      (\local => local) view)
                                  0 nextRelated : FiberControlRelated leftNext rightNext
                                  nextRelated = FibersControlRelated leftParent
                                    rightParent False False leftTable rightTable
                                    (Reloading (componentProgram component)
                                      (\local => local) view)
                                    (Reloading (componentProgram component)
                                      (\local => local) view)
                                    parentSame Refl
                                    (beginLifecycleControlRelated
                                      (componentProgram component) view)
                                  rightAfter : SystemState name key value world error
                                  rightAfter = MkSystemState rightWorld
                                    (replaceBinding @{nameEq} actor rightNext
                                      rightRegistry)
                                  0 rightRaw : applyAction @{nameEq} @{keyEq}
                                    (LBegin actor)
                                    (MkSystemState rightWorld rightRegistry) =
                                      Just (LBeginTag, rightAfter)
                                  rightRaw = rewrite rightFound in
                                    rewrite rightTarget in Refl
                                  0 tagSame : namedTag leftNamed = LBeginTag
                                  tagSame = tagShape
                                  0 rightObservedRaw : applyAction @{nameEq} @{keyEq}
                                    (LBegin actor)
                                    (MkSystemState rightWorld rightRegistry) =
                                    Just (namedTag leftNamed, rightAfter)
                                  rightObservedRaw = rewrite tagSame in rightRaw
                                  0 leftAfterShape : MkSystemState leftWorld
                                    (replaceBinding @{nameEq} actor
                                      (MkFiber component leftParent False
                                        leftTable
                                        (Reloading (componentProgram component)
                                          (\local => local) view))
                                      leftRegistry) = namedAfter leftNamed
                                  leftAfterShape = afterShape
                                  0 replacedControls :
                                    OrderedRegistryControlsRelated name key world
                                      error value
                                      (replaceEntries @{nameEq} actor leftNext
                                        (bindings leftRegistry))
                                      (replaceEntries @{nameEq} actor rightNext
                                        (bindings rightRegistry))
                                  replacedControls = orderedControlsReplace
                                    nameEq actor leftNext rightNext nextRelated
                                    (bindings leftRegistry)
                                    (bindings rightRegistry) ordered
                                  0 leftBindings : bindings
                                    (replaceBinding @{nameEq} actor leftNext
                                      leftRegistry) =
                                    replaceEntries @{nameEq} actor leftNext
                                      (bindings leftRegistry)
                                  leftBindings = replaceBindingRuntimeBindings
                                    nameEq actor leftNext leftRegistry
                                  0 rightBindings : bindings
                                    (replaceBinding @{nameEq} actor rightNext
                                      rightRegistry) =
                                    replaceEntries @{nameEq} actor rightNext
                                      (bindings rightRegistry)
                                  rightBindings = replaceBindingRuntimeBindings
                                    nameEq actor rightNext rightRegistry
                                  0 concreteControls :
                                    OrderedRegistryControlsRelated name key world
                                      error value
                                      (bindings (replaceBinding @{nameEq} actor
                                        leftNext leftRegistry))
                                      (bindings (replaceBinding @{nameEq} actor
                                        rightNext rightRegistry))
                                  concreteControls = orderedControlsTransport
                                    (sym leftBindings) (sym rightBindings)
                                    replacedControls
                                  0 finalControls :
                                    OrderedRegistryControlsRelated name key world
                                      error value
                                      (bindings (registry
                                        (namedAfter leftNamed)))
                                      (bindings (registry rightAfter))
                                  finalControls = orderedControlsTransport
                                    (cong (\state => bindings (registry state))
                                      leftAfterShape) Refl concreteControls
                                  0 leftSourceToTarget : EffectStateRelated keyEq
                                    (projectEffectState @{nameEq}
                                      (the (SystemState name key value world error)
                                        (MkSystemState leftWorld leftRegistry)))
                                    (projectEffectState @{nameEq}
                                      (namedAfter leftNamed))
                                  leftSourceToTarget = replace
                                    {p = \state => EffectStateRelated keyEq
                                      (projectEffectState @{nameEq}
                                        (the (SystemState name key value world error)
                                          (MkSystemState leftWorld leftRegistry)))
                                      (projectEffectState @{nameEq} state)}
                                    leftAfterShape
                                    (projectTablePreservingReplace nameEq keyEq
                                      actor leftWorld
                                      (MkFiber component leftParent False
                                        leftTable (Inactive Nothing)) leftNext
                                      leftRegistry leftFound Refl)
                                  0 rightSourceToTarget : EffectStateRelated keyEq
                                    (projectEffectState @{nameEq}
                                      (the (SystemState name key value world error)
                                        (MkSystemState rightWorld rightRegistry)))
                                    (projectEffectState @{nameEq} rightAfter)
                                  rightSourceToTarget =
                                    projectTablePreservingReplace nameEq keyEq
                                      actor rightWorld
                                      (MkFiber component rightParent False
                                        rightTable (Inactive Nothing)) rightNext
                                      rightRegistry exactRightFound Refl
                                  0 finalEffects : EffectStateRelated keyEq
                                    (projectEffectState @{nameEq}
                                      (namedAfter leftNamed))
                                    (projectEffectState @{nameEq} rightAfter)
                                  finalEffects = effectTransitive
                                    (effectSymmetric leftSourceToTarget)
                                    (effectTransitive effects rightSourceToTarget)
                              in packageRelatedReplay nameEq keyEq (LBegin actor)
                                (MkSystemState leftWorld leftRegistry)
                                (MkSystemState rightWorld rightRegistry)
                                leftNamed rightAfter
                                rightObservedRaw rightWellFormed finalEffects
                                finalControls
