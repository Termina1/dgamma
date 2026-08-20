module DGamma.CP4DeletionRelationalLifecycleAdvanceCases

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionRelationalLifecycleCore
import DGamma.CP4DeletionSelectedForeignLifecycleAdvanceOutcome
import DGamma.CP4DeletionSelectedForeignLifecycleReplayCore
import DGamma.CP4RecoveryForeignCommute
import DGamma.Unified
import Decidable.Equality

%default total

0 partialMapsEquivalentSymmetric :
  (eq : Equivalence state) ->
  PartialMapsEquivalent eq left right ->
  PartialMapsEquivalent eq right left
partialMapsEquivalentSymmetric eq maps input =
  partialSymmetric eq (maps input)

0 effectRelatedSymmetric : EffectStateRelated keyEq left right ->
  EffectStateRelated keyEq right left
effectRelatedSymmetric (MkEffectStateRelated ambient tables) =
  MkEffectStateRelated (sym ambient) (\actor => sym (tables actor))

0 effectRelatedTransitive : EffectStateRelated keyEq left middle ->
  EffectStateRelated keyEq middle right -> EffectStateRelated keyEq left right
effectRelatedTransitive (MkEffectStateRelated firstAmbient firstTables)
  (MkEffectStateRelated secondAmbient secondTables) =
    MkEffectStateRelated (trans firstAmbient secondAmbient)
      (\actor => trans (firstTables actor) (secondTables actor))

0 controlAdvanceEffects :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (leftWorld, rightWorld : world) ->
  (left, right : Registry name key value world error) ->
  (leftOld, rightOld, leftNext, rightNext : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor left = Just leftOld ->
  lookupFiber @{nameEq} actor right = Just rightOld ->
  ownedValues (fiberTable leftNext) = ownedValues (fiberTable leftOld) ->
  ownedValues (fiberTable rightNext) = ownedValues (fiberTable rightOld) ->
  EffectStateRelated keyEq
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState leftWorld left)))
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState rightWorld right))) ->
  (leftAfter : SystemState name key value world error) ->
  MkSystemState leftWorld (replaceBinding @{nameEq} actor leftNext left) =
    leftAfter ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} leftAfter)
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState rightWorld
          (replaceBinding @{nameEq} actor rightNext right))))
controlAdvanceEffects nameEq keyEq actor leftWorld rightWorld left right leftOld
  rightOld leftNext rightNext leftFound rightFound leftTableSame rightTableSame
  effects leftAfter leftShape =
    let 0 leftSourceToTarget : EffectStateRelated keyEq
          (projectEffectState @{nameEq}
            (the (SystemState name key value world error)
              (MkSystemState leftWorld left)))
          (projectEffectState @{nameEq} leftAfter)
        leftSourceToTarget = replace
          {p = \state => EffectStateRelated keyEq
            (projectEffectState @{nameEq}
              (the (SystemState name key value world error)
                (MkSystemState leftWorld left)))
            (projectEffectState @{nameEq} state)}
          leftShape (projectTablePreservingReplace nameEq keyEq actor leftWorld
            leftOld leftNext left leftFound leftTableSame)
        0 rightSourceToTarget : EffectStateRelated keyEq
          (projectEffectState @{nameEq}
            (the (SystemState name key value world error)
              (MkSystemState rightWorld right)))
          (projectEffectState @{nameEq}
            (the (SystemState name key value world error)
              (MkSystemState rightWorld
                (replaceBinding @{nameEq} actor rightNext right))))
        rightSourceToTarget = projectTablePreservingReplace nameEq keyEq actor
          rightWorld rightOld rightNext right rightFound rightTableSame
    in effectRelatedTransitive (effectRelatedSymmetric leftSourceToTarget)
      (effectRelatedTransitive effects rightSourceToTarget)

0 runtimeAdvanceEffects :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (leftWorld, rightWorld : world) ->
  (left, right : Registry name key value world error) ->
  (leftOld, rightOld, leftNext, rightNext : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor left = Just leftOld ->
  lookupFiber @{nameEq} actor right = Just rightOld ->
  (leftAfterLocal, rightAfterLocal : LocalState key value world provision) ->
  ownedValues (fiberTable leftNext) =
    ownedValues (localTable leftAfterLocal) ->
  ownedValues (fiberTable rightNext) =
    ownedValues (localTable rightAfterLocal) ->
  EffectStateRelated keyEq
    (setEffectTable @{nameEq} actor (ownedValues (localTable leftAfterLocal))
      (setEffectAmbient (localWorld leftAfterLocal)
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState leftWorld left)))))
    (setEffectTable @{nameEq} actor (ownedValues (localTable rightAfterLocal))
      (setEffectAmbient (localWorld rightAfterLocal)
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState rightWorld right))))) ->
  (leftAfter : SystemState name key value world error) ->
  MkSystemState (localWorld leftAfterLocal)
    (replaceBinding @{nameEq} actor leftNext left) = leftAfter ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} leftAfter)
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState (localWorld rightAfterLocal)
          (replaceBinding @{nameEq} actor rightNext right))))
runtimeAdvanceEffects nameEq keyEq actor leftWorld rightWorld left right leftOld
  rightOld leftNext rightNext leftFound rightFound leftAfterLocal rightAfterLocal
  leftTableSame rightTableSame primitiveRelated leftAfter leftShape =
    let 0 leftUpdateToTarget : EffectStateRelated keyEq
          (setEffectTable @{nameEq} actor
            (ownedValues (localTable leftAfterLocal))
            (setEffectAmbient (localWorld leftAfterLocal)
              (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState leftWorld left)))))
          (projectEffectState @{nameEq} leftAfter)
        leftUpdateToTarget = replace
          {p = \state => EffectStateRelated keyEq
            (setEffectTable @{nameEq} actor
              (ownedValues (localTable leftAfterLocal))
              (setEffectAmbient (localWorld leftAfterLocal)
                (projectEffectState @{nameEq}
                  (the (SystemState name key value world error)
                    (MkSystemState leftWorld left)))))
            (projectEffectState @{nameEq} state)}
          leftShape (projectRuntimeReplace nameEq keyEq actor leftWorld
            (localWorld leftAfterLocal) leftOld leftNext left leftFound
            (ownedValues (localTable leftAfterLocal)) leftTableSame)
        0 rightUpdateToTarget : EffectStateRelated keyEq
          (setEffectTable @{nameEq} actor
            (ownedValues (localTable rightAfterLocal))
            (setEffectAmbient (localWorld rightAfterLocal)
              (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState rightWorld right)))))
          (projectEffectState @{nameEq}
            (the (SystemState name key value world error)
              (MkSystemState (localWorld rightAfterLocal)
                (replaceBinding @{nameEq} actor rightNext right))))
        rightUpdateToTarget = projectRuntimeReplace nameEq keyEq actor
          rightWorld (localWorld rightAfterLocal) rightOld rightNext right
          rightFound (ownedValues (localTable rightAfterLocal)) rightTableSame
    in effectRelatedTransitive (effectRelatedSymmetric leftUpdateToTarget)
      (effectRelatedTransitive primitiveRelated rightUpdateToTarget)

||| Empty-continuation L-Finish/L-Divert reconstruction.  Provider-frame guard
||| saturation supplies the two equal target-match observations to this final
||| evaluator constructor.
public export
0 replayRelatedAdvanceEmptyControls :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) ->
  (planAmbient, survivorAmbient : world) ->
  (plan, survivor : Registry name key value world error) ->
  (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) -> (retiredFlag : Bool) ->
  (leftTable, rightTable : OwnedTable key value
    (componentProvisions component)) ->
  (leftAccumulator, rightAccumulator : LocalState key value world
    (componentProvisions component) -> LocalState key value world
    (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  leftParent = rightParent ->
  AccumulatorRelated leftAccumulator rightAccumulator ->
  (leftFound : lookupFiber @{nameEq} actor plan = Just
    (MkFiber component leftParent retiredFlag leftTable
      (Reloading [] leftAccumulator view))) ->
  (rightFound : lookupFiber @{nameEq} actor survivor = Just
    (MkFiber component rightParent retiredFlag rightTable
      (Reloading [] rightAccumulator view))) ->
  OrderedRegistryControlsRelated name key world error value
    (bindings plan) (bindings survivor) ->
  EffectStateRelated keyEq
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState planAmbient plan)))
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState survivorAmbient survivor))) ->
  (matches : Bool) ->
  targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq} {name = name} {key = key}
      {value = value} {world = world} {error = error}
      (MkFiber component leftParent retiredFlag leftTable
        (Reloading [] leftAccumulator view)) plan) view = matches ->
  targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq} {name = name} {key = key}
      {value = value} {world = world} {error = error}
      (MkFiber component rightParent retiredFlag rightTable
        (Reloading [] rightAccumulator view)) survivor) view = matches ->
  (tag : RuleTag) ->
  (planAfter : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (LAdvance actor))
    (MkSystemState planAmbient plan) = Just (tag, planAfter) ->
  FullLifecycleControlReplay name key world error value nameEq keyEq
    (LAdvance actor) tag planAfter
    (MkSystemState survivorAmbient survivor)
replayRelatedAdvanceEmptyControls {name} {key} {world} {error} {value}
  nameEq keyEq actor planAmbient survivorAmbient plan
  survivor component leftParent rightParent retiredFlag leftTable rightTable
  leftAccumulator rightAccumulator view parentSame accumulatorsSame leftFound
  rightFound sourceOrdered sourceEffects matches leftMatches rightMatches tag planAfter raw
  with (matches)
  replayRelatedAdvanceEmptyControls nameEq keyEq actor
    planAmbient survivorAmbient plan survivor component leftParent rightParent
    retiredFlag leftTable rightTable leftAccumulator rightAccumulator view
    parentSame accumulatorsSame leftFound rightFound sourceOrdered sourceEffects matches
    leftMatches rightMatches tag planAfter raw | True =
      let leftNext : Fiber name key value world error
          leftNext = MkFiber component leftParent retiredFlag leftTable
            (Active leftAccumulator view)
          rightNext : Fiber name key value world error
          rightNext = MkFiber component rightParent retiredFlag rightTable
            (Active rightAccumulator view)
          0 planConcrete : applyAction @{nameEq} @{keyEq}
            (the (Action name key value world error) (LAdvance actor))
            (MkSystemState planAmbient plan) = Just (LFinishTag,
              MkSystemState planAmbient
                (replaceBinding @{nameEq} actor leftNext plan))
          planConcrete = rewrite leftFound in rewrite leftMatches in Refl
          0 pairSame : (LFinishTag, MkSystemState planAmbient
              (replaceBinding @{nameEq} actor leftNext plan)) = (tag, planAfter)
          pairSame = justInjective (trans (sym planConcrete) raw)
          0 nextControls : FiberControlRelated leftNext rightNext
          nextControls = FibersControlRelated leftParent rightParent retiredFlag
            retiredFlag leftTable rightTable (Active leftAccumulator view)
            (Active rightAccumulator view) parentSame Refl
            (ActiveControls {error = error} accumulatorsSame Refl)
          0 survivorRaw : applyAction @{nameEq} @{keyEq}
            (the (Action name key value world error) (LAdvance actor))
            (MkSystemState survivorAmbient survivor) = Just (LFinishTag,
              MkSystemState survivorAmbient
                (replaceBinding @{nameEq} actor rightNext survivor))
          survivorRaw = rewrite rightFound in rewrite rightMatches in Refl
      in case pairSame of
        Refl => packageFullLifecycleReplacementReplay nameEq keyEq
          actor (LAdvance actor) LFinishTag planAfter
          survivorAmbient plan survivor leftNext rightNext nextControls
          sourceOrdered planAmbient Refl survivorAmbient survivorRaw
          (controlAdvanceEffects nameEq keyEq actor planAmbient survivorAmbient
            plan survivor
            (MkFiber component leftParent retiredFlag leftTable
              (Reloading [] leftAccumulator view))
            (MkFiber component rightParent retiredFlag rightTable
              (Reloading [] rightAccumulator view))
            leftNext rightNext leftFound rightFound Refl Refl sourceEffects
            planAfter Refl)
         
  replayRelatedAdvanceEmptyControls nameEq keyEq actor
    planAmbient survivorAmbient plan survivor component leftParent rightParent
    retiredFlag leftTable rightTable leftAccumulator rightAccumulator view
    parentSame accumulatorsSame leftFound rightFound sourceOrdered sourceEffects matches
    leftMatches rightMatches tag planAfter raw | False =
      let leftNext : Fiber name key value world error
          leftNext = MkFiber component leftParent retiredFlag leftTable
            (Unloading leftAccumulator view Nothing)
          rightNext : Fiber name key value world error
          rightNext = MkFiber component rightParent retiredFlag rightTable
            (Unloading rightAccumulator view Nothing)
          0 planConcrete : applyAction @{nameEq} @{keyEq}
            (the (Action name key value world error) (LAdvance actor))
            (MkSystemState planAmbient plan) = Just (LDivertTag,
              MkSystemState planAmbient
                (replaceBinding @{nameEq} actor leftNext plan))
          planConcrete = rewrite leftFound in rewrite leftMatches in Refl
          0 pairSame : (LDivertTag, MkSystemState planAmbient
              (replaceBinding @{nameEq} actor leftNext plan)) = (tag, planAfter)
          pairSame = justInjective (trans (sym planConcrete) raw)
          0 nextControls : FiberControlRelated leftNext rightNext
          nextControls = FibersControlRelated leftParent rightParent retiredFlag
            retiredFlag leftTable rightTable
            (Unloading leftAccumulator view Nothing)
            (Unloading rightAccumulator view Nothing) parentSame Refl
            (UnloadingControls accumulatorsSame Refl Refl)
          0 survivorRaw : applyAction @{nameEq} @{keyEq}
            (the (Action name key value world error) (LAdvance actor))
            (MkSystemState survivorAmbient survivor) = Just (LDivertTag,
              MkSystemState survivorAmbient
                (replaceBinding @{nameEq} actor rightNext survivor))
          survivorRaw = rewrite rightFound in rewrite rightMatches in Refl
      in case pairSame of
        Refl => packageFullLifecycleReplacementReplay nameEq keyEq
          actor (LAdvance actor) LDivertTag planAfter
          survivorAmbient plan survivor leftNext rightNext nextControls
          sourceOrdered planAmbient Refl survivorAmbient survivorRaw
          (controlAdvanceEffects nameEq keyEq actor planAmbient survivorAmbient
            plan survivor
            (MkFiber component leftParent retiredFlag leftTable
              (Reloading [] leftAccumulator view))
            (MkFiber component rightParent retiredFlag rightTable
              (Reloading [] rightAccumulator view))
            leftNext rightNext leftFound rightFound Refl Refl sourceEffects
            planAfter Refl)
         

||| L-Raise reconstruction uses the repaired Definition-60 failure clause:
||| both evaluations expose the same exact observable error.
public export
0 replayRelatedAdvanceRaisedControls :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) ->
  (planAmbient, survivorAmbient : world) ->
  (plan, survivor : Registry name key value world error) ->
  (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) -> (retiredFlag : Bool) ->
  (leftTable, rightTable : OwnedTable key value
    (componentProvisions component)) ->
  (step : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (rest : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (leftAccumulator, rightAccumulator : LocalState key value world
    (componentProvisions component) -> LocalState key value world
    (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  leftParent = rightParent ->
  AccumulatorRelated leftAccumulator rightAccumulator ->
  (leftFound : lookupFiber @{nameEq} actor plan = Just
    (MkFiber component leftParent retiredFlag leftTable
      (Reloading (step :: rest) leftAccumulator view))) ->
  (rightFound : lookupFiber @{nameEq} actor survivor = Just
    (MkFiber component rightParent retiredFlag rightTable
      (Reloading (step :: rest) rightAccumulator view))) ->
  OrderedRegistryControlsRelated name key world error value
    (bindings plan) (bindings survivor) ->
  EffectStateRelated keyEq
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState planAmbient plan)))
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState survivorAmbient survivor))) ->
  (leftCapability, rightCapability : DepValues key value
    (dependencies (componentDependencies component))) ->
  resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (dependencies (componentDependencies component)) view plan =
    Just leftCapability ->
  resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (dependencies (componentDependencies component)) view survivor =
    Just rightCapability ->
  (leftError, rightError : error) -> leftError = rightError ->
  runStepEffect step leftCapability
    (MkLocalState planAmbient
      (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component)
        (ownedValues leftTable))) = Left leftError ->
  runStepEffect step rightCapability
    (MkLocalState survivorAmbient
      (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component)
        (ownedValues rightTable))) = Left rightError ->
  (tag : RuleTag) ->
  (planAfter : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (LAdvance actor))
    (MkSystemState planAmbient plan) = Just (tag, planAfter) ->
  FullLifecycleControlReplay name key world error value nameEq keyEq
    (LAdvance actor) tag planAfter
    (MkSystemState survivorAmbient survivor)
replayRelatedAdvanceRaisedControls {name} {key} {world} {error} {value}
  nameEq keyEq actor planAmbient survivorAmbient plan
  survivor component leftParent rightParent retiredFlag leftTable rightTable
  step rest leftAccumulator rightAccumulator view parentSame accumulatorsSame
  leftFound rightFound sourceOrdered sourceEffects leftCapability rightCapability leftResolved
  rightResolved leftError rightError errorsSame leftRan rightRan tag planAfter raw
  =
    let leftNext : Fiber name key value world error
        leftNext = MkFiber component leftParent retiredFlag leftTable
          (Unloading leftAccumulator view (Just leftError))
        rightNext : Fiber name key value world error
        rightNext = MkFiber component rightParent retiredFlag rightTable
          (Unloading rightAccumulator view (Just rightError))
        0 planConcrete : applyAction @{nameEq} @{keyEq}
          (the (Action name key value world error) (LAdvance actor))
          (MkSystemState planAmbient plan) = Just (LRaiseTag,
            MkSystemState planAmbient
              (replaceBinding @{nameEq} actor leftNext plan))
        planConcrete = rewrite leftFound in rewrite leftResolved in
          rewrite leftRan in Refl
        0 pairSame : (LRaiseTag, MkSystemState planAmbient
            (replaceBinding @{nameEq} actor leftNext plan)) = (tag, planAfter)
        pairSame = justInjective (trans (sym planConcrete) raw)
        0 nextControls : FiberControlRelated leftNext rightNext
        nextControls = FibersControlRelated leftParent rightParent retiredFlag
          retiredFlag leftTable rightTable
          (Unloading leftAccumulator view (Just leftError))
          (Unloading rightAccumulator view (Just rightError)) parentSame Refl
          (UnloadingControls accumulatorsSame Refl (cong Just errorsSame))
        0 survivorRaw : applyAction @{nameEq} @{keyEq}
          (the (Action name key value world error) (LAdvance actor))
          (MkSystemState survivorAmbient survivor) = Just (LRaiseTag,
            MkSystemState survivorAmbient
              (replaceBinding @{nameEq} actor rightNext survivor))
        survivorRaw = rewrite rightFound in rewrite rightResolved in
          rewrite rightRan in Refl
    in case pairSame of
      Refl => packageFullLifecycleReplacementReplay nameEq keyEq actor (LAdvance actor) LRaiseTag planAfter survivorAmbient
        plan survivor leftNext rightNext nextControls sourceOrdered planAmbient
        Refl survivorAmbient survivorRaw
        (controlAdvanceEffects nameEq keyEq actor planAmbient survivorAmbient
          plan survivor
          (MkFiber component leftParent retiredFlag leftTable
            (Reloading (step :: rest) leftAccumulator view))
          (MkFiber component rightParent retiredFlag rightTable
            (Reloading (step :: rest) rightAccumulator view))
          leftNext rightNext leftFound rightFound Refl Refl sourceEffects
          planAfter Refl)

||| Successful L-Advance reconstruction.  The yielded inverse equivalence is
||| the successful constructor of repaired Equation 55 (survivor-to-plan
||| orientation); symmetry plus the local projection lemma feeds the original
||| and survivor callbacks to `pushLocalUndoRuntimeRelated`.
public export
0 replayRelatedAdvanceSuccessfulControls :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) ->
  (planAmbient, survivorAmbient : world) ->
  (plan, survivor : Registry name key value world error) ->
  (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) -> (retiredFlag : Bool) ->
  (leftTable, rightTable : OwnedTable key value
    (componentProvisions component)) ->
  (step : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (rest : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (leftAccumulator, rightAccumulator : LocalState key value world
    (componentProvisions component) -> LocalState key value world
    (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  leftParent = rightParent ->
  AccumulatorRelated leftAccumulator rightAccumulator ->
  (leftFound : lookupFiber @{nameEq} actor plan = Just
    (MkFiber component leftParent retiredFlag leftTable
      (Reloading (step :: rest) leftAccumulator view))) ->
  (rightFound : lookupFiber @{nameEq} actor survivor = Just
    (MkFiber component rightParent retiredFlag rightTable
      (Reloading (step :: rest) rightAccumulator view))) ->
  OrderedRegistryControlsRelated name key world error value
    (bindings plan) (bindings survivor) ->
  EffectStateRelated keyEq
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState planAmbient plan)))
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState survivorAmbient survivor))) ->
  (leftCapability, rightCapability : DepValues key value
    (dependencies (componentDependencies component))) ->
  resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (dependencies (componentDependencies component)) view plan =
    Just leftCapability ->
  resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (dependencies (componentDependencies component)) view survivor =
    Just rightCapability ->
  (leftAfter, rightAfter : LocalState key value world
    (componentProvisions component)) ->
  (leftUndo, rightUndo : LocalState key value world
    (componentProvisions component) -> LocalState key value world
    (componentProvisions component)) ->
  runStepEffect step leftCapability
    (MkLocalState planAmbient
      (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component)
        (ownedValues leftTable))) = Right (leftAfter, leftUndo) ->
  runStepEffect step rightCapability
    (MkLocalState survivorAmbient
      (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component)
        (ownedValues rightTable))) = Right (rightAfter, rightUndo) ->
  EffectStateRelated keyEq
    (setEffectTable @{nameEq} actor (ownedValues (localTable leftAfter))
      (setEffectAmbient (localWorld leftAfter)
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState planAmbient plan)))))
    (setEffectTable @{nameEq} actor (ownedValues (localTable rightAfter))
      (setEffectAmbient (localWorld rightAfter)
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState survivorAmbient survivor))))) ->
  PartialMapsEquivalent (EffectStateEquivalence keyEq)
    (yieldedInverseEffectMap nameEq keyEq actor
      (componentProvisions component) rightUndo)
    (yieldedInverseEffectMap nameEq keyEq actor
      (componentProvisions component) leftUndo) ->
  (matches : Bool) ->
  targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq} {name = name} {key = key}
      {value = value} {world = world} {error = error}
      (MkFiber component leftParent retiredFlag leftTable
        (Reloading (step :: rest) leftAccumulator view)) plan) view = matches ->
  targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq} {name = name} {key = key}
      {value = value} {world = world} {error = error}
      (MkFiber component rightParent retiredFlag rightTable
        (Reloading (step :: rest) rightAccumulator view)) survivor) view =
    matches ->
  (tag : RuleTag) ->
  (planAfter : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (LAdvance actor))
    (MkSystemState planAmbient plan) = Just (tag, planAfter) ->
  FullLifecycleControlReplay name key world error value nameEq keyEq
    (LAdvance actor) tag planAfter
    (MkSystemState survivorAmbient survivor)
replayRelatedAdvanceSuccessfulControls {name} {key} {world} {error} {value}
  nameEq keyEq actor planAmbient survivorAmbient plan
  survivor component leftParent rightParent retiredFlag leftTable rightTable
  step rest leftAccumulator rightAccumulator view parentSame accumulatorsSame
  leftFound rightFound sourceOrdered sourceEffects leftCapability rightCapability leftResolved
  rightResolved leftAfter rightAfter leftUndo rightUndo leftRan rightRan primitiveEffects undoMaps
  matches leftMatches rightMatches tag planAfter raw =
    let 0 originalToSurvivorMaps = partialMapsEquivalentSymmetric
          (EffectStateEquivalence keyEq) undoMaps
        0 undosRelated = yieldedMapsGiveLocalUndoRuntimeRelated nameEq keyEq actor
          (componentProvisions component) leftUndo rightUndo
          originalToSurvivorMaps
        0 pushedRelated = pushLocalUndoRuntimeRelated keyEq
          (componentProvisions component) leftAccumulator rightAccumulator
          leftUndo rightUndo accumulatorsSame undosRelated
    in successfulByMatch matches Refl pushedRelated
  where
  0 successfulByMatch :
    (observed : Bool) -> observed = matches ->
    AccumulatorRelated
      (pushLocalUndo @{keyEq} (componentProvisions component) leftAccumulator
        leftUndo)
      (pushLocalUndo @{keyEq} (componentProvisions component) rightAccumulator
        rightUndo) ->
    FullLifecycleControlReplay name key world error value nameEq keyEq
      (LAdvance actor) tag planAfter
      (MkSystemState survivorAmbient survivor)
  successfulByMatch False observedMatches pushedRelated =
    let 0 leftObserved = trans leftMatches (sym observedMatches)
        0 rightObserved = trans rightMatches (sym observedMatches)
        leftNext : Fiber name key value world error
        leftNext = MkFiber component leftParent retiredFlag (localTable leftAfter)
          (Unloading (pushLocalUndo (componentProvisions component)
            leftAccumulator leftUndo) view Nothing)
        rightNext : Fiber name key value world error
        rightNext = MkFiber component rightParent retiredFlag
          (localTable rightAfter)
          (Unloading (pushLocalUndo (componentProvisions component)
            rightAccumulator rightUndo) view Nothing)
        0 planConcrete : applyAction @{nameEq} @{keyEq}
          (the (Action name key value world error) (LAdvance actor))
          (MkSystemState planAmbient plan) = Just (LDivertTag,
            MkSystemState (localWorld leftAfter)
              (replaceBinding @{nameEq} actor leftNext plan))
        planConcrete = rewrite leftFound in rewrite leftResolved in
          rewrite leftRan in rewrite leftObserved in Refl
        0 pairSame : (LDivertTag, MkSystemState (localWorld leftAfter)
            (replaceBinding @{nameEq} actor leftNext plan)) = (tag, planAfter)
        pairSame = justInjective (trans (sym planConcrete) raw)
        0 nextControls : FiberControlRelated leftNext rightNext
        nextControls = FibersControlRelated leftParent rightParent retiredFlag
          retiredFlag (localTable leftAfter) (localTable rightAfter)
          (Unloading (pushLocalUndo (componentProvisions component)
            leftAccumulator leftUndo) view Nothing)
          (Unloading (pushLocalUndo (componentProvisions component)
            rightAccumulator rightUndo) view Nothing) parentSame Refl
          (UnloadingControls pushedRelated Refl Refl)
        0 survivorRaw : applyAction @{nameEq} @{keyEq}
          (the (Action name key value world error) (LAdvance actor))
          (MkSystemState survivorAmbient survivor) = Just (LDivertTag,
            MkSystemState (localWorld rightAfter)
              (replaceBinding @{nameEq} actor rightNext survivor))
        survivorRaw = rewrite rightFound in rewrite rightResolved in
          rewrite rightRan in rewrite rightObserved in Refl
    in case pairSame of
      Refl => packageFullLifecycleReplacementReplay nameEq keyEq actor (LAdvance actor) LDivertTag planAfter survivorAmbient
        plan survivor leftNext rightNext nextControls sourceOrdered
        (localWorld leftAfter) Refl (localWorld rightAfter) survivorRaw
        (runtimeAdvanceEffects nameEq keyEq actor planAmbient survivorAmbient
          plan survivor
          (MkFiber component leftParent retiredFlag leftTable
            (Reloading (step :: rest) leftAccumulator view))
          (MkFiber component rightParent retiredFlag rightTable
            (Reloading (step :: rest) rightAccumulator view))
          leftNext rightNext leftFound rightFound leftAfter rightAfter Refl Refl
          primitiveEffects planAfter Refl)
       
  successfulByMatch True observedMatches pushedRelated with (rest) proof restShape
    successfulByMatch True observedMatches pushedRelated | [] =
      let 0 leftObserved = trans leftMatches (sym observedMatches)
          0 rightObserved = trans rightMatches (sym observedMatches)
          leftNext : Fiber name key value world error
          leftNext = MkFiber component leftParent retiredFlag
            (localTable leftAfter)
            (Active (pushLocalUndo (componentProvisions component)
              leftAccumulator leftUndo) view)
          rightNext : Fiber name key value world error
          rightNext = MkFiber component rightParent retiredFlag
            (localTable rightAfter)
            (Active (pushLocalUndo (componentProvisions component)
              rightAccumulator rightUndo) view)
          0 planConcrete : applyAction @{nameEq} @{keyEq}
            (the (Action name key value world error) (LAdvance actor))
            (MkSystemState planAmbient plan) = Just (LFinishTag,
              MkSystemState (localWorld leftAfter)
                (replaceBinding @{nameEq} actor leftNext plan))
          planConcrete = rewrite leftFound in rewrite leftResolved in
            rewrite leftRan in rewrite leftObserved in
            rewrite restShape in Refl
          0 pairSame : (LFinishTag, MkSystemState (localWorld leftAfter)
              (replaceBinding @{nameEq} actor leftNext plan)) = (tag, planAfter)
          pairSame = justInjective (trans (sym planConcrete) raw)
          0 nextControls : FiberControlRelated leftNext rightNext
          nextControls = FibersControlRelated leftParent rightParent retiredFlag
            retiredFlag (localTable leftAfter) (localTable rightAfter)
            (Active (pushLocalUndo (componentProvisions component)
              leftAccumulator leftUndo) view)
            (Active (pushLocalUndo (componentProvisions component)
              rightAccumulator rightUndo) view) parentSame Refl
            (ActiveControls {error = error} pushedRelated Refl)
          0 survivorRaw : applyAction @{nameEq} @{keyEq}
            (the (Action name key value world error) (LAdvance actor))
            (MkSystemState survivorAmbient survivor) = Just (LFinishTag,
              MkSystemState (localWorld rightAfter)
                (replaceBinding @{nameEq} actor rightNext survivor))
          survivorRaw = rewrite rightFound in rewrite rightResolved in
            rewrite rightRan in rewrite rightObserved in
            rewrite restShape in Refl
      in case pairSame of
        Refl => packageFullLifecycleReplacementReplay nameEq keyEq
          actor (LAdvance actor) LFinishTag planAfter
          survivorAmbient plan survivor leftNext rightNext nextControls
          sourceOrdered (localWorld leftAfter) Refl (localWorld rightAfter)
          survivorRaw
          (runtimeAdvanceEffects nameEq keyEq actor planAmbient survivorAmbient
          plan survivor
          (MkFiber component leftParent retiredFlag leftTable
            (Reloading (step :: rest) leftAccumulator view))
          (MkFiber component rightParent retiredFlag rightTable
            (Reloading (step :: rest) rightAccumulator view))
          leftNext rightNext leftFound rightFound leftAfter rightAfter Refl Refl
          primitiveEffects planAfter Refl)
    successfulByMatch True observedMatches pushedRelated | next :: later =
      let 0 leftObserved = trans leftMatches (sym observedMatches)
          0 rightObserved = trans rightMatches (sym observedMatches)
          leftNext : Fiber name key value world error
          leftNext = MkFiber component leftParent retiredFlag
            (localTable leftAfter)
            (Reloading (next :: later)
              (pushLocalUndo (componentProvisions component) leftAccumulator
                leftUndo) view)
          rightNext : Fiber name key value world error
          rightNext = MkFiber component rightParent retiredFlag
            (localTable rightAfter)
            (Reloading (next :: later)
              (pushLocalUndo (componentProvisions component) rightAccumulator
                rightUndo) view)
          0 planConcrete : applyAction @{nameEq} @{keyEq}
            (the (Action name key value world error) (LAdvance actor))
            (MkSystemState planAmbient plan) = Just (LIterTag,
              MkSystemState (localWorld leftAfter)
                (replaceBinding @{nameEq} actor leftNext plan))
          planConcrete = rewrite leftFound in rewrite leftResolved in
            rewrite leftRan in rewrite leftObserved in
            rewrite restShape in Refl
          0 pairSame : (LIterTag, MkSystemState (localWorld leftAfter)
              (replaceBinding @{nameEq} actor leftNext plan)) = (tag, planAfter)
          pairSame = justInjective (trans (sym planConcrete) raw)
          0 nextControls : FiberControlRelated leftNext rightNext
          nextControls = FibersControlRelated leftParent rightParent retiredFlag
            retiredFlag (localTable leftAfter) (localTable rightAfter)
            (Reloading (next :: later)
              (pushLocalUndo (componentProvisions component) leftAccumulator
                leftUndo) view)
            (Reloading (next :: later)
              (pushLocalUndo (componentProvisions component) rightAccumulator
                rightUndo) view) parentSame Refl
            (ReloadingControls Refl pushedRelated Refl)
          0 survivorRaw : applyAction @{nameEq} @{keyEq}
            (the (Action name key value world error) (LAdvance actor))
            (MkSystemState survivorAmbient survivor) = Just (LIterTag,
              MkSystemState (localWorld rightAfter)
                (replaceBinding @{nameEq} actor rightNext survivor))
          survivorRaw = rewrite rightFound in rewrite rightResolved in
            rewrite rightRan in rewrite rightObserved in
            rewrite restShape in Refl
      in case pairSame of
        Refl => packageFullLifecycleReplacementReplay nameEq keyEq
          actor (LAdvance actor) LIterTag planAfter survivorAmbient
          plan survivor leftNext rightNext nextControls sourceOrdered
          (localWorld leftAfter) Refl (localWorld rightAfter) survivorRaw
          (runtimeAdvanceEffects nameEq keyEq actor planAmbient survivorAmbient
          plan survivor
          (MkFiber component leftParent retiredFlag leftTable
            (Reloading (step :: rest) leftAccumulator view))
          (MkFiber component rightParent retiredFlag rightTable
            (Reloading (step :: rest) rightAccumulator view))
          leftNext rightNext leftFound rightFound leftAfter rightAfter Refl Refl
          primitiveEffects planAfter Refl)
         
