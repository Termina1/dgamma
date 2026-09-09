module DGamma.L2R3FixtureCoverage

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.CP5L2R1ExtendedZeroGap
import DGamma.L2R2ConditionalGap
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3Attached
import DGamma.L2R3AttachedGap
import DGamma.L2R3SmallAttached
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R3BarrierBlocks
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| No actual action occurrence exists in an empty residual gap. This is the
||| HONESTLY VACUOUS post-attachment NF case, not nonvacuous root membership.
||| Exact occurrence decomposition and structural count additivity refute it.
export
0 emptyGapHasNoOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {state : SystemState name key value world error} ->
  {action : Action name key value world error} ->
  LocatedActionOccurrence action (NoTransitions {state}) -> Void
emptyGapHasNoOccurrence occurrence =
  uninhabited (trans
    (plusSuccRightSucc (transitionCount (beforeActionOccurrence occurrence)) (transitionCount (afterActionOccurrence occurrence)))
    (trans (sym (extendedCountAppend (beforeActionOccurrence occurrence)
      (MoreTransitions (locatedTransition occurrence) (afterActionOccurrence occurrence))))
      (cong transitionCount (actionOccurrenceDecomposition occurrence))))

||| A NONVACUOUS three-entry global bundle catalog: C12 R and barrier R/S,
||| each authenticated by an actual block/bundle/occurrence. Chosen intervals
||| end at the following Begin2 cut. Post-attachment residual-gap NF is
||| HONESTLY VACUOUS (both actual gaps are empty). This record does NOT assert
||| universal coverage or separation for every possible located bundle.
public export
record FixtureCoverage
  (0 c12Gap : Transitions (smallState 5) (smallState 5))
  (0 barrierGap : Transitions (barrierState 6) (barrierState 6)) where
  constructor MkFixtureCoverage
  c12CatalogR : AttachedBundleOccurrence Nat Bool Unit String (\key => Unit) %search %search
    smallTrace (OInsert 3 Root (smallComponent True)) 4
  barrierCatalogR : AttachedBundleOccurrence Nat Bool Unit String (\key => Unit) %search %search
    barrierTrace (OInsert 3 Root (smallComponent True)) 4
  barrierCatalogS : AttachedBundleOccurrence Nat Bool Unit String (\key => Unit) %search %search
    barrierTrace (OInsert 4 Root (smallComponent False)) 5
  0 c12CatalogInterval : (bundleOffset c12CatalogR, bundleOffset c12CatalogR + transitionCount (memberBundle c12CatalogR)) = (4, 5)
  0 barrierCatalogRInterval : (bundleOffset barrierCatalogR, bundleOffset barrierCatalogR + transitionCount (memberBundle barrierCatalogR)) = (4, 6)
  0 barrierCatalogSInterval : (bundleOffset barrierCatalogS, bundleOffset barrierCatalogS + transitionCount (memberBundle barrierCatalogS)) = (4, 6)
  0 c12ResidualCovered : RemainingGapHeadIsRoot %search
    c12Gap
  0 c12ResidualNF : AttachedNormalForm Nat Bool Unit String (\key => Unit) %search %search smallTrace
    c12Gap 5
  0 barrierResidualCovered : RemainingGapHeadIsRoot %search
    barrierGap
  0 barrierResidualNF : AttachedNormalForm Nat Bool Unit String (\key => Unit) %search %search barrierTrace
    barrierGap 6

||| Simultaneous NONVACUOUS catalog membership for the three actual roots,
||| their selected intervals, and HONESTLY VACUOUS NF/coverage for both actual
||| empty residual gaps. Gap indices are erased parameters to avoid repeatedly
||| elaborating closed block producers inside the generic record. No field or
||| actual-gap link is dropped; this result instantiates the exact native gaps.
public export
0 fixtureCoverage : FixtureCoverage
  (attachedBetweenBlocks (DGamma.L2R3SmallAttached.SmallAttachedBlocks.physicalOrder smallAttachedBlocks))
  (attachedBetweenBlocks (DGamma.L2R3BarrierBlocks.BarrierAttachedBlocks.physicalOrder barrierAttachedBlocks))
fixtureCoverage = MkFixtureCoverage smallInsertedBundleMember
  (MkAttachedBundleOccurrence 0 (DGamma.L2R3BarrierBlocks.BarrierAttachedBlocks.freeingBlock barrierAttachedBlocks)
    (barrierState 4) (MoreTransitions (Fired {before = barrierState 1} {afterState = barrierState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 2} {afterState = barrierState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 3} {afterState = barrierState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions))) (ExtendedLifecycleStep (Fired {before = barrierState 1} {afterState = barrierState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 2} {afterState = barrierState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 3} {afterState = barrierState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions)) Refl Refl (ExtendedChildRetireStep (Fired {before = barrierState 2} {afterState = barrierState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 3} {afterState = barrierState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions) 1 (freshFiber (smallComponent True) (ChildOf 0)) Refl Refl Refl (ExtendedChildRemoveStep (Fired {before = barrierState 3} {afterState = barrierState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions 1 (retireFiber (freshFiber (smallComponent True) (ChildOf 0))) Refl Refl Refl ExtendedLifecycleEnd)))
    (MoreTransitions (Fired {before = barrierState 4} {afterState = barrierState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) NoTransitions)) (ForcedBundleStep 3 (smallComponent True) (Fired {before = barrierState 4} {afterState = barrierState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) NoTransitions) Refl (KeyReleased smallRelease) (ForcedBundleStep 4 (smallComponent False) (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) NoTransitions Refl (EarlierForcedRoot {earlier = 3} Here) ForcedBundleEnd)) Refl
    (MkLocatedActionOccurrence (barrierState 4) (barrierState 5) NoTransitions (Fired {before = barrierState 4} {afterState = barrierState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) NoTransitions) Refl Refl) 4 Refl Refl (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))) (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))))
  (MkAttachedBundleOccurrence 0 (DGamma.L2R3BarrierBlocks.BarrierAttachedBlocks.freeingBlock barrierAttachedBlocks)
    (barrierState 4) (MoreTransitions (Fired {before = barrierState 1} {afterState = barrierState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 2} {afterState = barrierState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 3} {afterState = barrierState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions))) (ExtendedLifecycleStep (Fired {before = barrierState 1} {afterState = barrierState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 2} {afterState = barrierState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 3} {afterState = barrierState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions)) Refl Refl (ExtendedChildRetireStep (Fired {before = barrierState 2} {afterState = barrierState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 3} {afterState = barrierState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions) 1 (freshFiber (smallComponent True) (ChildOf 0)) Refl Refl Refl (ExtendedChildRemoveStep (Fired {before = barrierState 3} {afterState = barrierState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions 1 (retireFiber (freshFiber (smallComponent True) (ChildOf 0))) Refl Refl Refl ExtendedLifecycleEnd)))
    (MoreTransitions (Fired {before = barrierState 4} {afterState = barrierState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) NoTransitions)) (ForcedBundleStep 3 (smallComponent True) (Fired {before = barrierState 4} {afterState = barrierState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) NoTransitions) Refl (KeyReleased smallRelease) (ForcedBundleStep 4 (smallComponent False) (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) NoTransitions Refl (EarlierForcedRoot {earlier = 3} Here) ForcedBundleEnd)) Refl
    (MkLocatedActionOccurrence (barrierState 5) (barrierState 6) (MoreTransitions (Fired {before = barrierState 4} {afterState = barrierState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) NoTransitions) (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) NoTransitions Refl Refl) 4 Refl Refl (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))) (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))))))
  Refl Refl Refl
  () (MkAttachedNormalForm (\action, occurrence, root => void (emptyGapHasNoOccurrence occurrence)))
  () (MkAttachedNormalForm (\action, occurrence, root => void (emptyGapHasNoOccurrence occurrence)))
