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
record FixtureCoverage where
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
    (attachedBetweenBlocks (DGamma.L2R3SmallAttached.SmallAttachedBlocks.physicalOrder smallAttachedBlocks))
  0 c12ResidualNF : AttachedNormalForm Nat Bool Unit String (\key => Unit) %search %search smallTrace
    (attachedBetweenBlocks (DGamma.L2R3SmallAttached.SmallAttachedBlocks.physicalOrder smallAttachedBlocks)) 5
  0 barrierResidualCovered : RemainingGapHeadIsRoot %search
    (attachedBetweenBlocks (DGamma.L2R3BarrierBlocks.BarrierAttachedBlocks.physicalOrder barrierAttachedBlocks))
  0 barrierResidualNF : AttachedNormalForm Nat Bool Unit String (\key => Unit) %search %search barrierTrace
    (attachedBetweenBlocks (DGamma.L2R3BarrierBlocks.BarrierAttachedBlocks.physicalOrder barrierAttachedBlocks)) 6
