module DGamma.R41PointwiseRelianceProjectionNegative

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import Decidable.Equality

%default total

||| STOP-AUDIT pin for the direct representation attempted by the pointwise
||| L-Unload producer.  `FiberControlRelated` intentionally permits distinct
||| proof-bearing owned tables and accumulator functions.  Although `reliedHead`
||| observes only lifecycle shape and committed providers, direct reduction of
||| the two dependent `fiberLifecycle` projections does not erase those stored
||| witnesses.  The real theorem requires a separate observation-level bridge;
||| `Refl` may not be used as that bridge.
0 directPointwiseReliedHeadProjectionDoesNotReduce :
  (nameEq : DecEq name) -> (provider, self, current : name) ->
  (left, right : Fiber name key value world error) ->
  FiberControlRelated left right ->
  reliedHead @{nameEq} provider self (Bind current left) =
    reliedHead @{nameEq} provider self (Bind current right)
directPointwiseReliedHeadProjectionDoesNotReduce nameEq provider self current
  (MkFiber component leftParent leftRetired leftTable leftLifecycle)
  (MkFiber component rightParent rightRetired rightTable rightLifecycle)
  (FibersControlRelated leftParent rightParent leftRetired rightRetired leftTable
    rightTable leftLifecycle rightLifecycle parentSame retiredSame lifecycleSame) =
      case lifecycleSame of
        InactiveControls outcomeSame => case outcomeSame of Refl => Refl
        ReloadingControls remainingSame accumulatorsSame viewsSame =>
          case remainingSame of Refl => case viewsSame of Refl => Refl
        ActiveControls accumulatorsSame viewsSame =>
          case viewsSame of Refl => Refl
        UnloadingControls accumulatorsSame viewsSame outcomesSame =>
          case viewsSame of Refl => case outcomesSame of Refl => Refl
