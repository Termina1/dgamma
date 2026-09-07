module DGamma.R182O19RevisedSafetyNegative

import DGamma.Core
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.Unified
import DGamma.R180O19ObservedCompletion
import Data.Nat
import DGamma.CP3
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.Metatheory
import DGamma.Section3Example
import DGamma.R179O19ObservedExecution
import DGamma.R181O19SafetyCompletion
import DGamma.R181O19LocatedBlocks
import DGamma.R181O19BundlePrerequisites
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| A3: exact adjacent actor order used by the certified R181 pair.
public export
r182SwapZeroOne : AdjacentActorOrderSwap Nat [0, 1] [1, 0]
r182SwapZeroOne = MkAdjacentActorOrderSwap [] 0 1 [] Refl Refl
  (\same => case same of Refl impossible)

||| A4: full revised safety is impossible for the ACTUAL count7 blocks, for
||| EVERY candidate bundle. No TraceIndependent or bundle inhabitant is assumed
||| to establish rejection; the single new field contradicts the certified raw
||| consumer Begin=None at exactly the provider block's source.
public export
0 r182DependentPairRejected :
  (premises : ReplayInvariantBundle Nat ToyKey ToyRuntime String ToyValue
    r181Protocol (the (DecEq Nat) %search) (the (DecEq ToyKey) %search) r181WholeTrace) ->
  (safety : AdjacentActorSwapSafety Nat ToyKey ToyRuntime String ToyValue
    r181Protocol (the (DecEq Nat) %search) (the (DecEq ToyKey) %search)
    r182SwapZeroOne r181WholeTrace r181ActorBlockDecomposition premises) -> Void
r182DependentPairRejected premises safety =
  case trans (sym (Builtin.snd (Builtin.snd r181TraceStructure)))
    (checkedActionProjects (the (DecEq Nat) %search) (the (DecEq ToyKey) %search)
      (LBegin 1) r179ObservedRootSource
      (earlyApplicationFinal (safetyRightOpeningEarly safety)) LBeginTag
      (earlyApplicationChecked (safetyRightOpeningEarly safety))) of Refl impossible
