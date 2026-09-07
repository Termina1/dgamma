module DGamma.R182O19RevisedSafetyNegative

import DGamma.Calculus
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
