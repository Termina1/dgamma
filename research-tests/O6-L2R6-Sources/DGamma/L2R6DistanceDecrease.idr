module DGamma.L2R6DistanceDecrease

import Data.Nat

%default total
%unbound_implicits off

||| One physical cut moved left decreases distance by exactly one when its
||| fixed target is not crossed. Single LTE elimination. Authentication of
||| stable targets/all other roots under native swaps is a separate obligation.
export
0 distanceOneLeft : {position, target : Nat} -> LTE target position ->
  minus (S position) target = S (minus position target)
distanceOneLeft {position} LTEZero = sym (cong S (minusZeroRight position))
distanceOneLeft (LTESucc bounded) = distanceOneLeft bounded
