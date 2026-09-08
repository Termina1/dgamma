module DGamma.R188O19GridCertificationPositive

import DGamma.Coeffects
import DGamma.CP5O19CartesianNumericSpike
import DGamma.CP5O19GridCertificationSpike
import Data.List.Elem
import Data.Nat

%default total
%unbound_implicits off

||| A non-square grid: last bounded pair is present, neither out-of-range
||| coordinate is present, and uniqueness refers to that same explicit grid.
export
0 r188GridCoverageAndBounds :
  (Elem (1, 2) (o19GridPairs Z Z 2 3),
   (Not (Elem (2, 2) (o19GridPairs Z Z 2 3)),
    (Not (Elem (1, 3) (o19GridPairs Z Z 2 3)),
     UniqueKeys (o19GridPairs Z Z 2 3))))
r188GridCoverageAndBounds =
  (gridEveryPair (o19CertifyGrid 2 3) 1 2 (LTESucc (LTESucc LTEZero)) (LTESucc (LTESucc (LTESucc LTEZero))),
   (\member => succNotLTEpred (fst (gridEveryMember (o19CertifyGrid 2 3) 2 2 member)),
    (\member => succNotLTEpred (snd (gridEveryMember (o19CertifyGrid 2 3) 1 3 member)),
     gridPairsUnique (o19CertifyGrid 2 3))))
