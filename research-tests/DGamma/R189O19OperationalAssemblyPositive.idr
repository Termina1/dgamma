module DGamma.R189O19OperationalAssemblyPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5O19OperationalAssemblySpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R182O19RevisedSafetyNegative
import DGamma.R182O19RevisedSafetyPositive
import DGamma.R182O19ActualCrossingPositive
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Concrete no-oracle integration regression on the genuine independent
||| two-component six-transition trace. The result owns a NONEMPTY WHOLE
||| derivation, full reached decomposition and actual external relation.
export
0 r189IndependentOperationalSwap :
  OperationalAdjacentBlockSwap Nat R45Key Unit String R45Value
    r45Protocol r45NameEq r45KeyEq r182SwapZeroOne (r182IndependentTrace False)
    r182IndependentDecomposition r182IndependentBundle r182IndependentSafety
r189IndependentOperationalSwap =
  o19ActualOperationalBlockSwap r45NameEq r45KeyEq r45Protocol r182SwapZeroOne
    (r182IndependentTrace False) r182IndependentDecomposition r182IndependentBundle
    r182IndependentSafety r182IndependentUnique

||| Same genuine six-transition trace through the now-CLOSED public O19
||| producer. This checks its original signature and the unique/safety
||| argument order, independently of the direct assembler regression above.
export
0 r189IndependentPublicSwap :
  OperationalAdjacentBlockSwap Nat R45Key Unit String R45Value
    r45Protocol r45NameEq r45KeyEq r182SwapZeroOne (r182IndependentTrace False)
    r182IndependentDecomposition r182IndependentBundle r182IndependentSafety
r189IndependentPublicSwap =
  operationalAdjacentBlockSwapSpike r45NameEq r45KeyEq r45Protocol r182SwapZeroOne
    (r182IndependentTrace False) r182IndependentDecomposition r182IndependentBundle
    r182IndependentUnique r182IndependentSafety
