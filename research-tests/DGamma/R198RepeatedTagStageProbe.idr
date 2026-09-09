module DGamma.R198RepeatedTagStageProbe

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| A two-step parent with the SAME registration tag on both actual steps.
||| No schedule, synchronization or accepted-capital claim is contained here.
public export
r198RepeatedParent : Component R45Key R45Value Unit String
r198RepeatedParent = MkComponent r45Spec r45Spec [r45YieldingStep, r45YieldingStep]
