module DGamma.R45BareDiamondFalseDisciplineNegative

import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import Data.List.Elem

%default total
%unbound_implicits off

||| Expected failure paired with `r45TargetDisciplineImpossible`: the swapped
||| child insertion occurs while the parent is still Inactive.  The public bare
||| diamond therefore cannot manufacture the ParentRegistrationYield needed by
||| target RegistrationDiscipline.
0 bareDiamondCannotForgeTargetYield :
  ParentRegistrationYield r45Protocol r45NameEq 0 r45Child r45AfterParent
bareDiamondCannotForgeTargetYield =
  MkParentRegistrationYield r45ParentFresh Refl r45YieldingStep [] id EmptyView
    Refl Here 0 1 Refl Refl 0 Refl Refl
