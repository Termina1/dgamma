module DGamma.R195RootOrdinalBoundaryPositive

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O20RootOrdinalBoundarySpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive

%default total
%unbound_implicits off

||| The actual checked singleton root insertion contains no generated child
||| occurrence. Only the existing checked edge is used; no canonical capital
||| or assumption about root replay is part of this fixture.
export
0 r195RootOnlyNoChildBirth :
  {child, parent : Nat} ->
  {component : Component R45Key R45Value Unit String} ->
  LocatedGeneratedRegistration child parent component
    (MoreTransitions r45ParentInsert NoTransitions) -> Void
r195RootOnlyNoChildBirth
  (MkLocatedGeneratedRegistration _ _ NoTransitions _ NoTransitions action Refl) =
    case action of Refl impossible
r195RootOnlyNoChildBirth
  (MkLocatedGeneratedRegistration _ _ NoTransitions step (MoreTransitions head tail) action decomposition) =
    case cong transitionCount decomposition of Refl impossible
r195RootOnlyNoChildBirth
  (MkLocatedGeneratedRegistration _ _ (MoreTransitions head NoTransitions) step tail action decomposition) =
    case cong transitionCount decomposition of Refl impossible
r195RootOnlyNoChildBirth
  (MkLocatedGeneratedRegistration _ _ (MoreTransitions head (MoreTransitions next rest)) step tail action decomposition) =
    case cong transitionCount decomposition of Refl impossible
