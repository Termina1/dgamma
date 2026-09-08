module DGamma.L2R1RootHoist

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5L2R1ChildRelocation
import DGamma.CP5L2R1RootExchange
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import Decidable.Equality

%default total
%unbound_implicits off

||| Candidate admissible-root states (trace/square NOT proved in L2R1).
||| Root2 has empty provisions, unlike the blocked R174 collision.
||| No recursively nested evaluator builds these state indices.
public export
l2r1RootState : Nat -> SystemState Nat R45Key R45Value Unit String
l2r1RootState Z = r45AfterParent
l2r1RootState (S Z) = r45AfterBegin
l2r1RootState (S (S Z)) = MkSystemState ()
  (insertBinding @{r45NameEq} 2 (freshFiber r45Child Root) r45AfterBeginRegistry Refl)
l2r1RootState (S (S (S later))) = MkSystemState ()
  (insertBinding @{r45NameEq} 2 (freshFiber r45Child Root) r45AfterParentRegistry Refl)
