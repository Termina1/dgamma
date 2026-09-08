module DGamma.R190O20AllNameSynchronizationPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O20AllNameSynchronizationSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R182O19RevisedSafetyPositive
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Genuine nonempty fixture: build all-name runtime agreement by TWO actual
||| root insertion successors from the real empty origin of the six-edge run.
||| Refl inputs are primitive freshness/empty-state facts, never scalar
||| observations of nested O19/O20 proof producers.
export
0 r190TwoRootAllNameCut :
  O20AllNameCut Nat R45Key Unit String R45Value r45NameEq identityNameBijection
    (r182IndependentState 2) (r182IndependentState 2)
r190TwoRootAllNameCut =
  o20AllNameInsert r45NameEq r45KeyEq identityNameBijection 1 r45Child Root Root RootsRelated
    () () (registry (r182IndependentState 1)) (registry (r182IndependentState 1)) Refl Refl
    (o20AllNameInsert r45NameEq r45KeyEq identityNameBijection 0 r45Child Root Root RootsRelated
      () () emptyContext emptyContext Refl Refl
      (o20AllNameEmptyOrigin r45NameEq identityNameBijection (r182IndependentState 0) Refl))
