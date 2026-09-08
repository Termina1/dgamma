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
import Data.Nat
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

||| Nonzero whole-control integration: two ACTUAL checked Begin edges at the
||| authoritative explicit state2->3. Owner lookup is proved by insertion laws,
||| not by observing a nested proof-builder scalar. All foreign/absent names
||| remain quantified in the resulting full cut. This is not whole O20.
export
0 r190ActualBeginAllNameCut :
  O20AllNameCut Nat R45Key Unit String R45Value r45NameEq identityNameBijection
    (r182IndependentState 3) (r182IndependentState 3)
r190ActualBeginAllNameCut =
  o20SharedObservedBeginCut r45NameEq r45KeyEq identityNameBijection 0
    (r182IndependentState 2) (r182IndependentState 3) (r182IndependentState 2) (r182IndependentState 3)
    (MkBeginStep Refl) (MkBeginStep Refl) r45Child Root Root emptyOwned emptyOwned EmptyView EmptyView
    (trans (lookupInsertOther {key = Nat} {value = FiberAt Nat R45Key R45Value Unit String} @{r45NameEq}
      0 1 absurd (freshFiber r45Child Root) (registry (r182IndependentState 1)) Refl)
      (lookupInserted {key = Nat} {value = FiberAt Nat R45Key R45Value Unit String} @{r45NameEq}
        0 (freshFiber r45Child Root) emptyContext Refl))
    (trans (lookupInsertOther {key = Nat} {value = FiberAt Nat R45Key R45Value Unit String} @{r45NameEq}
      0 1 absurd (freshFiber r45Child Root) (registry (r182IndependentState 1)) Refl)
      (lookupInserted {key = Nat} {value = FiberAt Nat R45Key R45Value Unit String} @{r45NameEq}
        0 (freshFiber r45Child Root) emptyContext Refl))
    Refl Refl Refl Refl r190TwoRootAllNameCut Refl
