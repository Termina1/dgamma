module DGamma.R172O17OpenParentRootReuseCandidate

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import DGamma.CP3
import DGamma.CP3Support
import DGamma.CP4Support
import DGamma.CP4SupportSolution
import DGamma.CP4SupportQuiescence
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Candidate only: an open parent yields a child that is removed and reissued as a root.
||| Checked trace facts below are not by themselves a refutation of the full O17 telescope.

public export
r172ReuseRootFresh : Fiber Nat R45Key R45Value Unit String
r172ReuseRootFresh = freshFiber r45Child Root

public export
r172ReuseAfterRoot : SystemState Nat R45Key R45Value Unit String
r172ReuseAfterRoot = MkSystemState () (insertBinding @{r45NameEq} 1 r172ReuseRootFresh (registry r45AfterBegin) Refl)

