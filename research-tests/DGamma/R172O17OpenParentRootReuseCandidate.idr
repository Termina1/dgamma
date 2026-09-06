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

public export
r172ReuseRootRetired : Fiber Nat R45Key R45Value Unit String
r172ReuseRootRetired = retireFiber r172ReuseRootFresh

public export
r172ReuseAfterRetire : SystemState Nat R45Key R45Value Unit String
r172ReuseAfterRetire = MkSystemState () (replaceBinding @{r45NameEq} 1 r172ReuseRootRetired (registry r172ReuseAfterRoot))

||| Use the actual checked evaluator output; the later checked equation excludes the default branch.
public export
r172ReuseFinal : SystemState Nat R45Key R45Value Unit String
r172ReuseFinal = maybe r45AfterBegin snd (checkedApplyAction @{r45NameEq} @{r45KeyEq} (LAdvance 0) r172ReuseAfterRetire)

public export
0 r172ReuseRemoveChecked : checkedApplyAction @{r45NameEq} @{r45KeyEq} (ORemove 1) r45SourceFinal = Just (ORemoveTag, r45AfterBegin)
r172ReuseRemoveChecked = Refl

public export
0 r172ReuseRootChecked : checkedApplyAction @{r45NameEq} @{r45KeyEq} (OInsert 1 Root r45Child) r45AfterBegin = Just (OInsertTag, r172ReuseAfterRoot)
r172ReuseRootChecked = Refl

public export
0 r172ReuseRetireChecked : checkedApplyAction @{r45NameEq} @{r45KeyEq} (ORetire 1) r172ReuseAfterRoot = Just (ORetireTag, r172ReuseAfterRetire)
r172ReuseRetireChecked = Refl

public export
0 r172ReuseFinishChecked : checkedApplyAction @{r45NameEq} @{r45KeyEq} (LAdvance 0) r172ReuseAfterRetire = Just (LFinishTag, r172ReuseFinal)
r172ReuseFinishChecked = Refl

public export
r172ReuseRemove : Transition r45SourceFinal r45AfterBegin
r172ReuseRemove = Fired r45NameEq r45KeyEq (ORemove 1) ORemoveTag r172ReuseRemoveChecked

public export
r172ReuseRoot : Transition r45AfterBegin r172ReuseAfterRoot
r172ReuseRoot = Fired r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag r172ReuseRootChecked

public export
r172ReuseRetire : Transition r172ReuseAfterRoot r172ReuseAfterRetire
r172ReuseRetire = Fired r45NameEq r45KeyEq (ORetire 1) ORetireTag r172ReuseRetireChecked

