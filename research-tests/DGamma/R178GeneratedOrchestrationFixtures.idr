module DGamma.R178GeneratedOrchestrationFixtures

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Metatheory
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5RawClosingRankSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import Decidable.Equality
import Data.Nat

%default total
%unbound_implicits off

||| Exact state selected by R177 P2-4 after the common parent's LFinish.
||| State expressions retain the evaluator's actual table/accumulator structure.
public export
r178ParentDoneState : SystemState Nat R45Key R45Value Unit String
r178ParentDoneState = MkSystemState ()
  (replaceBinding @{r45NameEq} 0
    (setFiberRuntime r45ParentBegun
      (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec (ownedValues (fiberTable r45ParentBegun)))
      (Active (pushLocalUndo @{r45KeyEq} r45Spec id id) EmptyView))
    r45SourcePairFinalRegistry)
