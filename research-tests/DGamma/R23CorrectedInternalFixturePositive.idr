module DGamma.R23CorrectedInternalFixturePositive

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4Support
import DGamma.CP4SupportSolution
import DGamma.CP4SupportQuiescence
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorEndpoint
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R18ExternalOrderProducerPositive
import DGamma.R22QuietnessDomainAuditPositive
import Decidable.Equality
import Data.List.Elem
import Data.Maybe

%default total
%unbound_implicits off

public export
data R23Key : Type where

public export
implementation DecEq R23Key where
  decEq key impossible

public export
R23Value : R23Key -> Type
R23Value key impossible

public export
r23Component : Component R23Key R23Value Unit Unit
r23Component = MkComponent emptySpec emptySpec []

public export
r23Protocol : RegistrationProtocol R23Key R23Value Unit Unit
r23Protocol = MkRegistrationProtocol
  (\tag => Nothing)
  (\component => Just Z)
  (\parent, child, step, tag, parentRank, childRank, occurs, parentRanked,
    childRanked, yields, catalog => case catalog of Refl impossible)
  (\provider, consumer, providerRank, consumerRank, providerRanked,
    consumerRanked, key, provided, required => case key of _ impossible)

public export
r23NameEq : DecEq Nat
r23NameEq = %search

public export
r23KeyEq : DecEq R23Key
r23KeyEq = %search

r23Fresh : Fiber Nat R23Key R23Value Unit Unit
r23Fresh = freshFiber r23Component Root

r23Begun : Fiber Nat R23Key R23Value Unit Unit
r23Begun = setFiberLifecycle r23Fresh (Reloading [] id EmptyView)

r23Active : Fiber Nat R23Key R23Value Unit Unit
r23Active = setFiberLifecycle r23Begun (Active id EmptyView)

r23InitialRegistry : Registry Nat R23Key R23Value Unit Unit
r23InitialRegistry = emptyContext

r23AfterInsert1Registry : Registry Nat R23Key R23Value Unit Unit
r23AfterInsert1Registry = insertBinding 1 r23Fresh r23InitialRegistry Refl

r23AfterInsert2Registry : Registry Nat R23Key R23Value Unit Unit
r23AfterInsert2Registry = insertBinding 2 r23Fresh r23AfterInsert1Registry Refl

r23AfterBegin1Registry : Registry Nat R23Key R23Value Unit Unit
r23AfterBegin1Registry = replaceBinding 1 r23Begun r23AfterInsert2Registry

r23AfterPairRegistry : Registry Nat R23Key R23Value Unit Unit
r23AfterPairRegistry = replaceBinding 2 r23Begun r23AfterBegin1Registry

r23AfterEarlyBegin2Registry : Registry Nat R23Key R23Value Unit Unit
r23AfterEarlyBegin2Registry = replaceBinding 2 r23Begun r23AfterInsert2Registry

r23AfterSwappedPairRegistry : Registry Nat R23Key R23Value Unit Unit
r23AfterSwappedPairRegistry = replaceBinding 1 r23Begun r23AfterEarlyBegin2Registry

r23AfterAdvance1Registry : Registry Nat R23Key R23Value Unit Unit
r23AfterAdvance1Registry = replaceBinding 1 r23Active r23AfterPairRegistry

r23FinalRegistry : Registry Nat R23Key R23Value Unit Unit
r23FinalRegistry = replaceBinding 2 r23Active r23AfterAdvance1Registry

r23Initial : SystemState Nat R23Key R23Value Unit Unit
r23Initial = MkSystemState () r23InitialRegistry

r23AfterInsert1 : SystemState Nat R23Key R23Value Unit Unit
r23AfterInsert1 = MkSystemState () r23AfterInsert1Registry

r23AfterInsert2 : SystemState Nat R23Key R23Value Unit Unit
r23AfterInsert2 = MkSystemState () r23AfterInsert2Registry

r23AfterBegin1 : SystemState Nat R23Key R23Value Unit Unit
r23AfterBegin1 = MkSystemState () r23AfterBegin1Registry

r23AfterPair : SystemState Nat R23Key R23Value Unit Unit
r23AfterPair = MkSystemState () r23AfterPairRegistry

r23AfterEarlyBegin2 : SystemState Nat R23Key R23Value Unit Unit
r23AfterEarlyBegin2 = MkSystemState () r23AfterEarlyBegin2Registry

r23AfterSwappedPair : SystemState Nat R23Key R23Value Unit Unit
r23AfterSwappedPair = MkSystemState () r23AfterSwappedPairRegistry

r23AfterAdvance1 : SystemState Nat R23Key R23Value Unit Unit
r23AfterAdvance1 = MkSystemState () r23AfterAdvance1Registry

r23Final : SystemState Nat R23Key R23Value Unit Unit
r23Final = MkSystemState () r23FinalRegistry

0 r23InitialWellFormed :
  registryWellFormed @{r23NameEq} @{r23KeyEq} r23Initial = True
r23InitialWellFormed = Refl

0 r23Insert1Raw :
  applyAction @{r23NameEq} @{r23KeyEq} (OInsert 1 Root r23Component)
    r23Initial = Just (OInsertTag, r23AfterInsert1)
r23Insert1Raw = Refl

0 r23AfterInsert1WellFormed :
  registryWellFormed @{r23NameEq} @{r23KeyEq} r23AfterInsert1 = True
r23AfterInsert1WellFormed = preservationTheoremProof r23NameEq r23KeyEq
  (OInsert 1 Root r23Component) r23Initial r23AfterInsert1 OInsertTag
  r23InitialWellFormed r23Insert1Raw

0 r23Insert1Checked :
  checkedApplyAction @{r23NameEq} @{r23KeyEq} (OInsert 1 Root r23Component)
    r23Initial = Just (OInsertTag, r23AfterInsert1)
r23Insert1Checked = rewrite r23Insert1Raw in Refl

0 r23Insert2Raw :
  applyAction @{r23NameEq} @{r23KeyEq} (OInsert 2 Root r23Component)
    r23AfterInsert1 = Just (OInsertTag, r23AfterInsert2)
r23Insert2Raw = Refl

0 r23AfterInsert2WellFormed :
  registryWellFormed @{r23NameEq} @{r23KeyEq} r23AfterInsert2 = True
r23AfterInsert2WellFormed = preservationTheoremProof r23NameEq r23KeyEq
  (OInsert 2 Root r23Component) r23AfterInsert1 r23AfterInsert2 OInsertTag
  r23AfterInsert1WellFormed r23Insert2Raw

0 r23Insert2Checked :
  checkedApplyAction @{r23NameEq} @{r23KeyEq} (OInsert 2 Root r23Component)
    r23AfterInsert1 = Just (OInsertTag, r23AfterInsert2)
r23Insert2Checked = rewrite r23Insert2Raw in Refl

0 r23Begin1Raw : applyAction @{r23NameEq} @{r23KeyEq} (LBegin 1)
  r23AfterInsert2 = Just (LBeginTag, r23AfterBegin1)
r23Begin1Raw = Refl

0 r23AfterBegin1WellFormed :
  registryWellFormed @{r23NameEq} @{r23KeyEq} r23AfterBegin1 = True
r23AfterBegin1WellFormed = preservationTheoremProof r23NameEq r23KeyEq
  (LBegin 1) r23AfterInsert2 r23AfterBegin1 LBeginTag
  r23AfterInsert2WellFormed r23Begin1Raw

0 r23Begin1Checked :
  checkedApplyAction @{r23NameEq} @{r23KeyEq} (LBegin 1) r23AfterInsert2 =
    Just (LBeginTag, r23AfterBegin1)
r23Begin1Checked = rewrite r23Begin1Raw in Refl

0 r23Begin2Raw : applyAction @{r23NameEq} @{r23KeyEq} (LBegin 2)
  r23AfterBegin1 = Just (LBeginTag, r23AfterPair)
r23Begin2Raw = Refl

0 r23AfterPairWellFormed :
  registryWellFormed @{r23NameEq} @{r23KeyEq} r23AfterPair = True
r23AfterPairWellFormed = preservationTheoremProof r23NameEq r23KeyEq
  (LBegin 2) r23AfterBegin1 r23AfterPair LBeginTag
  r23AfterBegin1WellFormed r23Begin2Raw

0 r23Begin2Checked :
  checkedApplyAction @{r23NameEq} @{r23KeyEq} (LBegin 2) r23AfterBegin1 =
    Just (LBeginTag, r23AfterPair)
r23Begin2Checked = rewrite r23Begin2Raw in Refl

0 r23EarlyBegin2Raw : applyAction @{r23NameEq} @{r23KeyEq} (LBegin 2)
  r23AfterInsert2 = Just (LBeginTag, r23AfterEarlyBegin2)
r23EarlyBegin2Raw = Refl

0 r23AfterEarlyBegin2WellFormed :
  registryWellFormed @{r23NameEq} @{r23KeyEq} r23AfterEarlyBegin2 = True
r23AfterEarlyBegin2WellFormed = preservationTheoremProof r23NameEq r23KeyEq
  (LBegin 2) r23AfterInsert2 r23AfterEarlyBegin2 LBeginTag
  r23AfterInsert2WellFormed r23EarlyBegin2Raw

0 r23EarlyBegin2Checked :
  checkedApplyAction @{r23NameEq} @{r23KeyEq} (LBegin 2) r23AfterInsert2 =
    Just (LBeginTag, r23AfterEarlyBegin2)
r23EarlyBegin2Checked = rewrite r23EarlyBegin2Raw in Refl

0 r23MovedBegin1Raw : applyAction @{r23NameEq} @{r23KeyEq} (LBegin 1)
  r23AfterEarlyBegin2 = Just (LBeginTag, r23AfterSwappedPair)
r23MovedBegin1Raw = Refl

0 r23AfterSwappedPairWellFormed :
  registryWellFormed @{r23NameEq} @{r23KeyEq} r23AfterSwappedPair = True
r23AfterSwappedPairWellFormed = preservationTheoremProof r23NameEq r23KeyEq
  (LBegin 1) r23AfterEarlyBegin2 r23AfterSwappedPair LBeginTag
  r23AfterEarlyBegin2WellFormed r23MovedBegin1Raw

0 r23MovedBegin1Checked :
  checkedApplyAction @{r23NameEq} @{r23KeyEq} (LBegin 1) r23AfterEarlyBegin2 =
    Just (LBeginTag, r23AfterSwappedPair)
r23MovedBegin1Checked = rewrite r23MovedBegin1Raw in Refl

0 r23PairEndpointsEqual : r23AfterSwappedPair = r23AfterPair
r23PairEndpointsEqual = Refl

0 r23Advance1Raw : applyAction @{r23NameEq} @{r23KeyEq} (LAdvance 1)
  r23AfterPair = Just (LFinishTag, r23AfterAdvance1)
r23Advance1Raw = Refl

0 r23AfterAdvance1WellFormed :
  registryWellFormed @{r23NameEq} @{r23KeyEq} r23AfterAdvance1 = True
r23AfterAdvance1WellFormed = preservationTheoremProof r23NameEq r23KeyEq
  (LAdvance 1) r23AfterPair r23AfterAdvance1 LFinishTag
  r23AfterPairWellFormed r23Advance1Raw

0 r23Advance1Checked :
  checkedApplyAction @{r23NameEq} @{r23KeyEq} (LAdvance 1) r23AfterPair =
    Just (LFinishTag, r23AfterAdvance1)
r23Advance1Checked = rewrite r23Advance1Raw in Refl

0 r23Advance2Raw : applyAction @{r23NameEq} @{r23KeyEq} (LAdvance 2)
  r23AfterAdvance1 = Just (LFinishTag, r23Final)
r23Advance2Raw = Refl

0 r23FinalWellFormed :
  registryWellFormed @{r23NameEq} @{r23KeyEq} r23Final = True
r23FinalWellFormed = preservationTheoremProof r23NameEq r23KeyEq
  (LAdvance 2) r23AfterAdvance1 r23Final LFinishTag
  r23AfterAdvance1WellFormed r23Advance2Raw

0 r23Advance2Checked :
  checkedApplyAction @{r23NameEq} @{r23KeyEq} (LAdvance 2) r23AfterAdvance1 =
    Just (LFinishTag, r23Final)
r23Advance2Checked = rewrite r23Advance2Raw in Refl

r23Insert1 : Transition r23Initial r23AfterInsert1
r23Insert1 = Fired r23NameEq r23KeyEq (OInsert 1 Root r23Component) OInsertTag
  r23Insert1Checked

r23Insert2 : Transition r23AfterInsert1 r23AfterInsert2
r23Insert2 = Fired r23NameEq r23KeyEq (OInsert 2 Root r23Component) OInsertTag
  r23Insert2Checked

r23Begin1 : Transition r23AfterInsert2 r23AfterBegin1
r23Begin1 = Fired r23NameEq r23KeyEq (LBegin 1) LBeginTag r23Begin1Checked

r23Begin2 : Transition r23AfterBegin1 r23AfterPair
r23Begin2 = Fired r23NameEq r23KeyEq (LBegin 2) LBeginTag r23Begin2Checked

r23EarlyBegin2 : Transition r23AfterInsert2 r23AfterEarlyBegin2
r23EarlyBegin2 = Fired r23NameEq r23KeyEq (LBegin 2) LBeginTag
  r23EarlyBegin2Checked

r23MovedBegin1 : Transition r23AfterEarlyBegin2 r23AfterSwappedPair
r23MovedBegin1 = Fired r23NameEq r23KeyEq (LBegin 1) LBeginTag
  r23MovedBegin1Checked

r23Advance1 : Transition r23AfterPair r23AfterAdvance1
r23Advance1 = Fired r23NameEq r23KeyEq (LAdvance 1) LFinishTag
  r23Advance1Checked

r23Advance2 : Transition r23AfterAdvance1 r23Final
r23Advance2 = Fired r23NameEq r23KeyEq (LAdvance 2) LFinishTag
  r23Advance2Checked

public export
r23SourceTrace : Transitions r23Initial r23Final
r23SourceTrace = MoreTransitions r23Insert1
  (MoreTransitions r23Insert2
    (MoreTransitions r23Begin1
      (MoreTransitions r23Begin2
        (MoreTransitions r23Advance1
          (MoreTransitions r23Advance2 NoTransitions)))))

public export
r23PairPrefix : Transitions r23Initial r23AfterInsert2
r23PairPrefix = MoreTransitions r23Insert1 (MoreTransitions r23Insert2 NoTransitions)

public export
r23Suffix : Transitions r23AfterPair r23Final
r23Suffix = MoreTransitions r23Advance1 (MoreTransitions r23Advance2 NoTransitions)

0 r23ExactDecomposition :
  appendTransitions r23PairPrefix
    (MoreTransitions r23Begin1 (MoreTransitions r23Begin2 r23Suffix)) =
  r23SourceTrace
r23ExactDecomposition = Refl

0 r23Begin1Node : O19BlockNode 1 r23Begin1
r23Begin1Node = O19LifecycleNode Refl

0 r23Begin2Node : O19BlockNode 2 r23Begin2
r23Begin2Node = O19LifecycleNode Refl
