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

||| Use the PREVIOUS CHECKED transition's target-validity theorem, not an
||| independently recomputed raw child insertion equation (R177 P2-2 wall).
public export
r178ParentFinish : Transition r45SourcePairFinal r178ParentDoneState
r178ParentFinish = Fired r45NameEq r45KeyEq (LAdvance 0) LFinishTag
  (DGamma.CP4ProgressNoDeadlock.checkedFromRaw r45NameEq r45KeyEq
    (LAdvance 0) r45SourcePairFinal r178ParentDoneState LFinishTag
    (checkedTransitionTargetValid r45ChildInsert) Refl)

public export
r178ChildBegunState : SystemState Nat R45Key R45Value Unit String
r178ChildBegunState = MkSystemState ()
  (replaceBinding @{r45NameEq} 1
    (setFiberLifecycle r45ChildFresh (Reloading [] id EmptyView))
    (registry r178ParentDoneState))

public export
r178ChildBegin : Transition r178ParentDoneState r178ChildBegunState
r178ChildBegin = Fired r45NameEq r45KeyEq (LBegin 1) LBeginTag
  (DGamma.CP4ProgressNoDeadlock.checkedFromRaw r45NameEq r45KeyEq
    (LBegin 1) r178ParentDoneState r178ChildBegunState LBeginTag
    (checkedTransitionTargetValid r178ParentFinish) Refl)

public export
r178LeftFinal : SystemState Nat R45Key R45Value Unit String
r178LeftFinal = MkSystemState ()
  (replaceBinding @{r45NameEq} 1
    (setFiberLifecycle r45ChildFresh (Active id EmptyView))
    (registry r178ParentDoneState))

public export
r178ChildFinish : Transition r178ChildBegunState r178LeftFinal
r178ChildFinish = Fired r45NameEq r45KeyEq (LAdvance 1) LFinishTag
  (DGamma.CP4ProgressNoDeadlock.checkedFromRaw r45NameEq r45KeyEq
    (LAdvance 1) r178ChildBegunState r178LeftFinal LFinishTag
    (checkedTransitionTargetValid r178ChildBegin) Refl)

public export
r178RightFinal : SystemState Nat R45Key R45Value Unit String
r178RightFinal = MkSystemState ()
  (replaceBinding @{r45NameEq} 1 r45ChildRetired (registry r178ParentDoneState))

public export
r178ChildRetire : Transition r178ParentDoneState r178RightFinal
r178ChildRetire = Fired r45NameEq r45KeyEq (ORetire 1) ORetireTag
  (DGamma.CP4ProgressNoDeadlock.checkedFromRaw r45NameEq r45KeyEq
    (ORetire 1) r178ParentDoneState r178RightFinal ORetireTag
    (checkedTransitionTargetValid r178ParentFinish) Refl)

public export
r178CommonTrace : Transitions r45Initial r178ParentDoneState
r178CommonTrace = MoreTransitions r45ParentInsert
  (MoreTransitions r45Begin (MoreTransitions r45ChildInsert
    (MoreTransitions r178ParentFinish NoTransitions)))

public export
r178LeftTrace : Transitions r45Initial r178LeftFinal
r178LeftTrace = appendTransitions r178CommonTrace
  (MoreTransitions r178ChildBegin (MoreTransitions r178ChildFinish NoTransitions))

public export
r178RightTrace : Transitions r45Initial r178RightFinal
r178RightTrace = appendTransitions r178CommonTrace
  (MoreTransitions r178ChildRetire NoTransitions)

||| The actual right retirement has source child lookup and the exact current
||| birth (name 1, insertion ordinal 2), authenticated through the four-step scan.
export
0 r178RightGeneratedRetirement :
  LocatedGeneratedOrchestration Nat R45Key Unit String R45Value r45NameEq r178RightTrace
r178RightGeneratedRetirement = MkLocatedGeneratedOrchestration 1 False
  (MkLocatedActionOccurrence r178ParentDoneState r178RightFinal r178CommonTrace
    r178ChildRetire NoTransitions Refl Refl)
  r45ChildFresh 0 Refl Refl 4
  [(0, MkRegistrationGeneration 0 0), (1, MkRegistrationGeneration 1 2)]
  (GenerationTraceScanStep r45ParentInsert
    (MoreTransitions r45Begin (MoreTransitions r45ChildInsert (MoreTransitions r178ParentFinish NoTransitions)))
    (GenerationTraceScanStep r45Begin
      (MoreTransitions r45ChildInsert (MoreTransitions r178ParentFinish NoTransitions))
      (GenerationTraceScanStep r45ChildInsert (MoreTransitions r178ParentFinish NoTransitions)
        (GenerationTraceScanStep r178ParentFinish NoTransitions GenerationTraceScanEnd))))
  (MkRegistrationGeneration 1 2) Refl

export
0 r178RightRetirementKind : (generatedRemoval r178RightGeneratedRetirement = False)
r178RightRetirementKind = Refl

||| Structural action observation only; no quiet/fixed-point observer unfolds.
export
0 r178LeftNoRetirementAt :
  (actor, ordinal : Nat) ->
  (rawClosingActionAt Nat R45Key Unit String R45Value ordinal r178LeftTrace = Just (ORetire actor)) -> Void
r178LeftNoRetirementAt actor Z observed = case observed of Refl impossible
r178LeftNoRetirementAt actor (S Z) observed = case observed of Refl impossible
r178LeftNoRetirementAt actor (S (S Z)) observed = case observed of Refl impossible
r178LeftNoRetirementAt actor (S (S (S Z))) observed = case observed of Refl impossible
r178LeftNoRetirementAt actor (S (S (S (S Z)))) observed = case observed of Refl impossible
r178LeftNoRetirementAt actor (S (S (S (S (S Z))))) observed = case observed of Refl impossible
r178LeftNoRetirementAt actor (S (S (S (S (S (S later)))))) observed = case observed of Refl impossible

export
0 r178LeftGeneratedRetirementImpossible :
  (occurrence : LocatedGeneratedOrchestration Nat R45Key Unit String R45Value r45NameEq r178LeftTrace) ->
  (generatedRemoval occurrence = False) -> Void
r178LeftGeneratedRetirementImpossible occurrence kind =
  r178LeftNoRetirementAt (generatedActor occurrence)
    (locatedActionOrdinal (generatedOccurrence occurrence))
    (replace {p = \removal => (rawClosingActionAt Nat R45Key Unit String R45Value
      (locatedActionOrdinal (generatedOccurrence occurrence)) r178LeftTrace =
      Just (generatedOrchestrationAction Nat R45Key Unit String R45Value removal (generatedActor occurrence)))}
      kind (rawClosingActionAtLocated Nat R45Key Unit String R45Value r178LeftTrace
        (generatedOrchestrationAction Nat R45Key Unit String R45Value
          (generatedRemoval occurrence) (generatedActor occurrence))
        (generatedOccurrence occurrence)))

||| NEGATIVE: the exact R177 P2-4 action pair fails A9 for EVERY bijection,
||| hence in particular for any accepted generation bijection. This does not
||| construct a frozen accepted correspondence or either canonical capital.
export
0 r178QuietPairRejectsGeneratedMatching :
  (renaming : RegistrationGenerationBijection Nat) ->
  Not (GeneratedOrchestrationMatched Nat R45Key Unit String R45Value r45NameEq
    r178LeftTrace r178RightTrace renaming)
r178QuietPairRejectsGeneratedMatching renaming matched =
  r178LeftGeneratedRetirementImpossible
    (generatedBackward matched r178RightGeneratedRetirement)
    (trans (generatedBackwardKind matched r178RightGeneratedRetirement) r178RightRetirementKind)
