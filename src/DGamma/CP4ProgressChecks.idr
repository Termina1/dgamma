module DGamma.CP4ProgressChecks

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CalculusChecks
import DGamma.Section3Example
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total

||| A component whose declared program is empty. The current CP3 Progress alias
||| does not require a Reloading continuation to be a suffix of this program.
public export
progressCounterComponent : Component ToyKey ToyValue ToyRuntime String
progressCounterComponent = MkComponent DGamma.CalculusChecks.toyEmptySpec
  DGamma.Section3Example.toySpecA []

progressSteps : List (StepEffect ToyKey ToyValue ToyRuntime String []
  DGamma.Section3Example.toySpecA)
progressSteps =
  [ DGamma.CalculusChecks.providerFinish
  , DGamma.CalculusChecks.providerFinish
  , DGamma.CalculusChecks.providerFinish
  , DGamma.CalculusChecks.providerFinish
  , DGamma.CalculusChecks.providerFinish
  ]

progressSteps1 : List (StepEffect ToyKey ToyValue ToyRuntime String []
  DGamma.Section3Example.toySpecA)
progressSteps1 =
  [ DGamma.CalculusChecks.providerFinish
  , DGamma.CalculusChecks.providerFinish
  , DGamma.CalculusChecks.providerFinish
  , DGamma.CalculusChecks.providerFinish
  ]

progressSteps2 : List (StepEffect ToyKey ToyValue ToyRuntime String []
  DGamma.Section3Example.toySpecA)
progressSteps2 =
  [ DGamma.CalculusChecks.providerFinish
  , DGamma.CalculusChecks.providerFinish
  , DGamma.CalculusChecks.providerFinish
  ]

progressSteps3 : List (StepEffect ToyKey ToyValue ToyRuntime String []
  DGamma.Section3Example.toySpecA)
progressSteps3 =
  [ DGamma.CalculusChecks.providerFinish
  , DGamma.CalculusChecks.providerFinish
  ]

progressSteps4 : List (StepEffect ToyKey ToyValue ToyRuntime String []
  DGamma.Section3Example.toySpecA)
progressSteps4 = [DGamma.CalculusChecks.providerFinish]

counterStateWithTable :
  (table : OwnedTable ToyKey ToyValue DGamma.Section3Example.toySpecA) ->
  Lifecycle ToyKey ToyValue ToyRuntime String Nat []
    DGamma.Section3Example.toySpecA ->
  SystemState Nat ToyKey ToyValue ToyRuntime String
counterStateWithTable table lifecycle = MkSystemState (MkToyRuntime False False)
  (MkCoeffectContext
    [Bind 0 (MkFiber progressCounterComponent Root False table lifecycle)]
    (UniqueCons notInEmpty UniqueNil))

counterState : Lifecycle ToyKey ToyValue ToyRuntime String Nat []
  DGamma.Section3Example.toySpecA ->
  SystemState Nat ToyKey ToyValue ToyRuntime String
counterState = counterStateWithTable emptyOwned

CounterAccumulator : Type
CounterAccumulator = LocalState ToyKey ToyValue ToyRuntime
    DGamma.Section3Example.toySpecA ->
  LocalState ToyKey ToyValue ToyRuntime DGamma.Section3Example.toySpecA

counterAccumulator0 : CounterAccumulator
counterAccumulator0 = id

counterAccumulator1 : CounterAccumulator
counterAccumulator1 = pushLocalUndo DGamma.Section3Example.toySpecA
  counterAccumulator0 id

counterAccumulator2 : CounterAccumulator
counterAccumulator2 = pushLocalUndo DGamma.Section3Example.toySpecA
  counterAccumulator1 id

counterAccumulator3 : CounterAccumulator
counterAccumulator3 = pushLocalUndo DGamma.Section3Example.toySpecA
  counterAccumulator2 id

counterAccumulator4 : CounterAccumulator
counterAccumulator4 = pushLocalUndo DGamma.Section3Example.toySpecA
  counterAccumulator3 id

counterAccumulator5 : CounterAccumulator
counterAccumulator5 = pushLocalUndo DGamma.Section3Example.toySpecA
  counterAccumulator4 id

counterTable0 : OwnedTable ToyKey ToyValue DGamma.Section3Example.toySpecA
counterTable0 = emptyOwned

counterTable1 : OwnedTable ToyKey ToyValue DGamma.Section3Example.toySpecA
counterTable1 = restrictOwnedPreservingOrder DGamma.Section3Example.toySpecA
  (ownedValues counterTable0)

counterTable2 : OwnedTable ToyKey ToyValue DGamma.Section3Example.toySpecA
counterTable2 = restrictOwnedPreservingOrder DGamma.Section3Example.toySpecA
  (ownedValues counterTable1)

counterTable3 : OwnedTable ToyKey ToyValue DGamma.Section3Example.toySpecA
counterTable3 = restrictOwnedPreservingOrder DGamma.Section3Example.toySpecA
  (ownedValues counterTable2)

counterTable4 : OwnedTable ToyKey ToyValue DGamma.Section3Example.toySpecA
counterTable4 = restrictOwnedPreservingOrder DGamma.Section3Example.toySpecA
  (ownedValues counterTable3)

counterTable5 : OwnedTable ToyKey ToyValue DGamma.Section3Example.toySpecA
counterTable5 = restrictOwnedPreservingOrder DGamma.Section3Example.toySpecA
  (ownedValues counterTable4)

public export
progressCounter0 : SystemState Nat ToyKey ToyValue ToyRuntime String
progressCounter0 = counterStateWithTable counterTable0
  (Reloading progressSteps counterAccumulator0 EmptyView)

progressCounter1 : SystemState Nat ToyKey ToyValue ToyRuntime String
progressCounter1 = counterStateWithTable counterTable1
  (Reloading progressSteps1 counterAccumulator1 EmptyView)

progressCounter2 : SystemState Nat ToyKey ToyValue ToyRuntime String
progressCounter2 = counterStateWithTable counterTable2
  (Reloading progressSteps2 counterAccumulator2 EmptyView)

progressCounter3 : SystemState Nat ToyKey ToyValue ToyRuntime String
progressCounter3 = counterStateWithTable counterTable3
  (Reloading progressSteps3 counterAccumulator3 EmptyView)

progressCounter4 : SystemState Nat ToyKey ToyValue ToyRuntime String
progressCounter4 = counterStateWithTable counterTable4
  (Reloading progressSteps4 counterAccumulator4 EmptyView)

public export
progressCounter5 : SystemState Nat ToyKey ToyValue ToyRuntime String
progressCounter5 = counterStateWithTable counterTable5
  (Active counterAccumulator5 EmptyView)

0 emptyViewBindingsValid :
  (fibers : Registry Nat ToyKey ToyValue ToyRuntime String) ->
  viewBindingsInvariant @{the (DecEq Nat) %search}
    @{the (DecEq ToyKey) %search} {value = ToyValue} {world = ToyRuntime}
    {error = String} [] EmptyView fibers = True
emptyViewBindingsValid fibers = Refl

0 counterReloadingWellFormed :
  (table : OwnedTable ToyKey ToyValue DGamma.Section3Example.toySpecA) ->
  (remaining : List (StepEffect ToyKey ToyValue ToyRuntime String []
    DGamma.Section3Example.toySpecA)) ->
  (accumulator : LocalState ToyKey ToyValue ToyRuntime
      DGamma.Section3Example.toySpecA ->
    LocalState ToyKey ToyValue ToyRuntime DGamma.Section3Example.toySpecA) ->
  registryWellFormed @{the (DecEq Nat) %search}
    @{the (DecEq ToyKey) %search}
    (counterStateWithTable table
      (Reloading remaining accumulator EmptyView)) = True
counterReloadingWellFormed table remaining accumulator =
  rewrite emptyViewBindingsValid
    (registry (counterStateWithTable table
      (Reloading remaining accumulator EmptyView))) in Refl

0 counterActiveWellFormed :
  (table : OwnedTable ToyKey ToyValue DGamma.Section3Example.toySpecA) ->
  (accumulator : LocalState ToyKey ToyValue ToyRuntime
      DGamma.Section3Example.toySpecA ->
    LocalState ToyKey ToyValue ToyRuntime DGamma.Section3Example.toySpecA) ->
  registryWellFormed @{the (DecEq Nat) %search}
    @{the (DecEq ToyKey) %search}
    (counterStateWithTable table (Active accumulator EmptyView)) = True
counterActiveWellFormed table accumulator =
  rewrite emptyViewBindingsValid
    (registry (counterStateWithTable table
      (Active accumulator EmptyView))) in Refl

0 progressCounter0WellFormed :
  registryWellFormed @{the (DecEq Nat) %search}
    @{the (DecEq ToyKey) %search}
    DGamma.CP4ProgressChecks.progressCounter0 = True
progressCounter0WellFormed = counterReloadingWellFormed counterTable0
  progressSteps counterAccumulator0

0 progressCounter1WellFormed :
  registryWellFormed @{the (DecEq Nat) %search}
    @{the (DecEq ToyKey) %search}
    DGamma.CP4ProgressChecks.progressCounter1 = True
progressCounter1WellFormed = counterReloadingWellFormed counterTable1
  progressSteps1 counterAccumulator1

0 progressCounter2WellFormed :
  registryWellFormed @{the (DecEq Nat) %search}
    @{the (DecEq ToyKey) %search}
    DGamma.CP4ProgressChecks.progressCounter2 = True
progressCounter2WellFormed = counterReloadingWellFormed counterTable2
  progressSteps2 counterAccumulator2

0 progressCounter3WellFormed :
  registryWellFormed @{the (DecEq Nat) %search}
    @{the (DecEq ToyKey) %search}
    DGamma.CP4ProgressChecks.progressCounter3 = True
progressCounter3WellFormed = counterReloadingWellFormed counterTable3
  progressSteps3 counterAccumulator3

0 progressCounter4WellFormed :
  registryWellFormed @{the (DecEq Nat) %search}
    @{the (DecEq ToyKey) %search}
    DGamma.CP4ProgressChecks.progressCounter4 = True
progressCounter4WellFormed = counterReloadingWellFormed counterTable4
  progressSteps4 counterAccumulator4

0 progressCounter5WellFormed :
  registryWellFormed @{the (DecEq Nat) %search}
    @{the (DecEq ToyKey) %search}
    DGamma.CP4ProgressChecks.progressCounter5 = True
progressCounter5WellFormed = counterActiveWellFormed counterTable5
  counterAccumulator5

0 progressCounterRaw0 :
  applyAction @{the (DecEq Nat) %search} @{the (DecEq ToyKey) %search}
    (LAdvance (the Nat 0)) DGamma.CP4ProgressChecks.progressCounter0 =
    Just (LIterTag, DGamma.CP4ProgressChecks.progressCounter1)
progressCounterRaw0 = Refl

0 checkedFromRaw :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  registryWellFormed @{nameEq} @{keyEq} afterState = True ->
  checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)
checkedFromRaw nameEq keyEq action before afterState tag raw valid =
  rewrite raw in rewrite valid in Refl

0 counterStep0 : Transition DGamma.CP4ProgressChecks.progressCounter0
  DGamma.CP4ProgressChecks.progressCounter1
counterStep0 = Fired %search %search (LAdvance (the Nat 0)) LIterTag
  (checkedFromRaw %search %search (LAdvance (the Nat 0)) progressCounter0
    progressCounter1 LIterTag progressCounterRaw0 progressCounter1WellFormed)

0 counterStep1 : Transition DGamma.CP4ProgressChecks.progressCounter1
  DGamma.CP4ProgressChecks.progressCounter2
counterStep1 = Fired %search %search (LAdvance (the Nat 0)) LIterTag
  (checkedFromRaw %search %search (LAdvance (the Nat 0)) progressCounter1
    progressCounter2 LIterTag Refl progressCounter2WellFormed)

0 counterStep2 : Transition DGamma.CP4ProgressChecks.progressCounter2
  DGamma.CP4ProgressChecks.progressCounter3
counterStep2 = Fired %search %search (LAdvance (the Nat 0)) LIterTag
  (checkedFromRaw %search %search (LAdvance (the Nat 0)) progressCounter2
    progressCounter3 LIterTag Refl progressCounter3WellFormed)

0 counterStep3 : Transition DGamma.CP4ProgressChecks.progressCounter3
  DGamma.CP4ProgressChecks.progressCounter4
counterStep3 = Fired %search %search (LAdvance (the Nat 0)) LIterTag
  (checkedFromRaw %search %search (LAdvance (the Nat 0)) progressCounter3
    progressCounter4 LIterTag Refl progressCounter4WellFormed)

0 counterStep4 : Transition DGamma.CP4ProgressChecks.progressCounter4
  DGamma.CP4ProgressChecks.progressCounter5
counterStep4 = Fired %search %search (LAdvance (the Nat 0)) LFinishTag
  (checkedFromRaw %search %search (LAdvance (the Nat 0)) progressCounter4
    progressCounter5 LFinishTag Refl progressCounter5WellFormed)

public export
0 progressCounterTrace : Transitions DGamma.CP4ProgressChecks.progressCounter0
  DGamma.CP4ProgressChecks.progressCounter5
progressCounterTrace = MoreTransitions counterStep0
  (MoreTransitions counterStep1
    (MoreTransitions counterStep2
      (MoreTransitions counterStep3
        (MoreTransitions counterStep4 NoTransitions))))

0 progressCounterLifecycleOnly :
  LifecycleOnly DGamma.CP4ProgressChecks.progressCounterTrace
progressCounterLifecycleOnly = LifecycleOnlyStep counterStep0 _ Refl
  (LifecycleOnlyStep counterStep1 _ Refl
    (LifecycleOnlyStep counterStep2 _ Refl
      (LifecycleOnlyStep counterStep3 _ Refl
        (LifecycleOnlyStep counterStep4 NoTransitions Refl LifecycleOnlyEnd))))

||| Non-vacuity witness for CP4 Finding #6: the existing checked five-step
||| regression trace uses one global pair of equality witnesses throughout.
public export
0 progressCounterAligned : AlignedTransitions Nat ToyKey ToyRuntime String
  ToyValue %search %search DGamma.CP4ProgressChecks.progressCounterTrace
progressCounterAligned =
  AlignedStep (LAdvance (the Nat 0)) LIterTag
    (checkedFromRaw %search %search (LAdvance (the Nat 0)) progressCounter0
      progressCounter1 LIterTag progressCounterRaw0 progressCounter1WellFormed)
    _ (AlignedStep (LAdvance (the Nat 0)) LIterTag
      (checkedFromRaw %search %search (LAdvance (the Nat 0)) progressCounter1
        progressCounter2 LIterTag Refl progressCounter2WellFormed)
      _ (AlignedStep (LAdvance (the Nat 0)) LIterTag
        (checkedFromRaw %search %search (LAdvance (the Nat 0)) progressCounter2
          progressCounter3 LIterTag Refl progressCounter3WellFormed)
        _ (AlignedStep (LAdvance (the Nat 0)) LIterTag
          (checkedFromRaw %search %search (LAdvance (the Nat 0)) progressCounter3
            progressCounter4 LIterTag Refl progressCounter4WellFormed)
          _ (AlignedStep (LAdvance (the Nat 0)) LFinishTag
            (checkedFromRaw %search %search (LAdvance (the Nat 0))
              progressCounter4 progressCounter5 LFinishTag Refl
              progressCounter5WellFormed)
            NoTransitions AlignedEnd))))

0 counterTargetProviders :
  (lifecycle : Lifecycle ToyKey ToyValue ToyRuntime String Nat []
    DGamma.Section3Example.toySpecA) ->
  targetProvidersAt @{the (DecEq Nat) %search}
    @{the (DecEq ToyKey) %search} (the Nat 0) (counterState lifecycle) =
      Just []
counterTargetProviders lifecycle = Refl

0 counterSameTarget :
  (left, right : Lifecycle ToyKey ToyValue ToyRuntime String Nat []
    DGamma.Section3Example.toySpecA) ->
  sameTarget @{the (DecEq Nat) %search}
    (targetProvidersAt @{the (DecEq Nat) %search}
      @{the (DecEq ToyKey) %search} (the Nat 0) (counterState left))
    (targetProvidersAt @{the (DecEq Nat) %search}
      @{the (DecEq ToyKey) %search} (the Nat 0) (counterState right)) = True
counterSameTarget left right =
  let 0 rightLift :
        (sameTarget @{the (DecEq Nat) %search} (Just [])
          (targetProvidersAt @{the (DecEq Nat) %search}
            @{the (DecEq ToyKey) %search} (the Nat 0)
            (counterState right)) = True)
      rightLift = replace
        {p = \observed => sameTarget @{the (DecEq Nat) %search}
          (Just []) observed = True}
        (sym (counterTargetProviders right)) Refl
  in replace
    {p = \observed => sameTarget @{the (DecEq Nat) %search} observed
      (targetProvidersAt @{the (DecEq Nat) %search}
        @{the (DecEq ToyKey) %search} (the Nat 0)
        (counterState right)) = True}
    (sym (counterTargetProviders left)) rightLift

0 progressCounterTurns :
  TargetTurnCount Nat ToyKey ToyRuntime String ToyValue %search %search 0
    DGamma.CP4ProgressChecks.progressCounterTrace Z
progressCounterTurns = TargetStayed counterStep0 _
  (counterSameTarget (Reloading progressSteps id EmptyView)
    (Reloading progressSteps1 (id . id) EmptyView))
  (TargetStayed counterStep1 _
    (counterSameTarget (Reloading progressSteps1 (id . id) EmptyView)
      (Reloading progressSteps2 ((id . id) . id) EmptyView))
    (TargetStayed counterStep2 _
      (counterSameTarget (Reloading progressSteps2 ((id . id) . id) EmptyView)
        (Reloading progressSteps3 (((id . id) . id) . id) EmptyView))
      (TargetStayed counterStep3 _
        (counterSameTarget
          (Reloading progressSteps3 (((id . id) . id) . id) EmptyView)
          (Reloading progressSteps4 ((((id . id) . id) . id) . id)
            EmptyView))
        (TargetStayed counterStep4 NoTransitions
          (counterSameTarget
            (Reloading progressSteps4 ((((id . id) . id) . id) . id)
              EmptyView)
            (Active (((((id . id) . id) . id) . id) . id) EmptyView))
          NoTargetTurns))))

0 elemEmptyAbsurd : Elem value [] -> Void
elemEmptyAbsurd Here impossible
elemEmptyAbsurd (There later) impossible

0 counterFoundHasNoDependencies :
  (selected : Nat) -> (fiber : Fiber Nat ToyKey ToyValue ToyRuntime String) ->
  lookupFiber @{the (DecEq Nat) %search} selected
    (registry DGamma.CP4ProgressChecks.progressCounter0) = Just fiber ->
  (wanted : ToyKey) ->
  Elem wanted (dependencies (componentDependencies (fiberComponent fiber))) ->
  Void
counterFoundHasNoDependencies selected fiber found wanted declared
  with (decEq selected (the Nat 0))
  counterFoundHasNoDependencies (the Nat 0) fiber found wanted declared |
    Yes Refl =
      let 0 same = justInjective found
      in case same of Refl => elemEmptyAbsurd declared
  counterFoundHasNoDependencies selected fiber found wanted declared |
    No distinct = case found of Refl impossible

0 progressCounterAcyclic : PrecedenceAcyclic (the (DecEq Nat) %search)
  DGamma.CP4ProgressChecks.progressCounter0
progressCounterAcyclic selected (PrecedenceOne
  (MkPrecedenceEdge edgeKey providerFiber consumerFiber providerFound
    consumerFound providerDeclares consumerDeclares)) =
      counterFoundHasNoDependencies selected consumerFiber consumerFound
        edgeKey consumerDeclares
progressCounterAcyclic selected (PrecedenceMore {middle}
  (MkPrecedenceEdge edgeKey providerFiber consumerFiber providerFound
    consumerFound providerDeclares consumerDeclares) rest) =
      counterFoundHasNoDependencies middle consumerFiber consumerFound
        edgeKey consumerDeclares

0 succNotLTEZero : LTE (S n) Z -> Void
succNotLTEZero LTEZero impossible
succNotLTEZero (LTESucc earlier) impossible

0 fiveNotLTEFour : LTE 5 4 -> Void
fiveNotLTEFour (LTESucc (LTESucc (LTESucc (LTESucc impossibleBound)))) =
  succNotLTEZero impossibleBound

||| The rejected pre-repair Theorem-66 shape, retained to pin the missed
||| arbitrary-initial-continuation countermodel.
public export
UnboundedProgressTheorem : Type
UnboundedProgressTheorem =
  (nameEq : DecEq Nat) -> (keyEq : DecEq ToyKey) -> (bound : Nat) ->
  (first, last : SystemState Nat ToyKey ToyValue ToyRuntime String) ->
  (trace : Transitions first last) -> LifecycleOnly trace ->
  registryWellFormed @{nameEq} @{keyEq} first = True ->
  PrecedenceAcyclic nameEq first -> programsBoundedBy bound first = True ->
  ProgressResult Nat ToyKey ToyRuntime String ToyValue nameEq keyEq bound trace

||| The rejected old alias is uninhabited: it admitted the five-step
||| continuation while promising a four-step bound.
public export
0 unboundedProgressAliasCounterexample : UnboundedProgressTheorem -> Void
unboundedProgressAliasCounterexample theorem =
  let result = theorem %search %search Z progressCounter0 progressCounter5
        progressCounterTrace progressCounterLifecycleOnly
        progressCounter0WellFormed
        progressCounterAcyclic Refl
      impossibleBound = perFiberBound result 0 Z progressCounterTurns
  in fiveNotLTEFour impossibleBound

||| The same concrete first state is rejected exactly at the additional premise
||| of the repaired public `progressTheorem` alias.
public export
0 progressAliasCounterexample :
  continuationsBoundedBy Z DGamma.CP4ProgressChecks.progressCounter0 = True ->
  Void
progressAliasCounterexample bounded = case bounded of Refl impossible

public export
0 progressCounterContinuationRejected :
  continuationsBoundedBy Z DGamma.CP4ProgressChecks.progressCounter0 = True ->
  Void
progressCounterContinuationRejected = progressAliasCounterexample

||| Non-vacuity of the repaired premise at a checked, nonempty trace endpoint:
||| after one of the five Reloading landings, four remain and K=4.
public export
0 repairedContinuationPremisePositive :
  (trace : Transitions DGamma.CP4ProgressChecks.progressCounter0
      DGamma.CP4ProgressChecks.progressCounter1 **
    continuationsBoundedBy 4 DGamma.CP4ProgressChecks.progressCounter1 = True)
repairedContinuationPremisePositive =
  (MoreTransitions counterStep0 NoTransitions ** Refl)

public export
progressAliasCounterexampleRuntimeCheck : Bool
progressAliasCounterexampleRuntimeCheck =
  length progressSteps == 5 &&
  length (componentProgram progressCounterComponent) == 0 &&
  targetProvidersAt @{the (DecEq Nat) %search}
    @{the (DecEq ToyKey) %search} 0 progressCounter0 == Just [] &&
  targetProvidersAt @{the (DecEq Nat) %search}
    @{the (DecEq ToyKey) %search} 0 progressCounter5 == Just [] &&
  registryWellFormed progressCounter0 &&
  programsBoundedBy Z progressCounter0 &&
  not (continuationsBoundedBy Z progressCounter0) &&
  continuationsBoundedBy 4 progressCounter1
