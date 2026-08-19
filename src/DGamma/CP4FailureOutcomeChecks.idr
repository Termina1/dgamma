module DGamma.CP4FailureOutcomeChecks

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4IndependenceNonVacuity
import DGamma.CP4RestrictionChecks
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

public export
data FailureWorld = ColdWorld | HotWorld

public export
implementation DecEq FailureWorld where
  decEq ColdWorld ColdWorld = Yes Refl
  decEq ColdWorld HotWorld = No (\Refl impossible)
  decEq HotWorld ColdWorld = No (\Refl impossible)
  decEq HotWorld HotWorld = Yes Refl

public export
data DivergentError = ColdError | HotError

public export
implementation DecEq DivergentError where
  decEq ColdError ColdError = Yes Refl
  decEq ColdError HotError = No (\Refl impossible)
  decEq HotError ColdError = No (\Refl impossible)
  decEq HotError HotError = Yes Refl

public export
data FailureKey = FailureService

public export
implementation DecEq FailureKey where
  decEq FailureService FailureService = Yes Refl

public export
FailureValue : FailureKey -> Type
FailureValue FailureService = Unit

public export
failureNameEq : DecEq Nat
failureNameEq = %search

public export
failureKeyEq : DecEq FailureKey
failureKeyEq = %search

failureDependencies : CoeffectSpec FailureKey
failureDependencies = MkCoeffectSpec [] UniqueNil

failureProvisions : CoeffectSpec FailureKey
failureProvisions = MkCoeffectSpec [] UniqueNil

||| One callback whose observable failure changes when a foreign effect changes
||| the ambient state.  Its recovery witness is vacuous because it never yields
||| a successful effect/inverse pair.
public export
failureSensitiveStep : StepEffect FailureKey FailureValue FailureWorld
  DivergentError [] DGamma.CP4FailureOutcomeChecks.failureProvisions
failureSensitiveStep = MkStepEffect Nothing run witness
  where
  run : DepValues FailureKey FailureValue [] ->
    LocalState FailureKey FailureValue FailureWorld
      DGamma.CP4FailureOutcomeChecks.failureProvisions ->
    Either DivergentError
      (LocalState FailureKey FailureValue FailureWorld
         DGamma.CP4FailureOutcomeChecks.failureProvisions,
       LocalState FailureKey FailureValue FailureWorld
         DGamma.CP4FailureOutcomeChecks.failureProvisions ->
       LocalState FailureKey FailureValue FailureWorld
         DGamma.CP4FailureOutcomeChecks.failureProvisions)
  run NoDepValues (MkLocalState ColdWorld table) = Left ColdError
  run NoDepValues (MkLocalState HotWorld table) = Left HotError

  0 witness : {auto keyEq : DecEq FailureKey} ->
    (capability : DepValues FailureKey FailureValue []) ->
    (before, after : LocalState FailureKey FailureValue FailureWorld
      DGamma.CP4FailureOutcomeChecks.failureProvisions) ->
    (undo : LocalState FailureKey FailureValue FailureWorld
        DGamma.CP4FailureOutcomeChecks.failureProvisions ->
      LocalState FailureKey FailureValue FailureWorld
        DGamma.CP4FailureOutcomeChecks.failureProvisions) ->
    run capability before = Right (after, undo) ->
    normalizeLocal DGamma.CP4FailureOutcomeChecks.failureProvisions before =
      before ->
    undo (normalizeLocal DGamma.CP4FailureOutcomeChecks.failureProvisions
      after) = before
  witness NoDepValues (MkLocalState ColdWorld table) after undo ran canonical =
    case ran of Refl impossible
  witness NoDepValues (MkLocalState HotWorld table) after undo ran canonical =
    case ran of Refl impossible

public export
failureComponent : Component FailureKey FailureValue FailureWorld DivergentError
failureComponent = MkComponent failureDependencies failureProvisions
  [failureSensitiveStep]

failureFiber : Fiber Nat FailureKey FailureValue FailureWorld DivergentError
failureFiber = MkFiber failureComponent Root False emptyOwned
  (Reloading [failureSensitiveStep] (\local => local) EmptyView)

0 zeroFreshFailure : Not (Elem (the Nat 0) [])
zeroFreshFailure present impossible

failureRegistry : Registry Nat FailureKey FailureValue FailureWorld DivergentError
failureRegistry = MkCoeffectContext [Bind (the Nat 0) failureFiber]
  (UniqueCons zeroFreshFailure UniqueNil)

public export
coldFailureState : SystemState Nat FailureKey FailureValue FailureWorld
  DivergentError
coldFailureState = MkSystemState ColdWorld failureRegistry

public export
coldFailureAfter : SystemState Nat FailureKey FailureValue FailureWorld
  DivergentError
coldFailureAfter = MkSystemState ColdWorld
  (replaceBinding @{DGamma.CP4FailureOutcomeChecks.failureNameEq} 0
    (MkFiber failureComponent Root False emptyOwned
      (Unloading (\local => local) EmptyView (Just ColdError)))
    failureRegistry)

0 coldFailureRaw : applyAction
  @{DGamma.CP4FailureOutcomeChecks.failureNameEq}
  @{DGamma.CP4FailureOutcomeChecks.failureKeyEq} (LAdvance (the Nat 0))
  DGamma.CP4FailureOutcomeChecks.coldFailureState = Just (LRaiseTag,
    DGamma.CP4FailureOutcomeChecks.coldFailureAfter)
coldFailureRaw = Refl

0 coldFailureAfterWellFormed : registryWellFormed
  @{DGamma.CP4FailureOutcomeChecks.failureNameEq}
  @{DGamma.CP4FailureOutcomeChecks.failureKeyEq}
  DGamma.CP4FailureOutcomeChecks.coldFailureAfter = True
coldFailureAfterWellFormed = Refl

public export
0 coldFailureChecked : checkedApplyAction
  @{DGamma.CP4FailureOutcomeChecks.failureNameEq}
  @{DGamma.CP4FailureOutcomeChecks.failureKeyEq} (LAdvance (the Nat 0))
  DGamma.CP4FailureOutcomeChecks.coldFailureState = Just (LRaiseTag,
    DGamma.CP4FailureOutcomeChecks.coldFailureAfter)
coldFailureChecked = rewrite coldFailureRaw in Refl

public export
0 coldFailureTransition : Transition
  DGamma.CP4FailureOutcomeChecks.coldFailureState
  DGamma.CP4FailureOutcomeChecks.coldFailureAfter
coldFailureTransition = Fired DGamma.CP4FailureOutcomeChecks.failureNameEq
  DGamma.CP4FailureOutcomeChecks.failureKeyEq (LAdvance 0) LRaiseTag
  DGamma.CP4FailureOutcomeChecks.coldFailureChecked

public export
0 failureTrace : Transitions DGamma.CP4FailureOutcomeChecks.coldFailureState
  DGamma.CP4FailureOutcomeChecks.coldFailureAfter
failureTrace = MoreTransitions coldFailureTransition NoTransitions

public export
0 failureStage : IteratorStage Nat FailureKey FailureWorld DivergentError
  FailureValue 0 DGamma.CP4FailureOutcomeChecks.failureTrace
failureStage = StageFromAdvance DGamma.CP4FailureOutcomeChecks.failureNameEq
  DGamma.CP4FailureOutcomeChecks.failureKeyEq 0 LRaiseTag
  DGamma.CP4FailureOutcomeChecks.coldFailureChecked OccursHere
  failureFiber Refl [failureSensitiveStep] (\local => local) EmptyView Refl
  failureSensitiveStep [] SuffixHere

public export
coldFailureEffects : EffectState Nat FailureKey FailureValue FailureWorld
coldFailureEffects = projectEffectState
  @{DGamma.CP4FailureOutcomeChecks.failureNameEq}
  DGamma.CP4FailureOutcomeChecks.coldFailureState

public export
hotFailureEffects : EffectState Nat FailureKey FailureValue FailureWorld
hotFailureEffects = setEffectAmbient HotWorld coldFailureEffects

||| The rejected pre-Finding-13 premise collapses both distinct failures to
||| `Nothing`, so it certifies the divergent callback.
0 hotStageOutcome : iteratorStageOutcome
  DGamma.CP4FailureOutcomeChecks.failureStage
  DGamma.CP4FailureOutcomeChecks.hotFailureEffects =
  Just (IteratorRaised HotError)
hotStageOutcome = Refl

0 coldStageOutcome : iteratorStageOutcome
  DGamma.CP4FailureOutcomeChecks.failureStage
  DGamma.CP4FailureOutcomeChecks.coldFailureEffects =
  Just (IteratorRaised ColdError)
coldStageOutcome = Refl

0 raisedStageHasNoSuccessfulEffect :
  iteratorStageOutcome stage state = Just (IteratorRaised failure) ->
  iteratorStageEffect stage state = Nothing
raisedStageHasNoSuccessfulEffect equation = rewrite equation in Refl

0 hotStageEffect : iteratorStageEffect
  DGamma.CP4FailureOutcomeChecks.failureStage
  DGamma.CP4FailureOutcomeChecks.hotFailureEffects = Nothing
hotStageEffect = raisedStageHasNoSuccessfulEffect
  {stage = DGamma.CP4FailureOutcomeChecks.failureStage}
  {state = DGamma.CP4FailureOutcomeChecks.hotFailureEffects}
  {failure = HotError} hotStageOutcome

0 coldStageEffect : iteratorStageEffect
  DGamma.CP4FailureOutcomeChecks.failureStage
  DGamma.CP4FailureOutcomeChecks.coldFailureEffects = Nothing
coldStageEffect = raisedStageHasNoSuccessfulEffect
  {stage = DGamma.CP4FailureOutcomeChecks.failureStage}
  {state = DGamma.CP4FailureOutcomeChecks.coldFailureEffects}
  {failure = ColdError} coldStageOutcome

public export
0 oldFailurePremiseAccepted : IteratorYieldAgreement Nat FailureKey FailureValue
  FailureWorld DivergentError DGamma.CP4FailureOutcomeChecks.failureKeyEq
  (iteratorStageEffect DGamma.CP4FailureOutcomeChecks.failureStage
    DGamma.CP4FailureOutcomeChecks.hotFailureEffects)
  (iteratorStageEffect DGamma.CP4FailureOutcomeChecks.failureStage
    DGamma.CP4FailureOutcomeChecks.coldFailureEffects)
oldFailurePremiseAccepted = rewrite hotStageEffect in
  rewrite coldStageEffect in IteratorBothUndefined

0 hotNotColdError : Not (HotError = ColdError)
hotNotColdError Refl impossible

||| The repaired premise observes `HotError` versus `ColdError` and therefore
||| rejects exactly the schedule-sensitive behavior accepted above.
public export
0 repairedFailurePremiseRejected : Not (IteratorOutcomeAgreement Nat FailureKey
  FailureValue FailureWorld DivergentError
  DGamma.CP4FailureOutcomeChecks.failureKeyEq
  (iteratorStageOutcome DGamma.CP4FailureOutcomeChecks.failureStage
    DGamma.CP4FailureOutcomeChecks.hotFailureEffects)
  (iteratorStageOutcome DGamma.CP4FailureOutcomeChecks.failureStage
    DGamma.CP4FailureOutcomeChecks.coldFailureEffects))
repairedFailurePremiseRejected agreement =
  let atHot : IteratorOutcomeAgreement Nat FailureKey FailureValue FailureWorld
        DivergentError DGamma.CP4FailureOutcomeChecks.failureKeyEq
        (Just (IteratorRaised HotError))
        (iteratorStageOutcome DGamma.CP4FailureOutcomeChecks.failureStage
          DGamma.CP4FailureOutcomeChecks.coldFailureEffects)
      atHot = replace
        {p = \observed => IteratorOutcomeAgreement Nat FailureKey FailureValue
          FailureWorld DivergentError
          DGamma.CP4FailureOutcomeChecks.failureKeyEq observed
          (iteratorStageOutcome DGamma.CP4FailureOutcomeChecks.failureStage
            DGamma.CP4FailureOutcomeChecks.coldFailureEffects)}
        hotStageOutcome agreement
      concrete : IteratorOutcomeAgreement Nat FailureKey FailureValue
        FailureWorld DivergentError
        DGamma.CP4FailureOutcomeChecks.failureKeyEq
        (Just (IteratorRaised HotError)) (Just (IteratorRaised ColdError))
      concrete = replace
        {p = \observed => IteratorOutcomeAgreement Nat FailureKey FailureValue
          FailureWorld DivergentError
          DGamma.CP4FailureOutcomeChecks.failureKeyEq
          (Just (IteratorRaised HotError)) observed}
        coldStageOutcome atHot
  in case concrete of
    IteratorFailuresAgree same => hotNotColdError same

public export
hotFailureState : SystemState Nat FailureKey FailureValue FailureWorld
  DivergentError
hotFailureState = MkSystemState HotWorld failureRegistry

public export
hotFailureAfter : SystemState Nat FailureKey FailureValue FailureWorld
  DivergentError
hotFailureAfter = MkSystemState HotWorld
  (replaceBinding @{DGamma.CP4FailureOutcomeChecks.failureNameEq} 0
    (MkFiber failureComponent Root False emptyOwned
      (Unloading (\local => local) EmptyView (Just HotError)))
    failureRegistry)

0 hotFailureRaw : applyAction
  @{DGamma.CP4FailureOutcomeChecks.failureNameEq}
  @{DGamma.CP4FailureOutcomeChecks.failureKeyEq} (LAdvance (the Nat 0))
  DGamma.CP4FailureOutcomeChecks.hotFailureState = Just (LRaiseTag,
    DGamma.CP4FailureOutcomeChecks.hotFailureAfter)
hotFailureRaw = Refl

0 hotFailureAfterWellFormed : registryWellFormed
  @{DGamma.CP4FailureOutcomeChecks.failureNameEq}
  @{DGamma.CP4FailureOutcomeChecks.failureKeyEq}
  DGamma.CP4FailureOutcomeChecks.hotFailureAfter = True
hotFailureAfterWellFormed = Refl

public export
0 hotFailureChecked : checkedApplyAction
  @{DGamma.CP4FailureOutcomeChecks.failureNameEq}
  @{DGamma.CP4FailureOutcomeChecks.failureKeyEq} (LAdvance (the Nat 0))
  DGamma.CP4FailureOutcomeChecks.hotFailureState = Just (LRaiseTag,
    DGamma.CP4FailureOutcomeChecks.hotFailureAfter)
hotFailureChecked = rewrite hotFailureRaw in Refl

0 justErrorInjective : Just left = Just right -> left = right
justErrorInjective Refl = Refl

0 divergentFailureLifecycles : Not (LifecycleControlRelated
  (Unloading {key = FailureKey} {value = FailureValue} {world = FailureWorld}
    {error = DivergentError} {name = Nat} {deps = []}
    {provision = DGamma.CP4FailureOutcomeChecks.failureProvisions}
    (\local => local) EmptyView (Just ColdError))
  (Unloading (\local => local) EmptyView (Just HotError)))
divergentFailureLifecycles
  (UnloadingControls accumulatorsSame viewsSame outcomesSame) =
    hotNotColdError (sym (justErrorInjective outcomesSame))

||| The two accepted raw L-Raise endpoints disagree on the exact outcome field,
||| so Equation-53 control equivalence cannot relate them.
public export
0 divergentFailuresBreakControl : Not (ControlEquivalent Nat FailureKey
  FailureWorld DivergentError FailureValue
  DGamma.CP4FailureOutcomeChecks.failureNameEq
  DGamma.CP4FailureOutcomeChecks.coldFailureAfter
  DGamma.CP4FailureOutcomeChecks.hotFailureAfter)
divergentFailuresBreakControl (MkControlEquivalent pointwise) =
  case pointwise 0 of
    SomeControlFibers
      (FibersControlRelated _ _ _ _ _ _ _ _ _ _ lifecycleSame) =>
        divergentFailureLifecycles lifecycleSame

||| The repaired singleton witness remains constructive even when its sole
||| checked stage genuinely fails: foreign transformations are identity and the
||| exact failure outcome is therefore reflexive.
public export
0 agreeingFailureTraceIndependent : TraceIndependent Nat FailureKey FailureWorld
  DivergentError FailureValue DGamma.CP4FailureOutcomeChecks.failureKeyEq
  DGamma.CP4FailureOutcomeChecks.failureTrace
agreeingFailureTraceIndependent =
  DGamma.CP4IndependenceNonVacuity.singletonTraceIndependent
    DGamma.CP4FailureOutcomeChecks.failureNameEq
    DGamma.CP4FailureOutcomeChecks.failureKeyEq
    DGamma.CP4FailureOutcomeChecks.coldFailureTransition
