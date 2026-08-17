module DGamma.CP4SupportQuiescence

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4SupportSolution
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

0 emptyActiveFibersProvideAll :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  bindings (registry state) = [] ->
  ActiveFibersProvideAll nameEq keyEq state
emptyActiveFibersProvideAll nameEq keyEq state empty selected fiber found active =
  let absent = lookupFiberEmptyRegistry nameEq selected state empty
  in void (nothingIsNotJust (trans (sym absent) found))

||| One aligned checked action preserves actual Active-table totality. The
||| acting fiber is discharged by repaired Definition 69's boundary
||| certificate; every foreign fiber is unchanged by the local-update frame.
0 transitionPreservesActiveFibersProvideAll :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (equation : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  ActiveFibersProvideAll nameEq keyEq before ->
  TransitionComponentTotal nameEq keyEq
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag equation) ->
  ActiveFibersProvideAll nameEq keyEq afterState
transitionPreservesActiveFibersProvideAll nameEq keyEq action tag before
  afterState equation sourceTotal actorTotal selected fiber found active
  with (decEq @{nameEq} selected (actionOwner action))
  transitionPreservesActiveFibersProvideAll nameEq keyEq action tag before
    afterState equation sourceTotal actorTotal selected fiber found active |
    Yes same = actorTotal fiber
      (replace
        {p = \actor => lookupFiber @{nameEq} actor (registry afterState) =
          Just fiber}
        same found)
      active
  transitionPreservesActiveFibersProvideAll nameEq keyEq action tag before
    afterState equation sourceTotal actorTotal selected fiber found active |
    No distinct =
      let rawEquation = checkedActionProjects nameEq keyEq action before
            afterState tag equation
          update = applyActionLocalUpdate nameEq keyEq action before afterState
            tag rawEquation
          framed = systemLocalUpdateForeign nameEq selected (actionOwner action)
            distinct before afterState update
          sourceFound = trans (sym framed) found
      in sourceTotal selected fiber sourceFound active

||| Forward induction turns the repaired per-boundary Definition-69 evidence
||| into the endpoint property used by Lemma 70.
public export
0 traceActiveFibersProvideAll :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trace : Transitions first finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  TraceComponentsTotal nameEq keyEq trace ->
  ActiveFibersProvideAll nameEq keyEq first ->
  ActiveFibersProvideAll nameEq keyEq finalState
traceActiveFibersProvideAll nameEq keyEq NoTransitions AlignedEnd
  TraceComponentsTotalEnd sourceTotal = sourceTotal
traceActiveFibersProvideAll nameEq keyEq
  (MoreTransitions (Fired nameEq keyEq action tag equation) rest)
  (AlignedStep action tag equation rest alignedRest)
  (TraceComponentsTotalStep
    (Fired nameEq keyEq action tag equation) rest boundaryTotal tailTotal)
  sourceTotal =
    traceActiveFibersProvideAll nameEq keyEq rest alignedRest tailTotal
      (transitionPreservesActiveFibersProvideAll nameEq keyEq action tag _ _
        equation sourceTotal boundaryTotal)

0 andLeftTrue : (left, right : Bool) -> left && right = True -> left = True
andLeftTrue False right valid = case valid of Refl impossible
andLeftTrue True right valid = Refl

0 andRightTrue : (left, right : Bool) -> left && right = True -> right = True
andRightTrue False False valid = case valid of Refl impossible
andRightTrue True False valid = case valid of Refl impossible
andRightTrue left True valid = Refl

0 falseCannotEqualTrue : False = True -> Void
falseCannotEqualTrue Refl impossible

0 allElemTrue :
  (predicate : a -> Bool) -> (values : List a) ->
  allList predicate values = True ->
  (selected : a) -> Elem selected values -> predicate selected = True
allElemTrue predicate (selected :: rest) valid selected Here =
  andLeftTrue _ _ valid
allElemTrue predicate (current :: rest) valid selected (There later) =
  allElemTrue predicate rest (andRightTrue _ _ valid) selected later

public export
actorFiberTotalAt : DecEq name => DecEq key => name ->
  SystemState name key value world error -> Bool
actorFiberTotalAt selected state =
  case lookupFiber selected (registry state) of
    Nothing => True
    Just fiber => fiberTotalOnProvision fiber

0 fiberTotalCheckSound :
  (keyEq : DecEq key) -> (fiber : Fiber name key value world error) ->
  fiberTotalOnProvision @{keyEq} fiber = True ->
  isActive (fiberLifecycle fiber) = True ->
  ActiveFiberProvidesAll keyEq fiber
fiberTotalCheckSound keyEq fiber checked active with (fiber)
  fiberTotalCheckSound keyEq fiber checked active |
    (MkFiber component parent retired table (Inactive outcome)) =
      void (falseCannotEqualTrue active)
  fiberTotalCheckSound keyEq fiber checked active |
    (MkFiber component parent retired table
      (Reloading remaining accumulator view)) =
        void (falseCannotEqualTrue active)
  fiberTotalCheckSound keyEq fiber checked active |
    (MkFiber component parent retired table (Active accumulator view)) =
      \k, provision => allElemTrue
        (\candidate => isJust (lookupBinding @{keyEq} candidate
          (ownedValues table)))
        (dependencies (componentProvisions component)) checked k provision
  fiberTotalCheckSound keyEq fiber checked active |
    (MkFiber component parent retired table
      (Unloading accumulator view outcome)) =
        void (falseCannotEqualTrue active)

0 transitionComponentTotalFromCheck :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (transition : Transition before afterState) ->
  actorFiberTotalAt @{nameEq} @{keyEq}
    (actionOwner (transitionAction transition)) afterState = True ->
  TransitionComponentTotal nameEq keyEq transition
transitionComponentTotalFromCheck nameEq keyEq transition checked fiber found
  active
  with (lookupFiber @{nameEq}
    (actionOwner (transitionAction transition)) (registry afterState))
    proof observed
  transitionComponentTotalFromCheck nameEq keyEq transition checked fiber found
    active | Nothing = case found of Refl impossible
  transitionComponentTotalFromCheck nameEq keyEq transition checked fiber found
    active | Just observedFiber =
      let 0 sameFiber : (observedFiber = fiber)
          sameFiber = justInjective found
          0 observedChecked :
            (fiberTotalOnProvision @{keyEq} observedFiber = True)
          observedChecked = checked
      in case sameFiber of
        Refl => fiberTotalCheckSound keyEq fiber observedChecked active

||| Executable proof-producing validator for repaired Definition 69. It checks
||| the actual table at every actor boundary and returns the indexed trace
||| witness rather than a detached Boolean assertion.
public export
0 checkTraceComponentsTotal :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trace : Transitions first finalState) ->
  Maybe (TraceComponentsTotal nameEq keyEq trace)
checkTraceComponentsTotal nameEq keyEq NoTransitions =
  Just TraceComponentsTotalEnd
checkTraceComponentsTotal nameEq keyEq
  (MoreTransitions {middle} transition rest)
  with (actorFiberTotalAt @{nameEq} @{keyEq}
    (actionOwner (transitionAction transition)) middle) proof boundary
  checkTraceComponentsTotal nameEq keyEq
    (MoreTransitions {middle} transition rest) | False = Nothing
  checkTraceComponentsTotal nameEq keyEq
    (MoreTransitions {middle} transition rest) | True =
      case checkTraceComponentsTotal nameEq keyEq rest of
        Nothing => Nothing
        Just tailTotal => Just (TraceComponentsTotalStep transition rest
          (transitionComponentTotalFromCheck nameEq keyEq transition boundary)
          tailTotal)

public export
record CertifiedActionTrace
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (start : SystemState name key value world error) where
  constructor MkCertifiedActionTrace
  certifiedFinal : SystemState name key value world error
  certifiedTrace : Transitions start certifiedFinal
  0 certifiedTotality :
    TraceComponentsTotal nameEq keyEq certifiedTrace

||| Execute a concrete schedule and construct repaired Definition-69 evidence
||| at the same time. Runtime state and trace remain available; the totality
||| certificate is erased.
public export
0 buildCertifiedActionTrace :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  List (Action name key value world error) ->
  (start : SystemState name key value world error) ->
  Maybe (CertifiedActionTrace name key world error value nameEq keyEq start)
buildCertifiedActionTrace {name} {key} {world} {error} {value}
  nameEq keyEq [] start =
  Just (MkCertifiedActionTrace start NoTransitions TraceComponentsTotalEnd)
buildCertifiedActionTrace {name} {key} {world} {error} {value}
  nameEq keyEq (action :: rest) start =
  case fire nameEq keyEq action start of
    Nothing => Nothing
    Just (MkTransitionResult afterState rule transition) =>
      case decEq
        (actorFiberTotalAt @{nameEq} @{keyEq}
          (actionOwner (transitionAction transition)) afterState)
        True of
        No notTotal => Nothing
        Yes boundary =>
          case buildCertifiedActionTrace nameEq keyEq rest afterState of
            Nothing => Nothing
            Just tail =>
              let 0 transitionTotal = transitionComponentTotalFromCheck
                    nameEq keyEq transition boundary
                  0 traceTotal = TraceComponentsTotalStep transition
                    (certifiedTrace tail) transitionTotal
                    (certifiedTotality tail)
              in Just (MkCertifiedActionTrace (certifiedFinal tail)
                (MoreTransitions transition (certifiedTrace tail)) traceTotal)

public export
0 reachedActiveFibersProvideAll :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (reached : ReachedFromEmpty name key world error value nameEq keyEq state) ->
  TraceComponentsTotal nameEq keyEq (reachTrace reached) ->
  ActiveFibersProvideAll nameEq keyEq state
reachedActiveFibersProvideAll nameEq keyEq reached totality =
  traceActiveFibersProvideAll nameEq keyEq (reachTrace reached)
    (reachAligned reached) totality
    (emptyActiveFibersProvideAll nameEq keyEq (reachInitial reached)
      (reachInitialEmpty reached))
