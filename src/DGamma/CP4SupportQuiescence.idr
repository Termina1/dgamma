module DGamma.CP4SupportQuiescence

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

0 emptyActiveFibersProvideAll :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  bindings (registry state) = [] ->
  ActiveFibersProvideAll {name = name} {key = key} {value = value} {world = world} {error = error} nameEq keyEq state
emptyActiveFibersProvideAll {name = name} {key = key} {value = value} {world = world} {error = error} nameEq keyEq state empty selected fiber found active =
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

andLeftTrue : (left, right : Bool) -> left && right = True -> left = True
andLeftTrue False right valid = case valid of Refl impossible
andLeftTrue True right valid = Refl

andRightTrue : (left, right : Bool) -> left && right = True -> right = True
andRightTrue False False valid = case valid of Refl impossible
andRightTrue True False valid = case valid of Refl impossible
andRightTrue left True valid = Refl

falseCannotEqualTrue : False = True -> Void
falseCannotEqualTrue Refl impossible

andBothTrue : (left, right : Bool) -> left = True -> right = True ->
  left && right = True
andBothTrue False right leftTrue rightTrue =
  case leftTrue of Refl impossible
andBothTrue True right leftTrue rightTrue = rightTrue

andThirdTrue : (first, second, third : Bool) ->
  first && (second && third) = True -> third = True
andThirdTrue first second third valid =
  andRightTrue second third (andRightTrue first (second && third) valid)

andFirstLeftAssociated : (first, second, third : Bool) ->
  (first && second) && third = True -> first = True
andFirstLeftAssociated first second third valid =
  andLeftTrue first second (andLeftTrue (first && second) third valid)

orRightTrue : (left : Bool) -> right = True -> left || right = True
orRightTrue False rightTrue = rightTrue
orRightTrue True rightTrue = Refl

allElemTrue :
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

fiberTotalCheckSound :
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
                  traceTotal = TraceComponentsTotalStep transition
                    (certifiedTrace tail) transitionTotal
                    (certifiedTotality tail)
              in Just (MkCertifiedActionTrace (certifiedFinal tail)
                (MoreTransitions transition (certifiedTrace tail)) traceTotal)

0 allRecursiveLookup :
  (nameEq : DecEq name) ->
  (predicate : Binding name (FiberAt name key value world error) -> Bool) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  allRecursive predicate entries = True ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupEntries @{nameEq} selected entries = Just fiber ->
  predicate (Bind selected fiber) = True
allRecursiveLookup nameEq predicate [] valid selected fiber found =
  case found of Refl impossible
allRecursiveLookup nameEq predicate (Bind current observed :: rest) valid
  selected fiber found with (decEq @{nameEq} selected current)
  allRecursiveLookup nameEq predicate (Bind selected observed :: rest) valid
    selected fiber found | Yes Refl =
      let sameFiber = justInjective found
      in case sameFiber of Refl => andLeftTrue _ _ valid
  allRecursiveLookup nameEq predicate (Bind current observed :: rest) valid
    selected fiber found | No distinct =
      allRecursiveLookup nameEq predicate rest (andRightTrue _ _ valid)
        selected fiber found

0 allListLookup :
  (nameEq : DecEq name) ->
  (predicate : Binding name (FiberAt name key value world error) -> Bool) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  allList predicate entries = True ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupEntries @{nameEq} selected entries = Just fiber ->
  predicate (Bind selected fiber) = True
allListLookup nameEq predicate [] valid selected fiber found =
  case found of Refl impossible
allListLookup nameEq predicate (Bind current observed :: rest) valid selected
  fiber found with (decEq @{nameEq} selected current)
  allListLookup nameEq predicate (Bind selected observed :: rest) valid selected
    fiber found | Yes Refl =
      let sameFiber = justInjective found
      in case sameFiber of Refl => andLeftTrue _ _ valid
  allListLookup nameEq predicate (Bind current observed :: rest) valid selected
    fiber found | No distinct =
      allListLookup nameEq predicate rest (andRightTrue _ _ valid) selected
        fiber found

public export
0 quietFiberFromState :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  quiet @{nameEq} @{keyEq} state = True ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry state) = Just fiber ->
  quietFiber @{nameEq} @{keyEq} fiber (registry state) = True
quietFiberFromState nameEq keyEq
  state@(MkSystemState ambient (MkCoeffectContext entries unique)) quietState
  selected fiber found =
    allRecursiveLookup nameEq
      (quietEntryFor @{nameEq} @{keyEq} (registry state))
      entries quietState selected fiber found

public export
0 noFailureFromState :
  (nameEq : DecEq name) ->
  (state : SystemState name key value world error) ->
  noFailedFibers state = True ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry state) = Just fiber ->
  (case fiberLifecycle fiber of
    Inactive (Just errorValue) => False
    _ => True) = True
noFailureFromState nameEq
  state@(MkSystemState ambient (MkCoeffectContext entries unique)) noFailures
  selected fiber found =
    allListLookup nameEq notFailedEntry entries noFailures selected fiber found

listMemberTrueElemQ : DecEq a => (selected : a) -> (values : List a) ->
  listMember selected values = True -> Elem selected values
listMemberTrueElemQ selected [] present = case present of Refl impossible
listMemberTrueElemQ selected (current :: rest) present
  with (decEq selected current)
  listMemberTrueElemQ current (current :: rest) present | Yes Refl = Here
  listMemberTrueElemQ selected (current :: rest) present | No distinct =
    There (listMemberTrueElemQ selected rest present)

elemListMemberTrueQ : DecEq a => (selected : a) -> (values : List a) ->
  Elem selected values -> listMember selected values = True
elemListMemberTrueQ selected (selected :: rest) Here
  with (decEq selected selected)
  elemListMemberTrueQ selected (selected :: rest) Here | Yes Refl = Refl
  elemListMemberTrueQ selected (selected :: rest) Here | No contra =
    void (contra Refl)
elemListMemberTrueQ selected (current :: rest) (There later)
  with (decEq selected current)
  elemListMemberTrueQ current (current :: rest) (There later) | Yes Refl = Refl
  elemListMemberTrueQ selected (current :: rest) (There later) | No distinct =
    elemListMemberTrueQ selected rest later

lookupJustElemQ :
  (keyEq : DecEq key) -> (selected : key) ->
  (entries : List (Binding key value)) -> (found : value selected) ->
  lookupEntries @{keyEq} selected entries = Just found ->
  Elem selected (bindingKeys entries)
lookupJustElemQ keyEq selected [] found present = case present of Refl impossible
lookupJustElemQ keyEq selected (Bind current observed :: rest) found present
  with (decEq @{keyEq} selected current)
  lookupJustElemQ keyEq current (Bind current observed :: rest) found present |
    Yes Refl = Here
  lookupJustElemQ keyEq selected (Bind current observed :: rest) found present |
    No distinct = There (lookupJustElemQ keyEq selected rest found present)

bindingKeyElemQ :
  (entry : Binding key value) ->
  (entries : List (Binding key value)) ->
  Elem entry entries -> Elem (bindingKey entry) (bindingKeys entries)
bindingKeyElemQ entry (entry :: rest) Here = Here
bindingKeyElemQ entry (other :: rest) (There later) =
  There (bindingKeyElemQ entry rest later)

0 lookupIsJustElemQ :
  (keyEq : DecEq key) -> (selected : key) ->
  (entries : List (Binding key value)) ->
  isJust (lookupEntries @{keyEq} selected entries) = True ->
  Elem selected (bindingKeys entries)
lookupIsJustElemQ keyEq selected entries present
  with (lookupEntries @{keyEq} selected entries) proof found
  lookupIsJustElemQ keyEq selected entries present | Nothing =
    case present of Refl impossible
  lookupIsJustElemQ keyEq selected entries present | Just observed =
    lookupJustElemQ keyEq selected entries observed found

0 lookupIsJustBindingElemQ :
  (keyEq : DecEq key) -> (selected : key) ->
  (context : CoeffectContext key value) ->
  isJust (lookupBinding @{keyEq} selected context) = True ->
  Elem selected (bindingKeys (bindings context))
lookupIsJustBindingElemQ keyEq selected
  (MkCoeffectContext entries unique) present =
    lookupIsJustElemQ keyEq selected entries present

0 entryLookupFromElemQ :
  (nameEq : DecEq name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  UniqueKeys (bindingKeys entries) ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  Elem (Bind selected fiber) entries ->
  lookupEntries @{nameEq} selected entries = Just fiber
entryLookupFromElemQ nameEq [] UniqueNil selected fiber present impossible
entryLookupFromElemQ nameEq (Bind current observed :: rest)
  (UniqueCons headFresh tailUnique) selected fiber present
  with (decEq @{nameEq} selected current)
  entryLookupFromElemQ nameEq (Bind selected observed :: rest)
    (UniqueCons headFresh tailUnique) selected fiber present | Yes Refl =
      let 0 sameFiber : (observed = fiber)
          sameFiber = case present of
            Here => Refl
            There later =>
              void (headFresh
                (bindingKeyElemQ (Bind selected fiber) rest later))
      in case sameFiber of Refl => Refl
  entryLookupFromElemQ nameEq (Bind current observed :: rest)
    (UniqueCons headFresh tailUnique) selected fiber present | No distinct =
      case present of
        Here => void (distinct Refl)
        There later => entryLookupFromElemQ nameEq rest tailUnique selected
          fiber later

public export
activePredicate :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  SystemState name key value world error -> name -> Bool
activePredicate name key world error value nameEq state selected =
  supportedActiveAt @{nameEq} {key = key} {value = value} {world = world}
    {error = error} selected state

public export
0 activePredicateAtFoundQ :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  (state : SystemState name key value world error) ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry state) = Just fiber ->
  activePredicate name key world error value nameEq state selected =
    isActive (fiberLifecycle fiber)
activePredicateAtFoundQ nameEq state selected fiber found =
  rewrite found in Refl

activeProviderClauseIn :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (state : SystemState name key value world error) ->
  List (Binding name (FiberAt name key value world error)) -> Bool
activeProviderClauseIn name key world error value nameEq keyEq wanted state
  entries = providerFromPredicate @{nameEq} @{keyEq} {value = value}
    {world = world} {error = error} wanted
    (activePredicate name key world error value nameEq state) entries

public export
activeProviderClauses :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) -> List key -> Bool
activeProviderClauses name key world error value nameEq keyEq state deps =
  allList (\wanted => activeProviderClauseIn name key world error value nameEq
    keyEq wanted state (registryFibers (registry state))) deps

public export
providerClausesFor :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (predicate : name -> Bool) ->
  List (Binding name (FiberAt name key value world error)) -> List key -> Bool
providerClausesFor name key world error value nameEq keyEq predicate entries
  deps = allList (\wanted => providerFromPredicate @{nameEq} @{keyEq}
    {value = value} {world = world} {error = error} wanted predicate entries) deps

public export
0 activeProviderClausesExplicitQ :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (unique : UniqueKeys (bindingKeys entries)) -> (deps : List key) ->
  activeProviderClauses name key world error value nameEq keyEq
    (MkSystemState ambient (MkCoeffectContext entries unique)) deps =
  providerClausesFor name key world error value nameEq keyEq
    (activePredicate name key world error value nameEq
      (MkSystemState ambient (MkCoeffectContext entries unique))) entries deps
activeProviderClausesExplicitQ nameEq keyEq ambient entries unique deps = Refl

0 providerInGivesActiveDeclaration :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) ->
  (full : List (Binding name (FiberAt name key value world error))) ->
  (unique : UniqueKeys (bindingKeys full)) ->
  (scan : List (Binding name (FiberAt name key value world error))) ->
  ((entry : Binding name (FiberAt name key value world error)) ->
    Elem entry scan -> Elem entry full) ->
  (wanted : key) -> (provider : name) ->
  providerIn @{nameEq} @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error} wanted scan = Just provider ->
  activeProviderClauseIn name key world error value nameEq keyEq wanted
    (MkSystemState ambient (MkCoeffectContext full unique)) scan = True
providerInGivesActiveDeclaration nameEq keyEq ambient full unique [] subset
  wanted provider found = case found of Refl impossible
providerInGivesActiveDeclaration nameEq keyEq ambient full unique
  (Bind current fiber :: rest) subset wanted provider found
  with (isActive (fiberLifecycle fiber) &&
    memberKey @{keyEq} wanted (ownedValues (fiberTable fiber))) proof usable
  providerInGivesActiveDeclaration nameEq keyEq ambient full unique
    (Bind current fiber :: rest) subset wanted provider found | True =
      let 0 active : (isActive (fiberLifecycle fiber) = True)
          active = andLeftTrue _ _ usable
          0 keyPresent :
            (memberKey @{keyEq} wanted
              (ownedValues (fiberTable fiber)) = True)
          keyPresent = andRightTrue _ _ usable
          0 declared : Elem wanted
            (dependencies (componentProvisions (fiberComponent fiber)))
          declared = ownedSound (fiberTable fiber) wanted
            (lookupIsJustBindingElemQ keyEq wanted
              (ownedValues (fiberTable fiber)) keyPresent)
          0 globalFound :
            (lookupEntries @{nameEq} current full = Just fiber)
          globalFound = entryLookupFromElemQ nameEq full unique current fiber
            (subset (Bind current fiber) Here)
          0 activeGlobal :
            (supportedActiveAt @{nameEq} {key = key} {value = value}
              {world = world} {error = error} current
              (MkSystemState ambient (MkCoeffectContext full unique)) = True)
          activeGlobal = rewrite globalFound in active
          0 declaredMember :
            (listMember @{keyEq} wanted
              (dependencies (componentProvisions (fiberComponent fiber))) = True)
          declaredMember = elemListMemberTrueQ wanted
            (dependencies (componentProvisions (fiberComponent fiber))) declared
      in rewrite activeGlobal in rewrite declaredMember in Refl
  providerInGivesActiveDeclaration nameEq keyEq ambient full unique
    (Bind current fiber :: rest) subset wanted provider found | False =
      let 0 tailTrue = providerInGivesActiveDeclaration nameEq keyEq ambient full
            unique rest (\entry, present => subset entry (There present)) wanted
            provider found
      in orRightTrue _ tailTrue

0 resolvedViewGivesClauseProviders :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  (state : SystemState name key value world error) ->
  resolveView @{nameEq} @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error} deps (registry state) = Just view ->
  activeProviderClauses name key world error value nameEq keyEq state deps =
    True
resolvedViewGivesClauseProviders nameEq keyEq [] EmptyView
  (MkSystemState ambient (MkCoeffectContext entries unique)) resolved = Refl
resolvedViewGivesClauseProviders nameEq keyEq (wanted :: rest) view
  (MkSystemState ambient (MkCoeffectContext entries unique)) resolved
  with (providerOf @{nameEq} @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error} wanted (MkCoeffectContext entries unique)) proof provider
  resolvedViewGivesClauseProviders nameEq keyEq (wanted :: rest) view
    (MkSystemState ambient (MkCoeffectContext entries unique))
    resolved | Nothing = case resolved of Refl impossible
  resolvedViewGivesClauseProviders nameEq keyEq (wanted :: rest) view
    (MkSystemState ambient (MkCoeffectContext entries unique))
    resolved | Just providerName
    with (resolveView @{nameEq} @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error} rest (MkCoeffectContext entries unique)) proof tailView
    resolvedViewGivesClauseProviders nameEq keyEq (wanted :: rest) view
      (MkSystemState ambient (MkCoeffectContext entries unique))
      resolved | Just providerName | Nothing =
        case resolved of Refl impossible
    resolvedViewGivesClauseProviders nameEq keyEq (wanted :: rest) view
      (MkSystemState ambient (MkCoeffectContext entries unique))
      resolved | Just providerName | Just restView =
        case justInjective resolved of
          Refl => andBothTrue _ _
            (providerInGivesActiveDeclaration nameEq keyEq ambient entries
              unique entries (\entry, present => present) wanted providerName
              provider)
            (resolvedViewGivesClauseProviders nameEq keyEq rest restView
              (MkSystemState ambient (MkCoeffectContext entries unique))
              tailView)

0 providerInTailIsJust :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) ->
  (current : name) -> (fiber : Fiber name key value world error) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  isJust (providerIn @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} wanted rest) = True ->
  isJust (providerIn @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} wanted
    (Bind current fiber :: rest)) = True
providerInTailIsJust nameEq keyEq wanted current fiber rest tailPresent
  with (isActive (fiberLifecycle fiber) &&
    memberKey @{keyEq} wanted (ownedValues (fiberTable fiber)))
  providerInTailIsJust nameEq keyEq wanted current fiber rest tailPresent |
    True = Refl
  providerInTailIsJust nameEq keyEq wanted current fiber rest tailPresent |
    False = tailPresent

0 activeProviderClauseConsQ :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (state : SystemState name key value world error) ->
  (current : name) -> (fiber : Fiber name key value world error) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  activeProviderClauseIn name key world error value nameEq keyEq wanted state
    (Bind current fiber :: rest) =
    ((activePredicate name key world error value nameEq state current &&
      listMember @{keyEq} wanted
        (dependencies (componentProvisions (fiberComponent fiber)))) ||
     activeProviderClauseIn name key world error value nameEq keyEq wanted state
       rest)
activeProviderClauseConsQ nameEq keyEq wanted state current fiber rest = Refl

orTrueChoice : (left, right : Bool) -> left || right = True ->
  Either (left = True) (right = True)
orTrueChoice False False valid = case valid of Refl impossible
orTrueChoice False True valid = Right Refl
orTrueChoice True right valid = Left Refl

0 activeDeclarationGivesProviderIn :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) ->
  (full : List (Binding name (FiberAt name key value world error))) ->
  (unique : UniqueKeys (bindingKeys full)) ->
  ActiveFibersProvideAll {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq keyEq
    (MkSystemState ambient (MkCoeffectContext full unique)) ->
  (scan : List (Binding name (FiberAt name key value world error))) ->
  ((entry : Binding name (FiberAt name key value world error)) ->
    Elem entry scan -> Elem entry full) ->
  (wanted : key) ->
  activeProviderClauseIn name key world error value nameEq keyEq wanted
    (MkSystemState ambient (MkCoeffectContext full unique)) scan = True ->
  isJust (providerIn @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} wanted scan) = True
activeDeclarationGivesProviderIn nameEq keyEq ambient full unique totals []
  subset wanted predicateTrue = case predicateTrue of Refl impossible
activeDeclarationGivesProviderIn nameEq keyEq ambient full unique totals
  (Bind current fiber :: rest) subset wanted predicateTrue =
    let 0 predicateCore :
          ((activePredicate name key world error value nameEq
              (MkSystemState ambient (MkCoeffectContext full unique)) current &&
            listMember @{keyEq} wanted
              (dependencies (componentProvisions (fiberComponent fiber)))) ||
           activeProviderClauseIn name key world error value nameEq keyEq wanted
             (MkSystemState ambient (MkCoeffectContext full unique)) rest = True)
        predicateCore = trans
          (sym (activeProviderClauseConsQ nameEq keyEq wanted
            (MkSystemState ambient (MkCoeffectContext full unique)) current
            fiber rest)) predicateTrue
    in case orTrueChoice
      (activePredicate name key world error value nameEq
        (MkSystemState ambient (MkCoeffectContext full unique)) current &&
       listMember @{keyEq} wanted
         (dependencies (componentProvisions (fiberComponent fiber))))
      (activeProviderClauseIn name key world error value nameEq keyEq wanted
        (MkSystemState ambient (MkCoeffectContext full unique)) rest)
      predicateCore of
      Right tailTrue => providerInTailIsJust nameEq keyEq wanted current fiber
        rest (activeDeclarationGivesProviderIn nameEq keyEq ambient full unique
          totals rest (\entry, present => subset entry (There present)) wanted
          tailTrue)
      Left headTrue =>
        let activeGlobal = andLeftTrue _ _ headTrue
            declaredMember = andRightTrue _ _ headTrue
            globalFound = entryLookupFromElemQ nameEq full unique current fiber
              (subset (Bind current fiber) Here)
            active = trans
              (sym (activePredicateAtFoundQ nameEq
                (MkSystemState ambient (MkCoeffectContext full unique)) current
                fiber globalFound))
              activeGlobal
            installedAll = totals current fiber globalFound active
            installed = installedAll wanted
              (listMemberTrueElemQ wanted
                (dependencies (componentProvisions (fiberComponent fiber)))
                declaredMember)
        in rewrite active in rewrite installed in Refl

isJustMapTrue : (function : a -> b) -> (candidate : Maybe a) ->
  isJust candidate = True -> isJust (map function candidate) = True
isJustMapTrue function Nothing present = case present of Refl impossible
isJustMapTrue function (Just value) present = Refl

0 clauseProvidersGiveResolvedView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  ActiveFibersProvideAll {name = name} {key = key} {value = value} {world = world} {error = error} nameEq keyEq state ->
  (deps : List key) ->
  activeProviderClauses name key world error value nameEq keyEq state deps =
    True ->
  isJust (resolveView @{nameEq} @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error} deps (registry state)) = True
clauseProvidersGiveResolvedView nameEq keyEq
  (MkSystemState ambient (MkCoeffectContext entries unique)) totals []
  providers = Refl
clauseProvidersGiveResolvedView nameEq keyEq
  (MkSystemState ambient (MkCoeffectContext entries unique)) totals
  (wanted :: rest) providers =
    let 0 headPredicate :
          (activeProviderClauseIn name key world error value nameEq keyEq wanted
            (MkSystemState ambient (MkCoeffectContext entries unique)) entries = True)
        headPredicate = andLeftTrue _ _ providers
        0 tailPredicates :
          (activeProviderClauses name key world error value nameEq keyEq
            (MkSystemState ambient (MkCoeffectContext entries unique))
            rest = True)
        tailPredicates = andRightTrue _ _ providers
        0 providerExists :
          (isJust (providerOf @{nameEq} @{keyEq} {name = name} {key = key}
            {value = value} {world = world} {error = error} wanted
            (MkCoeffectContext entries unique)) = True)
        providerExists = activeDeclarationGivesProviderIn nameEq keyEq ambient
          entries unique totals entries (\entry, present => present) wanted
          headPredicate
    in case isJustTrueWitness
      (providerOf @{nameEq} @{keyEq} {name = name} {key = key}
        {value = value} {world = world} {error = error} wanted
        (MkCoeffectContext entries unique)) providerExists of
      (providerName ** providerFound) => rewrite providerFound in
        isJustMapTrue (ProviderView providerName)
          (resolveView @{nameEq} @{keyEq} {name = name} {key = key}
            {value = value} {world = world} {error = error} rest
            (MkCoeffectContext entries unique))
          (clauseProvidersGiveResolvedView nameEq keyEq
            (MkSystemState ambient (MkCoeffectContext entries unique)) totals
            rest tailPredicates)

public export
targetMatchesGivesTarget :
  (nameEq : DecEq name) ->
  (candidate : Maybe (View name deps)) -> (view : View name deps) ->
  targetMatches @{nameEq} candidate view = True ->
  (target : View name deps ** candidate = Just target)
targetMatchesGivesTarget nameEq Nothing view matches =
  case matches of Refl impossible
targetMatchesGivesTarget nameEq (Just target) view matches =
  (target ** Refl)

public export
0 targetGivesSupportRuntimeClauses :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry state) = Just fiber ->
  (target : View name
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  targetFiber @{nameEq} @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error} fiber (registry state) = Just target ->
  (not (retired fiber) = True,
   activeProviderClauses name key world error value nameEq keyEq state
     (dependencies (componentDependencies (fiberComponent fiber))) = True)
targetGivesSupportRuntimeClauses nameEq keyEq state selected
  (MkFiber component parent False table lifecycle) found target targetFound =
    (Refl, resolvedViewGivesClauseProviders nameEq keyEq
      (dependencies (componentDependencies component)) target state targetFound)
targetGivesSupportRuntimeClauses nameEq keyEq state selected
  (MkFiber component parent True table lifecycle) found target targetFound =
    case targetFound of Refl impossible

public export
0 supportClauseAtFoundQ :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (predicate : name -> Bool) -> (selected : name) ->
  (ambient : world) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (unique : UniqueKeys (bindingKeys entries)) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  lookupEntries @{nameEq} selected entries =
    Just (MkFiber component parent retiredFlag table lifecycle) ->
  supportClause @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} predicate selected
    (MkSystemState ambient (MkCoeffectContext entries unique)) =
    (not retiredFlag &&
      (case parent of
        Root => True
        ChildOf parentName => predicate parentName) &&
      providerClausesFor name key world error value nameEq keyEq predicate
        entries (dependencies (componentDependencies component)))
supportClauseAtFoundQ nameEq keyEq predicate selected ambient entries unique
  component Root retiredFlag table lifecycle found = rewrite found in Refl
supportClauseAtFoundQ nameEq keyEq predicate selected ambient entries unique
  component (ChildOf parentName) retiredFlag table lifecycle found =
    rewrite found in Refl

public export
0 supportClauseGivesTarget :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  ActiveFibersProvideAll {name = name} {key = key} {value = value} {world = world} {error = error} nameEq keyEq state ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry state) = Just fiber ->
  supportClause @{nameEq} @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error}
    (activePredicate name key world error value nameEq state) selected state = True ->
  isJust (targetFiber @{nameEq} @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error} fiber (registry state)) = True
supportClauseGivesTarget nameEq keyEq
  state@(MkSystemState ambient (MkCoeffectContext entries unique)) totals selected
  fiber@(MkFiber component Root retired table lifecycle) found clauseTrue =
    let 0 clauseCore :
          (not retired &&
            (True && providerClausesFor name key world error value nameEq keyEq
              (activePredicate name key world error value nameEq state) entries
              (dependencies (componentDependencies component))) = True)
        clauseCore = trans
          (sym (supportClauseAtFoundQ nameEq keyEq
            (activePredicate name key world error value nameEq state) selected
            ambient entries unique component Root retired table lifecycle found))
          clauseTrue
        0 providersCore :
          (providerClausesFor name key world error value nameEq keyEq
            (activePredicate name key world error value nameEq state) entries
            (dependencies (componentDependencies component)) = True)
        providersCore = andThirdTrue (not retired) True
          (providerClausesFor name key world error value nameEq keyEq
            (activePredicate name key world error value nameEq state) entries
            (dependencies (componentDependencies component))) clauseCore
        0 providers :
          (activeProviderClauses name key world error value nameEq keyEq state
            (dependencies (componentDependencies component)) = True)
        providers = trans
          (activeProviderClausesExplicitQ nameEq keyEq ambient entries unique
            (dependencies (componentDependencies component))) providersCore
        0 resolved :
          (isJust (resolveView @{nameEq} @{keyEq} {name = name} {key = key}
            {value = value} {world = world} {error = error}
            (dependencies (componentDependencies component))
            (MkCoeffectContext entries unique)) = True)
        resolved = clauseProvidersGiveResolvedView nameEq keyEq state totals
          (dependencies (componentDependencies component)) providers
        0 notRetired : (not retired = True)
        notRetired = andLeftTrue (not retired)
          (True && providerClausesFor name key world error value nameEq keyEq
            (activePredicate name key world error value nameEq state) entries
            (dependencies (componentDependencies component))) clauseCore
    in case retired of
      False => resolved
      True => case notRetired of Refl impossible
supportClauseGivesTarget nameEq keyEq
  state@(MkSystemState ambient (MkCoeffectContext entries unique)) totals selected
  fiber@(MkFiber component (ChildOf parentName) retired table lifecycle) found
  clauseTrue =
    let 0 clauseCore :
          (not retired &&
            (activePredicate name key world error value nameEq state parentName &&
              providerClausesFor name key world error value nameEq keyEq
                (activePredicate name key world error value nameEq state) entries
                (dependencies (componentDependencies component))) = True)
        clauseCore = trans
          (sym (supportClauseAtFoundQ nameEq keyEq
            (activePredicate name key world error value nameEq state) selected
            ambient entries unique component (ChildOf parentName) retired table
            lifecycle found))
          clauseTrue
        0 providersCore :
          (providerClausesFor name key world error value nameEq keyEq
            (activePredicate name key world error value nameEq state) entries
            (dependencies (componentDependencies component)) = True)
        providersCore = andThirdTrue (not retired)
          (activePredicate name key world error value nameEq state parentName)
          (providerClausesFor name key world error value nameEq keyEq
            (activePredicate name key world error value nameEq state) entries
            (dependencies (componentDependencies component))) clauseCore
        0 providers :
          (activeProviderClauses name key world error value nameEq keyEq state
            (dependencies (componentDependencies component)) = True)
        providers = trans
          (activeProviderClausesExplicitQ nameEq keyEq ambient entries unique
            (dependencies (componentDependencies component))) providersCore
        0 resolved :
          (isJust (resolveView @{nameEq} @{keyEq} {name = name} {key = key}
            {value = value} {world = world} {error = error}
            (dependencies (componentDependencies component))
            (MkCoeffectContext entries unique)) = True)
        resolved = clauseProvidersGiveResolvedView nameEq keyEq state totals
          (dependencies (componentDependencies component)) providers
        0 notRetired : (not retired = True)
        notRetired = andLeftTrue (not retired)
          (activePredicate name key world error value nameEq state parentName &&
            providerClausesFor name key world error value nameEq keyEq
              (activePredicate name key world error value nameEq state) entries
              (dependencies (componentDependencies component))) clauseCore
    in case retired of
      False => resolved
      True => case notRetired of Refl impossible

public export
0 reachedActiveFibersProvideAll :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (reached : ReachedFromEmpty name key world error value nameEq keyEq state) ->
  TraceComponentsTotal nameEq keyEq (reachTrace reached) ->
  ActiveFibersProvideAll {name = name} {key = key} {value = value} {world = world} {error = error} nameEq keyEq state
reachedActiveFibersProvideAll nameEq keyEq reached totality =
  traceActiveFibersProvideAll nameEq keyEq (reachTrace reached)
    (reachAligned reached) totality
    (emptyActiveFibersProvideAll nameEq keyEq (reachInitial reached)
      (reachInitialEmpty reached))
