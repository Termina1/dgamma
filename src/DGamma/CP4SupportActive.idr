module DGamma.CP4SupportActive

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4SupportQuiescence
import DGamma.CP4ParentSafety
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

0 notTrueMeansFalse : (flag : Bool) -> not flag = True -> flag = False
notTrueMeansFalse False valid = Refl
notTrueMeansFalse True valid = case valid of Refl impossible

0 andBothTrueA : (left, right : Bool) -> left = True -> right = True ->
  left && right = True
andBothTrueA False right leftTrue rightTrue = case leftTrue of Refl impossible
andBothTrueA True right leftTrue rightTrue = rightTrue

0 openQuietFiberIsActive :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (fiber : Fiber name key value world error) ->
  (context : Registry name key value world error) ->
  LifecycleOpen (fiberLifecycle fiber) ->
  quietFiber @{nameEq} @{keyEq} fiber context = True ->
  isActive (fiberLifecycle fiber) = True
openQuietFiberIsActive nameEq keyEq
  (MkFiber component parent retired table (Inactive outcome)) context opened
  quietFiber = void (lifecycleOpenInactiveQ opened)
  where
  lifecycleOpenInactiveQ : LifecycleOpen (Inactive outcome) -> Void
  lifecycleOpenInactiveQ OpenReloading impossible
  lifecycleOpenInactiveQ OpenActive impossible
openQuietFiberIsActive nameEq keyEq
  (MkFiber component parent retired table
    (Reloading remaining accumulator view)) context OpenReloading quietFiber =
      case quietFiber of Refl impossible
openQuietFiberIsActive nameEq keyEq
  (MkFiber component parent retired table (Active accumulator view)) context
  OpenActive quietFiber = Refl
openQuietFiberIsActive nameEq keyEq
  (MkFiber component parent retired table
    (Unloading accumulator view outcome)) context opened quietFiber =
      void (lifecycleOpenUnloadingQ opened)
  where
  lifecycleOpenUnloadingQ :
    LifecycleOpen (Unloading accumulator view outcome) -> Void
  lifecycleOpenUnloadingQ OpenReloading impossible
  lifecycleOpenUnloadingQ OpenActive impossible

0 parentOpenAtQuietIsActive :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  quiet @{nameEq} @{keyEq} state = True ->
  (parent : name) -> ParentOpenAt nameEq parent state ->
  activePredicate name key world error value nameEq state parent = True
parentOpenAtQuietIsActive nameEq keyEq state quietState parent
  (MkParentOpenAt fiber found opened) =
    let 0 quietParent = quietFiberFromState nameEq keyEq state quietState parent
          fiber found
        0 active = openQuietFiberIsActive nameEq keyEq fiber (registry state)
          opened quietParent
        0 observed = activePredicateAtFoundQ nameEq state parent fiber found
    in trans observed active

public export
0 activeGivesSupportClause :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  (reached : ReachedFromEmpty name key world error value nameEq keyEq state) ->
  RegistrationDiscipline protocol nameEq (reachTrace reached) ->
  ActiveFibersProvideAll nameEq keyEq state ->
  quiet @{nameEq} @{keyEq} state = True ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry state) = Just fiber ->
  isActive (fiberLifecycle fiber) = True ->
  supportClause @{nameEq} @{keyEq}
    (activePredicate name key world error value nameEq state) selected state =
      True
activeGivesSupportClause protocol nameEq keyEq state reached discipline totals
  quietState selected
  (MkFiber component parent retired table (Inactive outcome)) found active =
    case active of Refl impossible
activeGivesSupportClause protocol nameEq keyEq state reached discipline totals
  quietState selected
  (MkFiber component parent retired table
    (Reloading remaining accumulator view)) found active =
      case active of Refl impossible
activeGivesSupportClause protocol nameEq keyEq
  (MkSystemState ambient (MkCoeffectContext entries unique)) reached
  discipline totals quietState selected
  (MkFiber component parent retired table (Active accumulator view)) found active
  with (parent)
  activeGivesSupportClause protocol nameEq keyEq
    (MkSystemState ambient (MkCoeffectContext entries unique)) reached
    discipline totals quietState selected
    (MkFiber component parent retired table (Active accumulator view)) found active |
    Root =
    let 0 quietSelected = quietFiberFromState nameEq keyEq (MkSystemState ambient (MkCoeffectContext entries unique)) quietState
          selected (MkFiber component Root retired table
            (Active accumulator view)) found
        0 targetWitness = targetMatchesGivesTarget nameEq
          (targetFiber @{nameEq} @{keyEq}
            (MkFiber component Root retired table (Active accumulator view))
            (registry (MkSystemState ambient (MkCoeffectContext entries unique)))) view quietSelected
    in case targetWitness of
      (target ** targetFound) =>
        let 0 runtimeClauses = targetGivesSupportRuntimeClauses nameEq keyEq
              (MkSystemState ambient (MkCoeffectContext entries unique)) selected
              (MkFiber component Root retired table (Active accumulator view))
              found target targetFound
            0 notRetired = fst runtimeClauses
            0 providers = snd runtimeClauses
            0 providerCore :
              (providerClausesFor name key world error value nameEq keyEq
                (activePredicate name key world error value nameEq (MkSystemState ambient (MkCoeffectContext entries unique)))
                entries (dependencies (componentDependencies component)) = True)
            providerCore = trans
              (sym (activeProviderClausesExplicitQ nameEq keyEq ambient entries
                unique (dependencies (componentDependencies component))))
              providers
        in trans
          (supportClauseAtFoundQ nameEq keyEq
            (activePredicate name key world error value nameEq (MkSystemState ambient (MkCoeffectContext entries unique))) selected
            ambient entries unique component Root retired table
            (Active accumulator view) found)
          (andBothTrueA (not retired)
            (True && providerClausesFor name key world error value nameEq keyEq
              (activePredicate name key world error value nameEq (MkSystemState ambient (MkCoeffectContext entries unique))) entries
              (dependencies (componentDependencies component)))
            notRetired (andBothTrueA _ _ Refl providerCore))
  activeGivesSupportClause protocol nameEq keyEq
    (MkSystemState ambient (MkCoeffectContext entries unique)) reached
    discipline totals quietState selected
    (MkFiber component parent retired table
      (Active accumulator view)) found active | ChildOf parentName =
    let 0 quietSelected = quietFiberFromState nameEq keyEq (MkSystemState ambient (MkCoeffectContext entries unique)) quietState
          selected (MkFiber component (ChildOf parentName) retired table
            (Active accumulator view)) found
        0 targetWitness = targetMatchesGivesTarget nameEq
          (targetFiber @{nameEq} @{keyEq}
            (MkFiber component (ChildOf parentName) retired table
              (Active accumulator view))
            (registry (MkSystemState ambient (MkCoeffectContext entries unique)))) view quietSelected
    in case targetWitness of
      (target ** targetFound) =>
        let 0 runtimeClauses = targetGivesSupportRuntimeClauses nameEq keyEq
              (MkSystemState ambient (MkCoeffectContext entries unique)) selected
              (MkFiber component (ChildOf parentName) retired table
                (Active accumulator view))
              found target targetFound
            0 notRetired = fst runtimeClauses
            0 providers = snd runtimeClauses
            0 providerCore :
              (providerClausesFor name key world error value nameEq keyEq
                (activePredicate name key world error value nameEq (MkSystemState ambient (MkCoeffectContext entries unique)))
                entries (dependencies (componentDependencies component)) = True)
            providerCore = trans
              (sym (activeProviderClausesExplicitQ nameEq keyEq ambient entries
                unique (dependencies (componentDependencies component))))
              providers
            0 retiredFalse : (retired = False)
            retiredFalse = notTrueMeansFalse retired notRetired
            0 parentOpened : ParentOpenAt {name = name} {key = key}
              {value = value} {world = world} {error = error} nameEq parentName
              (MkSystemState ambient (MkCoeffectContext entries unique))
            parentOpened = reachedNonRetiredChildParentOpen protocol nameEq
              keyEq (MkSystemState ambient (MkCoeffectContext entries unique))
              reached discipline selected parentName
              (MkFiber component (ChildOf parentName) retired table
                (Active accumulator view)) found Refl retiredFalse
            0 parentSupported :
              (activePredicate name key world error value nameEq
                (MkSystemState ambient (MkCoeffectContext entries unique))
                parentName = True)
            parentSupported = parentOpenAtQuietIsActive nameEq keyEq
              (MkSystemState ambient (MkCoeffectContext entries unique))
              quietState parentName parentOpened
        in trans
          (supportClauseAtFoundQ nameEq keyEq
            (activePredicate name key world error value nameEq (MkSystemState ambient (MkCoeffectContext entries unique))) selected
            ambient entries unique component (ChildOf parentName) retired table
            (Active accumulator view) found)
          (andBothTrueA (not retired)
            (activePredicate name key world error value nameEq (MkSystemState ambient (MkCoeffectContext entries unique)) parentName &&
              providerClausesFor name key world error value nameEq keyEq
                (activePredicate name key world error value nameEq (MkSystemState ambient (MkCoeffectContext entries unique))) entries
                (dependencies (componentDependencies component)))
            notRetired (andBothTrueA _ _ parentSupported providerCore))

activeGivesSupportClause protocol nameEq keyEq state reached discipline totals
  quietState selected
  (MkFiber component parent retired table
    (Unloading accumulator view outcome)) found active =
      case active of Refl impossible

public export
0 supportClauseGivesActive :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  ActiveFibersProvideAll nameEq keyEq state ->
  quiet @{nameEq} @{keyEq} state = True ->
  noFailedFibers state = True ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry state) = Just fiber ->
  supportClause @{nameEq} @{keyEq}
    (activePredicate name key world error value nameEq state) selected state =
      True ->
  isActive (fiberLifecycle fiber) = True
supportClauseGivesActive nameEq keyEq state totals quietState noFailures selected
  (MkFiber component parent retired table (Inactive Nothing)) found
  clauseTrue =
    let 0 targetPresent = supportClauseGivesTarget nameEq keyEq state totals
          selected (MkFiber component parent retired table (Inactive Nothing))
          found clauseTrue
    in case isJustTrueWitness
      (targetFiber @{nameEq} @{keyEq}
        (MkFiber component parent retired table (Inactive Nothing))
        (registry state)) targetPresent of
      (target ** targetFound) =>
        let 0 quietSelected = quietFiberFromState nameEq keyEq state quietState
              selected (MkFiber component parent retired table (Inactive Nothing))
              found
            0 impossibleQuiet : (isNothing (Just target) = True)
            impossibleQuiet = replace
              {p = \candidate => isNothing candidate = True}
              targetFound quietSelected
        in case impossibleQuiet of Refl impossible
supportClauseGivesActive nameEq keyEq state totals quietState noFailures selected
  (MkFiber component parent retired table (Inactive (Just failure))) found
  clauseTrue =
    let 0 failureFree = noFailureFromState nameEq state noFailures selected
          (MkFiber component parent retired table (Inactive (Just failure)))
          found
    in case failureFree of Refl impossible
supportClauseGivesActive nameEq keyEq state totals quietState noFailures selected
  (MkFiber component parent retired table
    (Reloading remaining accumulator view)) found clauseTrue =
      let 0 quietSelected = quietFiberFromState nameEq keyEq state quietState
            selected (MkFiber component parent retired table
              (Reloading remaining accumulator view)) found
      in case quietSelected of Refl impossible
supportClauseGivesActive nameEq keyEq state totals quietState noFailures selected
  (MkFiber component parent retired table (Active accumulator view)) found
  clauseTrue = Refl
supportClauseGivesActive nameEq keyEq state totals quietState noFailures selected
  (MkFiber component parent retired table
    (Unloading accumulator view outcome)) found clauseTrue =
      let 0 quietSelected = quietFiberFromState nameEq keyEq state quietState
            selected (MkFiber component parent retired table
              (Unloading accumulator view outcome)) found
      in case quietSelected of Refl impossible

