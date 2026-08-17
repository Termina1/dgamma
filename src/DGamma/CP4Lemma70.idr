module DGamma.CP4Lemma70

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4SupportSolution
import DGamma.CP4SupportQuiescence
import DGamma.CP4SupportActive
import Decidable.Equality

%default total

0 boolEqualFromTrueIffQ : (left, right : Bool) ->
  (left = True -> right = True) ->
  (right = True -> left = True) -> left = right
boolEqualFromTrueIffQ False False forward backward = Refl
boolEqualFromTrueIffQ False True forward backward =
  case backward Refl of Refl impossible
boolEqualFromTrueIffQ True False forward backward =
  case forward Refl of Refl impossible
boolEqualFromTrueIffQ True True forward backward = Refl

activeFiberObservation : Maybe (Fiber name key value world error) -> Bool
activeFiberObservation Nothing = False
activeFiberObservation (Just fiber) = isActive (fiberLifecycle fiber)

supportFiberObservation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (predicate : name -> Bool) ->
  List (Binding name (FiberAt name key value world error)) ->
  Maybe (Fiber name key value world error) -> Bool
supportFiberObservation name key world error value nameEq keyEq predicate entries
  Nothing = False
supportFiberObservation name key world error value nameEq keyEq predicate entries
  (Just fiber) =
    not (retired fiber) &&
    (case fiberParent fiber of
      Root => True
      ChildOf parentName => predicate parentName) &&
    providerClausesFor name key world error value nameEq keyEq predicate entries
      (dependencies (componentDependencies (fiberComponent fiber)))

0 activeEqualsSupportAtFound :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (unique : UniqueKeys (bindingKeys entries)) ->
  (reached : ReachedFromEmpty name key world error value nameEq keyEq
    (MkSystemState ambient (MkCoeffectContext entries unique))) ->
  RegistrationDiscipline protocol nameEq (reachTrace reached) ->
  ActiveFibersProvideAll {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq keyEq
    (MkSystemState ambient (MkCoeffectContext entries unique)) ->
  quiet @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error}
    (MkSystemState ambient (MkCoeffectContext entries unique)) = True ->
  noFailedFibers {name = name} {key = key} {value = value}
    {world = world} {error = error}
    (MkSystemState ambient (MkCoeffectContext entries unique)) = True ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupEntries @{nameEq} {key = name}
    {value = FiberAt name key value world error} selected entries = Just fiber ->
  activeFiberObservation (Just fiber) =
  supportFiberObservation name key world error value nameEq keyEq
    (activePredicate name key world error value nameEq
      (MkSystemState ambient (MkCoeffectContext entries unique))) entries
    (Just fiber)
activeEqualsSupportAtFound protocol nameEq keyEq ambient entries unique reached
  discipline totals quietState noFailures selected
  (MkFiber component parent retired table lifecycle) found = case parent of
    Root =>
      let 0 clauseShape = supportClauseAtFoundQ nameEq keyEq
            (activePredicate name key world error value nameEq
              (MkSystemState ambient (MkCoeffectContext entries unique))) selected
            ambient entries unique component Root retired table lifecycle found
      in boolEqualFromTrueIffQ (isActive lifecycle)
        (not retired &&
          True && providerClausesFor name key world error value nameEq keyEq
            (activePredicate name key world error value nameEq
              (MkSystemState ambient (MkCoeffectContext entries unique)))
            entries (dependencies (componentDependencies component)))
        (\activeTrue => trans (sym clauseShape)
          (activeGivesSupportClause protocol nameEq keyEq
            (MkSystemState ambient (MkCoeffectContext entries unique)) reached
            discipline totals quietState selected
            (MkFiber component Root retired table lifecycle) found activeTrue))
        (\clauseTrue => supportClauseGivesActive nameEq keyEq
          (MkSystemState ambient (MkCoeffectContext entries unique)) totals
          quietState noFailures selected
          (MkFiber component Root retired table lifecycle) found
          (trans clauseShape clauseTrue))
    ChildOf parentName =>
      let 0 clauseShape = supportClauseAtFoundQ nameEq keyEq
            (activePredicate name key world error value nameEq
              (MkSystemState ambient (MkCoeffectContext entries unique))) selected
            ambient entries unique component (ChildOf parentName) retired table
            lifecycle found
      in boolEqualFromTrueIffQ (isActive lifecycle)
        (not retired &&
          activePredicate name key world error value nameEq
            (MkSystemState ambient (MkCoeffectContext entries unique))
            parentName &&
          providerClausesFor name key world error value nameEq keyEq
            (activePredicate name key world error value nameEq
              (MkSystemState ambient (MkCoeffectContext entries unique)))
            entries (dependencies (componentDependencies component)))
        (\activeTrue => trans (sym clauseShape)
          (activeGivesSupportClause protocol nameEq keyEq
            (MkSystemState ambient (MkCoeffectContext entries unique)) reached
            discipline totals quietState selected
            (MkFiber component (ChildOf parentName) retired table lifecycle)
            found activeTrue))
        (\clauseTrue => supportClauseGivesActive nameEq keyEq
          (MkSystemState ambient (MkCoeffectContext entries unique)) totals
          quietState noFailures selected
          (MkFiber component (ChildOf parentName) retired table lifecycle) found
          (trans clauseShape clauseTrue))

0 transportObservedSupport :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (predicate : name -> Bool) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (candidate : Maybe (Fiber name key value world error)) ->
  (fiber : Fiber name key value world error) ->
  candidate = Just fiber ->
  activeFiberObservation (Just fiber) =
    supportFiberObservation name key world error value nameEq keyEq predicate
      entries (Just fiber) ->
  activeFiberObservation candidate =
    supportFiberObservation name key world error value nameEq keyEq predicate
      entries candidate
transportObservedSupport nameEq keyEq predicate entries candidate fiber found
  core = replace
    {p = \observed => activeFiberObservation observed =
      supportFiberObservation name key world error value nameEq keyEq predicate
        entries observed}
    (sym found) core

0 activePredicateObservationQ :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (ambient : world) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (unique : UniqueKeys (bindingKeys entries)) -> (selected : name) ->
  activePredicate name key world error value nameEq
    (MkSystemState ambient (MkCoeffectContext entries unique)) selected =
  activeFiberObservation (lookupEntries @{nameEq} selected entries)
activePredicateObservationQ nameEq ambient entries unique selected
  with (lookupEntries @{nameEq} selected entries)
  activePredicateObservationQ nameEq ambient entries unique selected | Nothing =
    Refl
  activePredicateObservationQ nameEq ambient entries unique selected |
    Just fiber = Refl

0 supportClauseObservationQ :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (ambient : world) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (unique : UniqueKeys (bindingKeys entries)) ->
  (predicate : name -> Bool) -> (selected : name) ->
  supportClause @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} predicate selected
    (MkSystemState ambient (MkCoeffectContext entries unique)) =
  supportFiberObservation name key world error value nameEq keyEq predicate
    entries (lookupEntries @{nameEq} selected entries)
supportClauseObservationQ nameEq keyEq ambient entries unique predicate selected
  with (lookupEntries @{nameEq} selected entries)
  supportClauseObservationQ nameEq keyEq ambient entries unique predicate selected |
    Nothing = Refl
  supportClauseObservationQ nameEq keyEq ambient entries unique predicate selected |
    Just fiber with (fiberParent fiber)
    supportClauseObservationQ nameEq keyEq ambient entries unique predicate
      selected | Just fiber | Root = Refl
    supportClauseObservationQ nameEq keyEq ambient entries unique predicate
      selected | Just fiber | ChildOf parentName = Refl

0 observationEqualityFromPresent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (predicate : name -> Bool) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (candidate : Maybe (Fiber name key value world error)) ->
  ((fiber : Fiber name key value world error) -> candidate = Just fiber ->
    activeFiberObservation (Just fiber) =
      supportFiberObservation name key world error value nameEq keyEq predicate
        entries (Just fiber)) ->
  activeFiberObservation candidate =
    supportFiberObservation name key world error value nameEq keyEq predicate
      entries candidate
observationEqualityFromPresent nameEq keyEq predicate entries Nothing present =
  Refl
observationEqualityFromPresent nameEq keyEq predicate entries (Just fiber)
  present = present fiber Refl

0 activePredicateIsSupportSolution :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  (reached : ReachedFromEmpty name key world error value nameEq keyEq state) ->
  RegistrationDiscipline protocol nameEq (reachTrace reached) ->
  ActiveFibersProvideAll nameEq keyEq state ->
  quiet @{nameEq} @{keyEq} state = True ->
  noFailedFibers state = True ->
  SupportSolution @{nameEq} @{keyEq}
    (activePredicate name key world error value nameEq state) state
activePredicateIsSupportSolution protocol nameEq keyEq
  (MkSystemState ambient (MkCoeffectContext entries unique)) reached discipline
  totals quietState noFailures selected =
    trans (activePredicateObservationQ nameEq ambient entries unique selected)
      (trans
        (observationEqualityFromPresent nameEq keyEq
          (activePredicate name key world error value nameEq
            (MkSystemState ambient (MkCoeffectContext entries unique))) entries
          (lookupEntries @{nameEq} selected entries)
          (\fiber, found => activeEqualsSupportAtFound protocol nameEq keyEq
            ambient entries unique reached discipline totals quietState
            noFailures selected fiber found))
        (sym (supportClauseObservationQ nameEq keyEq ambient entries unique
          (activePredicate name key world error value nameEq
            (MkSystemState ambient (MkCoeffectContext entries unique)))
          selected)))

||| Constructive implementation of paper Lemma 70. Lemma 68 supplies unique
||| fixed-point support; repaired Definition 69 supplies actual Active-table
||| totality; quiescence plus retirement provenance identifies that fixed point
||| with the runtime Active fibers.
public export
0 supportAtQuiescenceTheoremProof :
  (name : Type) -> (key : Type) -> (value : key -> Type) ->
  (world, error : Type) ->
  supportAtQuiescenceTheorem name key value world error
supportAtQuiescenceTheoremProof name key value world error nameEq keyEq protocol
  state reached discipline precedenceAcyclic quietState noFailures totality =
    let 0 totals = reachedActiveFibersProvideAll nameEq keyEq reached totality
        0 solution = activePredicateIsSupportSolution protocol nameEq keyEq state
          reached discipline totals quietState noFailures
        0 wellFoundedResult = supportWellFoundedUnderDiscipline nameEq keyEq
          protocol state reached discipline precedenceAcyclic
    in \selected => sym (uniqueSupportSolution wellFoundedResult
      (activePredicate name key world error value nameEq state) solution selected)
