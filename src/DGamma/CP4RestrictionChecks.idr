module DGamma.CP4RestrictionChecks

import DGamma.Calculus
import DGamma.CP4IndependenceNonVacuity
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CalculusChecks
import DGamma.Section3Example
import Data.List.Elem
import Decidable.Equality

%default total

0 serviceANotInB : Not (Elem ServiceA [ServiceB])
serviceANotInB Here impossible
serviceANotInB (There later) impossible

0 serviceBNotInA : Not (Elem ServiceB [ServiceA])
serviceBNotInA Here impossible
serviceBNotInA (There later) impossible

public export
reverseOrderSpec : CoeffectSpec ToyKey
DGamma.CP4RestrictionChecks.reverseOrderSpec = MkCoeffectSpec [ServiceA, ServiceB]
  (UniqueCons serviceANotInB (UniqueCons notInEmpty UniqueNil))

reverseContext : CoeffectContext ToyKey ToyValue
reverseContext = MkCoeffectContext [Bind ServiceB False, Bind ServiceA False]
  (UniqueCons serviceBNotInA (UniqueCons notInEmpty UniqueNil))

reverseOwned : OwnedTable ToyKey ToyValue DGamma.CP4RestrictionChecks.reverseOrderSpec
reverseOwned = MkOwnedTable reverseContext sound
  where
  0 sound : (k : ToyKey) -> Elem k [ServiceB, ServiceA] ->
    Elem k (dependencies DGamma.CP4RestrictionChecks.reverseOrderSpec)
  sound ServiceB Here = There Here
  sound ServiceB (There Here) impossible
  sound ServiceA Here impossible
  sound ServiceA (There Here) = Here

orderWorld : OwnedTable ToyKey ToyValue DGamma.CP4RestrictionChecks.reverseOrderSpec -> ToyRuntime
orderWorld table = case bindings (ownedValues table) of
  Bind ServiceB value :: rest => MkToyRuntime True False
  _ => MkToyRuntime False False

orderSensitiveStep : StepEffect ToyKey ToyValue ToyRuntime String [] DGamma.CP4RestrictionChecks.reverseOrderSpec
orderSensitiveStep = MkStepEffect Nothing run witnessed
  where
  run : DepValues ToyKey ToyValue [] ->
    LocalState ToyKey ToyValue ToyRuntime DGamma.CP4RestrictionChecks.reverseOrderSpec ->
    Either String
      (LocalState ToyKey ToyValue ToyRuntime DGamma.CP4RestrictionChecks.reverseOrderSpec,
       LocalState ToyKey ToyValue ToyRuntime DGamma.CP4RestrictionChecks.reverseOrderSpec ->
         LocalState ToyKey ToyValue ToyRuntime DGamma.CP4RestrictionChecks.reverseOrderSpec)
  run NoDepValues before@(MkLocalState world table) =
    Right (MkLocalState (orderWorld table) table, (\later => before))

  0 witnessed : (capability : DepValues ToyKey ToyValue []) ->
    (before, after : LocalState ToyKey ToyValue ToyRuntime DGamma.CP4RestrictionChecks.reverseOrderSpec) ->
    (undo : LocalState ToyKey ToyValue ToyRuntime DGamma.CP4RestrictionChecks.reverseOrderSpec ->
      LocalState ToyKey ToyValue ToyRuntime DGamma.CP4RestrictionChecks.reverseOrderSpec) ->
    run capability before = Right (after, undo) -> undo after = before
  witnessed NoDepValues before@(MkLocalState world table) after undo returned =
    replace
      {p = \outcome => case outcome of
        Left err => Unit
        Right (next, inverse) => inverse next = before}
      returned Refl

reverseComponent : Component ToyKey ToyValue ToyRuntime String
reverseComponent = MkComponent toyEmptySpec DGamma.CP4RestrictionChecks.reverseOrderSpec [orderSensitiveStep]

reverseFiber : Fiber Nat ToyKey ToyValue ToyRuntime String
reverseFiber = MkFiber reverseComponent Root False reverseOwned
  (Reloading [orderSensitiveStep] (\local => local) EmptyView)

reverseRegistry : Registry Nat ToyKey ToyValue ToyRuntime String
reverseRegistry = MkCoeffectContext [Bind 0 reverseFiber]
  (UniqueCons notInEmpty UniqueNil)

public export
reverseOrderBefore : SystemState Nat ToyKey ToyValue ToyRuntime String
DGamma.CP4RestrictionChecks.reverseOrderBefore = MkSystemState (MkToyRuntime False False) reverseRegistry

legacyRestricted : OwnedTable ToyKey ToyValue DGamma.CP4RestrictionChecks.reverseOrderSpec
legacyRestricted = restrictOwned DGamma.CP4RestrictionChecks.reverseOrderSpec reverseContext

preservingRestricted : OwnedTable ToyKey ToyValue DGamma.CP4RestrictionChecks.reverseOrderSpec
preservingRestricted = restrictOwnedPreservingOrder DGamma.CP4RestrictionChecks.reverseOrderSpec reverseContext

legacyWorld : ToyRuntime
DGamma.CP4RestrictionChecks.legacyWorld = case runStepEffect orderSensitiveStep NoDepValues
  (MkLocalState (MkToyRuntime False False) legacyRestricted) of
  Left err => MkToyRuntime True True
  Right (after, undo) => localWorld after

preservingWorld : ToyRuntime
DGamma.CP4RestrictionChecks.preservingWorld = case runStepEffect orderSensitiveStep NoDepValues
  (MkLocalState (MkToyRuntime False False) preservingRestricted) of
  Left err => MkToyRuntime False True
  Right (after, undo) => localWorld after

independentComponent : Component ToyKey ToyValue ToyRuntime String
independentComponent = MkComponent toyEmptySpec toyEmptySpec []

independentFiber : Fiber Nat ToyKey ToyValue ToyRuntime String
independentFiber = freshFiber independentComponent Root

independentRegistry : Registry Nat ToyKey ToyValue ToyRuntime String
independentRegistry = MkCoeffectContext [Bind (the Nat 7) independentFiber]
  (UniqueCons notInEmpty UniqueNil)

independentBefore : SystemState Nat ToyKey ToyValue ToyRuntime String
DGamma.CP4RestrictionChecks.independentBefore = MkSystemState (MkToyRuntime False False) independentRegistry

independentAfter : SystemState Nat ToyKey ToyValue ToyRuntime String
DGamma.CP4RestrictionChecks.independentAfter = MkSystemState (MkToyRuntime False False)
  (replaceBinding (the Nat 7) (retireFiber independentFiber) independentRegistry)

0 independentChecked : checkedApplyAction @{the (DecEq Nat) %search}
  @{the (DecEq ToyKey) %search} (ORetire (the Nat 7)) DGamma.CP4RestrictionChecks.independentBefore =
  Just (ORetireTag, DGamma.CP4RestrictionChecks.independentAfter)
independentChecked = Refl

0 independentTransition : Transition DGamma.CP4RestrictionChecks.independentBefore DGamma.CP4RestrictionChecks.independentAfter
DGamma.CP4RestrictionChecks.independentTransition = Fired %search %search (ORetire (the Nat 7)) ORetireTag
  independentChecked

0 independentSingletonTrace : Transitions DGamma.CP4RestrictionChecks.independentBefore DGamma.CP4RestrictionChecks.independentAfter
DGamma.CP4RestrictionChecks.independentSingletonTrace = MoreTransitions DGamma.CP4RestrictionChecks.independentTransition NoTransitions

||| Corrected Definition-60 non-vacuity on a concrete nonempty checked trace.
public export
0 correctedTraceIndependentWitness :
  TraceIndependent Nat ToyKey ToyRuntime String ToyValue %search
    DGamma.CP4RestrictionChecks.independentSingletonTrace
correctedTraceIndependentWitness = singletonTraceIndependent %search %search
  DGamma.CP4RestrictionChecks.independentTransition

||| PrefixRecoveryIndependent is Definition 60 itself; this separately pins the
||| corrected premise alias on the same nonempty trace.
public export
0 correctedPrefixIndependentWitness :
  PrefixRecoveryIndependent Nat ToyKey ToyRuntime String ToyValue %search %search
    (the Nat 7) DGamma.CP4RestrictionChecks.independentSingletonTrace
correctedPrefixIndependentWitness = correctedTraceIndependentWitness

||| The pre-Finding-10 relation: ambient equality plus per-key lookup equality.
||| It is retained only as a negative regression, never as a semantic alias.
LegacyLookupRelated :
  {name, key, world : Type} -> {value : key -> Type} ->
  (keyEq : DecEq key) ->
  EffectState name key value world -> EffectState name key value world -> Type
LegacyLookupRelated {name} {key} keyEq left right =
  (effectAmbient left = effectAmbient right,
   (selected : name) -> (k : key) ->
     lookupBinding @{keyEq} k (effectTables left selected) =
     lookupBinding @{keyEq} k (effectTables right selected))

forwardContext : CoeffectContext ToyKey ToyValue
forwardContext = MkCoeffectContext [Bind ServiceA False, Bind ServiceB False]
  (UniqueCons serviceANotInB (UniqueCons notInEmpty UniqueNil))

forwardOwned : OwnedTable ToyKey ToyValue DGamma.CP4RestrictionChecks.reverseOrderSpec
forwardOwned = MkOwnedTable forwardContext sound
  where
  0 sound : (k : ToyKey) -> Elem k [ServiceA, ServiceB] ->
    Elem k (dependencies DGamma.CP4RestrictionChecks.reverseOrderSpec)
  sound ServiceA Here = Here
  sound ServiceA (There Here) impossible
  sound ServiceB Here impossible
  sound ServiceB (There Here) = There Here

orderedEffectTables : Nat -> CoeffectContext ToyKey ToyValue
orderedEffectTables Z = forwardContext
orderedEffectTables (S selected) = emptyContext

reverseEffectTables : Nat -> CoeffectContext ToyKey ToyValue
reverseEffectTables Z = reverseContext
reverseEffectTables (S selected) = emptyContext

orderedEffectState : EffectState Nat ToyKey ToyValue ToyRuntime
orderedEffectState = MkEffectState (MkToyRuntime False False) orderedEffectTables

reverseEffectState : EffectState Nat ToyKey ToyValue ToyRuntime
reverseEffectState = MkEffectState (MkToyRuntime False False) reverseEffectTables

||| The old lookup-only relation cannot see the reversed runtime binding order.
public export
0 legacyOrderBlindnessWitness : LegacyLookupRelated
  (the (DecEq ToyKey) %search)
  DGamma.CP4RestrictionChecks.orderedEffectState
  DGamma.CP4RestrictionChecks.reverseEffectState
legacyOrderBlindnessWitness = (Refl, lookups)
  where
  0 lookups : (selected : Nat) -> (k : ToyKey) ->
    lookupBinding @{the (DecEq ToyKey) %search} k
      (effectTables DGamma.CP4RestrictionChecks.orderedEffectState selected) =
    lookupBinding @{the (DecEq ToyKey) %search} k
      (effectTables DGamma.CP4RestrictionChecks.reverseEffectState selected)
  lookups Z ServiceA = Refl
  lookups Z ServiceB = Refl
  lookups (S selected) ServiceA = Refl
  lookups (S selected) ServiceB = Refl

0 orderedBindingsDiffer : Not
  (bindings DGamma.CP4RestrictionChecks.forwardContext =
   bindings DGamma.CP4RestrictionChecks.reverseContext)
orderedBindingsDiffer Refl impossible

||| Finding #10's ordered-context relation correctly rejects the same pair.
public export
0 strengthenedRelationRejectsOrderMismatch :
  EffectStateRelated (the (DecEq ToyKey) %search)
    DGamma.CP4RestrictionChecks.orderedEffectState
    DGamma.CP4RestrictionChecks.reverseEffectState -> Void
strengthenedRelationRejectsOrderMismatch related =
  orderedBindingsDiffer (tablesExact related 0)

||| Executable half of the discriminating regression: the host callback sees
||| the order that the old relation forgot and returns different worlds.
public export
effectRelationOrderRegression : Bool
effectRelationOrderRegression =
  case runStepEffect orderSensitiveStep NoDepValues
    (MkLocalState (MkToyRuntime False False) forwardOwned) of
    Left err => False
    Right (forwardAfter, forwardUndo) =>
      case runStepEffect orderSensitiveStep NoDepValues
        (MkLocalState (MkToyRuntime False False) reverseOwned) of
        Left err => False
        Right (reverseAfter, reverseUndo) =>
          let MkToyRuntime forwardProvider forwardConsumer = localWorld forwardAfter
              MkToyRuntime reverseProvider reverseConsumer = localWorld reverseAfter
          in not forwardProvider && reverseProvider

public export
reverseOrderRestrictionRegression : Bool
reverseOrderRestrictionRegression =
  case applyAction @{the (DecEq Nat) %search} @{the (DecEq ToyKey) %search} (LAdvance 0) DGamma.CP4RestrictionChecks.reverseOrderBefore of
    Just (LFinishTag, actual) =>
      case partialEffectMapFor %search %search (LAdvance 0) LFinishTag
        DGamma.CP4RestrictionChecks.reverseOrderBefore (projectEffectState DGamma.CP4RestrictionChecks.reverseOrderBefore) of
        Just moved =>
          let MkToyRuntime actualProvider actualConsumer = worldState actual
              MkToyRuntime movedProvider movedConsumer = effectAmbient moved
              MkToyRuntime oldProvider oldConsumer = DGamma.CP4RestrictionChecks.legacyWorld in
          actualProvider && movedProvider && not oldProvider
        Nothing => False
    _ => False
