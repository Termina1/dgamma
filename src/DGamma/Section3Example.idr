module DGamma.Section3Example

import DGamma.Core
import DGamma.Effects
import DGamma.Coeffects
import DGamma.Unified
import Decidable.Equality
import Data.List.Elem
import Data.Maybe

%default total

public export
data ToyKey = ServiceA | ServiceB

public export
DecEq ToyKey where
  decEq ServiceA ServiceA = Yes Refl
  decEq ServiceA ServiceB = No (\Refl impossible)
  decEq ServiceB ServiceA = No (\Refl impossible)
  decEq ServiceB ServiceB = Yes Refl

public export
ToyValue : ToyKey -> Type
ToyValue _ = Bool

public export
0 notInEmpty : Not (Elem key [])
notInEmpty elem impossible

public export
toyAContext : CoeffectContext ToyKey ToyValue
toyAContext = MkCoeffectContext [Bind ServiceA False]
  (UniqueCons notInEmpty UniqueNil)

public export
toySpecA : CoeffectSpec ToyKey
toySpecA = MkCoeffectSpec [ServiceA] (UniqueCons notInEmpty UniqueNil)

||| Executable Definition-23/26 checks.
public export
0 toyGetA : lookupBinding {key = ToyKey} {value = ToyValue}
  ServiceA DGamma.Section3Example.toyAContext = Just False
toyGetA = Refl

public export
0 toyEmptyUnsatisfied : satisfies
  (emptyContext {key = ToyKey} {value = ToyValue})
  DGamma.Section3Example.toySpecA = False
toyEmptyUnsatisfied = Refl

public export
0 toyASatisfied : satisfies DGamma.Section3Example.toyAContext
  DGamma.Section3Example.toySpecA = True
toyASatisfied = Refl

public export
0 toyActivates : notify {key = ToyKey} {value = ToyValue}
  DGamma.Section3Example.toySpecA
  (emptyContext {key = ToyKey} {value = ToyValue})
  DGamma.Section3Example.toyAContext = Activating
toyActivates = rewrite toyEmptyUnsatisfied in Refl

public export
0 toySetBWorks :
  case setFresh {key = ToyKey} {value = ToyValue}
    ServiceB True DGamma.Section3Example.toyAContext of
    Nothing => Void
    Just applied => lookupBinding ServiceB (coeffectAfter applied) = Just True
toySetBWorks = Refl

public export
boolNotOperation : CoeffectOperation Bool Unit Bool
boolNotOperation = MkCoeffectOperation EqEquivalence run witnessed respectful
  where
  run : Unit -> Bool -> Maybe (Bool, PartialMap Bool, Bool)
  run _ False = Just (True, \x => Just (not x), False)
  run _ True = Just (False, \x => Just (not x), True)

  0 witnessed : (arg : Unit) -> (before, after : Bool) ->
    (undo : PartialMap Bool) -> (result : Bool) ->
    run arg before = Just (after, undo, result) -> undo after = Just before
  witnessed arg before after undo result returned =
    replace
      {p = \maybeResult => case maybeResult of
        Nothing => Unit
        Just (next, inverse, out) => inverse next = Just before}
      returned (case before of False => Refl; True => Refl)

  0 respectful : (arg : Unit) -> {left, right : Bool} -> left = right ->
    OperationResultsRelated EqEquivalence (run arg left) (run arg right)
  respectful _ {left = False} Refl = ResultsDefined Refl Refl inverseRespect
    where
    0 inverseRespect : PartialMapsRelated EqEquivalence
      (\x => Just (not x)) (\x => Just (not x))
    inverseRespect Refl = PartialDefined Refl
  respectful _ {left = True} Refl = ResultsDefined Refl Refl inverseRespect
    where
    0 inverseRespect : PartialMapsRelated EqEquivalence
      (\x => Just (not x)) (\x => Just (not x))
    inverseRespect Refl = PartialDefined Refl

public export
0 boolNotUsesEq : valueEquivalence DGamma.Section3Example.boolNotOperation =
  (EqEquivalence {a = Bool})
boolNotUsesEq = Refl

public export
data ToyOp = ToggleA

public export
toyKeyedSuite : KeyedOperationSuite ToyKey ToyValue
toyKeyedSuite = MkKeyedOperationSuite
  (\_ => EqEquivalence)
  ToyOp
  (\ToggleA => ServiceA)
  (\ToggleA => Unit)
  (\ToggleA => Bool)
  (\ToggleA => DGamma.Section3Example.boolNotOperation)
  (\ToggleA => DGamma.Section3Example.boolNotUsesEq)

public export
toyProgram : Mediated DGamma.Section3Example.toyKeyedSuite
toyProgram = Stage {suite = DGamma.Section3Example.toyKeyedSuite}
  ToggleA () (\_ => Done)

||| Definition 41 executes a genuine partial coeffect operation.
public export
0 toyProgramRuns :
  case runMediated {key = ToyKey} {value = ToyValue}
    DGamma.Section3Example.toyKeyedSuite
    DGamma.Section3Example.toyProgram
    DGamma.Section3Example.toyAContext of
    Nothing => Void
    Just (after, undo) => lookupBinding ServiceA after = Just True
toyProgramRuns = Refl

||| A failing operation remains failure in the executable mediated interpreter;
||| it is not silently totalized to identity.
public export
failsOnTrue : CoeffectOperation Bool Unit Unit
failsOnTrue = MkCoeffectOperation EqEquivalence run witnessed respectful
  where
  run : Unit -> Bool -> Maybe (Bool, PartialMap Bool, Unit)
  run _ False = Just (False, \x => Just x, ())
  run _ True = Nothing

  0 witnessed : (arg : Unit) -> (before, after : Bool) ->
    (undo : PartialMap Bool) -> (result : Unit) ->
    run arg before = Just (after, undo, result) -> undo after = Just before
  witnessed arg before after undo result returned =
    replace
      {p = \maybeResult => case maybeResult of
        Nothing => Unit
        Just (next, inverse, out) => inverse next = Just before}
      returned (case before of False => Refl; True => ())

  0 respectful : (arg : Unit) -> {left, right : Bool} -> left = right ->
    OperationResultsRelated EqEquivalence (run arg left) (run arg right)
  respectful _ {left = False} Refl = ResultsDefined Refl Refl inverseRespect
    where
    0 inverseRespect : PartialMapsRelated EqEquivalence
      (\x => Just x) (\x => Just x)
    inverseRespect Refl = PartialDefined Refl
  respectful _ {left = True} Refl = ResultsUndefined

public export
0 failsOnTrueUsesEq : valueEquivalence DGamma.Section3Example.failsOnTrue =
  (EqEquivalence {a = Bool})
failsOnTrueUsesEq = Refl

public export
data FailingOp = FailA

public export
failingSuite : KeyedOperationSuite ToyKey ToyValue
failingSuite = MkKeyedOperationSuite
  (\_ => EqEquivalence)
  FailingOp
  (\FailA => ServiceA)
  (\FailA => Unit)
  (\FailA => Unit)
  (\FailA => DGamma.Section3Example.failsOnTrue)
  (\FailA => DGamma.Section3Example.failsOnTrueUsesEq)

public export
trueAContext : CoeffectContext ToyKey ToyValue
trueAContext = MkCoeffectContext [Bind ServiceA True]
  (UniqueCons notInEmpty UniqueNil)

public export
0 failurePropagates :
  runMediated {key = ToyKey} {value = ToyValue}
    DGamma.Section3Example.failingSuite
    (Stage {suite = DGamma.Section3Example.failingSuite} FailA () (\_ => Done))
    DGamma.Section3Example.trueAContext = Nothing
failurePropagates = Refl

public export
record ToyRuntime where
  constructor MkToyRuntime
  providerLoaded : Bool
  consumerLoaded : Bool

||| A small component interface for the Section-3 end-to-end scenario. Section 4
||| later refines this into fibers/LTS states; these fields already use the same
||| coeffect specifications/provisions and witnessed effects.
public export
record ToyComponent where
  constructor MkToyComponent
  requires : CoeffectSpec ToyKey
  provides : CoeffectSpec ToyKey
  componentEffect : EffStar ToyRuntime

public export
toggleProvider : EffStar ToyRuntime
toggleProvider = MkEffStar run witnessed
  where
  run : EffFn ToyRuntime
  run (MkToyRuntime provider consumer) =
    (MkToyRuntime (not provider) consumer,
     \(MkToyRuntime laterProvider laterConsumer) =>
       MkToyRuntime (not laterProvider) laterConsumer)

  0 witnessed : (world : ToyRuntime) ->
    snd (run world) (fst (run world)) = world
  witnessed (MkToyRuntime False consumer) = Refl
  witnessed (MkToyRuntime True consumer) = Refl

public export
toggleConsumer : EffStar ToyRuntime
toggleConsumer = MkEffStar run witnessed
  where
  run : EffFn ToyRuntime
  run (MkToyRuntime provider consumer) =
    (MkToyRuntime provider (not consumer),
     \(MkToyRuntime laterProvider laterConsumer) =>
       MkToyRuntime laterProvider (not laterConsumer))

  0 witnessed : (world : ToyRuntime) ->
    snd (run world) (fst (run world)) = world
  witnessed (MkToyRuntime provider False) = Refl
  witnessed (MkToyRuntime provider True) = Refl

public export
providerComponent : ToyComponent
providerComponent = MkToyComponent emptySpec DGamma.Section3Example.toySpecA
  DGamma.Section3Example.toggleProvider

public export
consumerComponent : ToyComponent
consumerComponent = MkToyComponent DGamma.Section3Example.toySpecA emptySpec
  DGamma.Section3Example.toggleConsumer

public export
activeCoeffects : ToyRuntime -> CoeffectContext ToyKey ToyValue
activeCoeffects (MkToyRuntime False _) = emptyContext
activeCoeffects (MkToyRuntime True _) = DGamma.Section3Example.toyAContext

public export
toyInitialRuntime : ToyRuntime
toyInitialRuntime = MkToyRuntime False False

public export
toyEffects : List (EffStar ToyRuntime)
toyEffects = [componentEffect DGamma.Section3Example.providerComponent,
              componentEffect DGamma.Section3Example.consumerComponent]

||| First load: the provider activates and makes the consumer's coeffect true.
public export
toyAfterProvider : ToyRuntime
toyAfterProvider = fst (runEff
  (componentEffect DGamma.Section3Example.providerComponent)
  DGamma.Section3Example.toyInitialRuntime)

public export
0 consumerSatisfiedAfterProvider : satisfies
  (activeCoeffects DGamma.Section3Example.toyAfterProvider)
  (requires DGamma.Section3Example.consumerComponent) = True
consumerSatisfiedAfterProvider = Refl

||| Second load: the consumer installs its own independent effect.
public export
toyAfterConsumer : ToyRuntime
toyAfterConsumer = fst (runEff
  (componentEffect DGamma.Section3Example.consumerComponent)
  DGamma.Section3Example.toyAfterProvider)

||| load/load executes both component effects.
public export
0 toyLoadsBoth : applyAll DGamma.Section3Example.toyEffects
  DGamma.Section3Example.toyInitialRuntime = MkToyRuntime True True
toyLoadsBoth = Refl

||| unload/unload uses the concrete inverses yielded by those loads. This is the
||| executable lifecycle endpoint, not merely an abstract equality.
public export
0 toyUnloadUnload : runUndoList
  (reverseList (collectUndos DGamma.Section3Example.toyEffects
    DGamma.Section3Example.toyInitialRuntime))
  (applyAll DGamma.Section3Example.toyEffects
    DGamma.Section3Example.toyInitialRuntime) =
  DGamma.Section3Example.toyInitialRuntime
toyUnloadUnload = reverseCollectedRecovery DGamma.Section3Example.toyEffects
  DGamma.Section3Example.toyInitialRuntime

||| Theorem 16 applied to the *actual lifted accumulator* used by the runtime.
public export
0 toyActualAccumulatorRecovery :
  let initialContext = MkEffectContext DGamma.Section3Example.toyInitialRuntime (\x => x)
   in (current (reverseActual DGamma.Section3Example.toyEffects initialContext) =
         DGamma.Section3Example.toyInitialRuntime,
       recover (reverseActual DGamma.Section3Example.toyEffects initialContext) =
         recover initialContext)
toyActualAccumulatorRecovery = reverseActualRecovery
  DGamma.Section3Example.toyEffects
  (MkEffectContext DGamma.Section3Example.toyInitialRuntime (\x => x))

||| After the final provider unload, the consumer coeffect is absent again.
public export
0 consumerUnsatisfiedAfterUnload : satisfies
  (activeCoeffects (current (reverseActual DGamma.Section3Example.toyEffects
    (MkEffectContext DGamma.Section3Example.toyInitialRuntime (\x => x)))))
  (requires DGamma.Section3Example.consumerComponent) = False
consumerUnsatisfiedAfterUnload = Refl
