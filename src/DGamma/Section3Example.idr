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
toyGetA : lookupBinding {key = ToyKey} {value = ToyValue}
  ServiceA DGamma.Section3Example.toyAContext = Just False
toyGetA = Refl

public export
toyEmptyUnsatisfied : satisfies
  (emptyContext {key = ToyKey} {value = ToyValue})
  DGamma.Section3Example.toySpecA = False
toyEmptyUnsatisfied = Refl

public export
toyASatisfied : satisfies DGamma.Section3Example.toyAContext
  DGamma.Section3Example.toySpecA = True
toyASatisfied = Refl

public export
toyActivates : notify {key = ToyKey} {value = ToyValue}
  DGamma.Section3Example.toySpecA
  (emptyContext {key = ToyKey} {value = ToyValue})
  DGamma.Section3Example.toyAContext = Activating
toyActivates = rewrite toyEmptyUnsatisfied in Refl

public export
toySetBWorks :
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
toyProgramRuns :
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
failurePropagates :
  runMediated {key = ToyKey} {value = ToyValue}
    DGamma.Section3Example.failingSuite
    (Stage {suite = DGamma.Section3Example.failingSuite} FailA () (\_ => Done))
    DGamma.Section3Example.trueAContext = Nothing
failurePropagates = Refl
