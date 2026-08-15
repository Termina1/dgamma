module DGamma.CalculusChecks

import DGamma.Core
import DGamma.Effects
import DGamma.Coeffects
import DGamma.Calculus
import DGamma.Metatheory
import DGamma.Section3Example
import Decidable.Equality
import Data.List.Elem

%default total

public export
emptySpec : CoeffectSpec ToyKey
emptySpec = MkCoeffectSpec [] UniqueNil

public export
providerStep : StepEffect ToyRuntime String
providerStep = MkStepEffect {world = ToyRuntime} {error = String} run witnessed
  where
  run : ToyRuntime -> Either String (ToyRuntime, ToyRuntime -> ToyRuntime)
  run (MkToyRuntime provider consumer) =
    Right (MkToyRuntime (not provider) consumer,
      \(MkToyRuntime laterProvider laterConsumer) =>
        MkToyRuntime (not laterProvider) laterConsumer)

  0 witnessed : (before, after : ToyRuntime) ->
    (undo : ToyRuntime -> ToyRuntime) ->
    run before = Right (after, undo) -> undo after = before
  witnessed before after undo returned =
    replace
      {p = \outcome => case outcome of
        Left _ => Unit
        Right (next, inverse) => inverse next = before}
      returned (case before of
        MkToyRuntime False consumer => Refl
        MkToyRuntime True consumer => Refl)

public export
consumerStep : StepEffect ToyRuntime String
consumerStep = MkStepEffect {world = ToyRuntime} {error = String} run witnessed
  where
  run : ToyRuntime -> Either String (ToyRuntime, ToyRuntime -> ToyRuntime)
  run (MkToyRuntime provider consumer) =
    Right (MkToyRuntime provider (not consumer),
      \(MkToyRuntime laterProvider laterConsumer) =>
        MkToyRuntime laterProvider (not laterConsumer))

  0 witnessed : (before, after : ToyRuntime) ->
    (undo : ToyRuntime -> ToyRuntime) ->
    run before = Right (after, undo) -> undo after = before
  witnessed before after undo returned =
    replace
      {p = \outcome => case outcome of
        Left _ => Unit
        Right (next, inverse) => inverse next = before}
      returned (case before of
        MkToyRuntime provider False => Refl
        MkToyRuntime provider True => Refl)

public export
providerComponent : Component ToyKey ToyValue ToyRuntime String
providerComponent = MkComponent
  DGamma.CalculusChecks.emptySpec
  DGamma.Section3Example.toySpecA
  DGamma.Section3Example.toyAContext
  [DGamma.CalculusChecks.providerStep]
  sound
  where
  0 sound : (k : ToyKey) ->
    Elem k (bindingKeys (bindings DGamma.Section3Example.toyAContext)) ->
    Elem k (dependencies DGamma.Section3Example.toySpecA)
  sound ServiceA Here = Here
  sound ServiceA (There later) = absurd later
  sound ServiceB Here impossible
  sound ServiceB (There later) = absurd later

public export
consumerComponent : Component ToyKey ToyValue ToyRuntime String
consumerComponent = MkComponent
  DGamma.Section3Example.toySpecA
  DGamma.CalculusChecks.emptySpec
  (emptyContext {key = ToyKey} {value = ToyValue})
  [DGamma.CalculusChecks.consumerStep]
  sound
  where
  0 sound : (k : ToyKey) -> Elem k [] -> Elem k []
  sound k present impossible

public export
initialSystem : SystemState Nat ToyKey ToyValue ToyRuntime String
initialSystem = MkSystemState (MkToyRuntime False False)
  (emptyContext {key = Nat}
    {value = FiberAt Nat ToyKey ToyValue ToyRuntime String})

public export
applyState : Action Nat ToyKey ToyValue ToyRuntime String ->
  SystemState Nat ToyKey ToyValue ToyRuntime String ->
  Maybe (SystemState Nat ToyKey ToyValue ToyRuntime String)
applyState action state = map snd (applyAction action state)

||| A checked full lifecycle: insert both fibers, activate the provider, activate
||| its dependent, then retire/leave/unload the dependent before the provider.
public export
calculusScenario : Maybe (SystemState Nat ToyKey ToyValue ToyRuntime String)
calculusScenario = do
  insertedProvider <- applyState (OInsert 0 Root providerComponent) initialSystem
  insertedConsumer <- applyState (OInsert 1 Root consumerComponent) insertedProvider
  providerBeginning <- applyState (LBegin 0) insertedConsumer
  providerActive <- applyState (LAdvance 0) providerBeginning
  consumerBeginning <- applyState (LBegin 1) providerActive
  bothActive <- applyState (LAdvance 1) consumerBeginning
  consumerRetired <- applyState (ORetire 1) bothActive
  consumerLeaving <- applyState (LLeave 1) consumerRetired
  consumerInactive <- applyState (LUnload 1) consumerLeaving
  providerRetired <- applyState (ORetire 0) consumerInactive
  providerLeaving <- applyState (LLeave 0) providerRetired
  applyState (LUnload 0) providerLeaving

||| Runtime regression projections. They remain executable checks rather than
||| proof claims, so callers can evaluate them in JS or native backends.
public export
calculusScenarioRecovered : Bool
calculusScenarioRecovered = case calculusScenario of
  Nothing => False
  Just final => case worldState final of
    MkToyRuntime False False => True
    _ => False

public export
calculusScenarioNoActiveCoeffects : Bool
calculusScenarioNoActiveCoeffects = case calculusScenario of
  Nothing => False
  Just final => null (bindings (activeCoeffects (registry final)))

public export
calculusScenarioWellFormed : Bool
calculusScenarioWellFormed = case calculusScenario of
  Nothing => False
  Just final => wellFormed final
