module DGamma.CalculusChecks

import DGamma.Core
import DGamma.Coeffects
import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.Section3Example
import Decidable.Equality
import Data.List.Elem
import Data.Maybe

%default total

public export
toyEmptySpec : CoeffectSpec ToyKey
toyEmptySpec = MkCoeffectSpec [] UniqueNil

public export
toySpecB : CoeffectSpec ToyKey
toySpecB = MkCoeffectSpec [ServiceB] (UniqueCons notInEmpty UniqueNil)

public export
contextA : Bool -> CoeffectContext ToyKey ToyValue
contextA value = MkCoeffectContext [Bind ServiceA value]
  (UniqueCons notInEmpty UniqueNil)

public export
contextB : Bool -> CoeffectContext ToyKey ToyValue
contextB value = MkCoeffectContext [Bind ServiceB value]
  (UniqueCons notInEmpty UniqueNil)

public export
ownedA : Bool -> OwnedTable ToyKey ToyValue DGamma.Section3Example.toySpecA
ownedA value = MkOwnedTable (contextA value) sound
  where
  0 sound : (k : ToyKey) -> Elem k [ServiceA] ->
    Elem k (dependencies DGamma.Section3Example.toySpecA)
  sound k present = present

public export
ownedB : Bool -> OwnedTable ToyKey ToyValue DGamma.CalculusChecks.toySpecB
ownedB value = MkOwnedTable (contextB value) sound
  where
  0 sound : (k : ToyKey) -> Elem k [ServiceB] ->
    Elem k (dependencies DGamma.CalculusChecks.toySpecB)
  sound k present = present

public export
providerInstall : StepEffect ToyKey ToyValue ToyRuntime String [] DGamma.Section3Example.toySpecA
providerInstall = MkStepEffect Nothing run witnessed
  where
  run : DepValues ToyKey ToyValue [] ->
        LocalState ToyKey ToyValue ToyRuntime DGamma.Section3Example.toySpecA ->
        Either String
          (LocalState ToyKey ToyValue ToyRuntime DGamma.Section3Example.toySpecA,
           LocalState ToyKey ToyValue ToyRuntime DGamma.Section3Example.toySpecA ->
             LocalState ToyKey ToyValue ToyRuntime DGamma.Section3Example.toySpecA)
  run NoDepValues before =
    let MkLocalState (MkToyRuntime provider consumer) previous = before
        after = MkLocalState (MkToyRuntime (not provider) consumer) (ownedA True)
        undo = the
          (LocalState ToyKey ToyValue ToyRuntime DGamma.Section3Example.toySpecA ->
           LocalState ToyKey ToyValue ToyRuntime DGamma.Section3Example.toySpecA)
          (\(MkLocalState (MkToyRuntime laterProvider laterConsumer) laterTable) =>
            MkLocalState (MkToyRuntime (not laterProvider) laterConsumer) previous)
     in Right (after, undo)

  0 witnessed : (cap : DepValues ToyKey ToyValue []) ->
    (before, after : LocalState ToyKey ToyValue ToyRuntime DGamma.Section3Example.toySpecA) ->
    (undo : LocalState ToyKey ToyValue ToyRuntime DGamma.Section3Example.toySpecA ->
            LocalState ToyKey ToyValue ToyRuntime DGamma.Section3Example.toySpecA) ->
    run cap before = Right (after, undo) -> undo after = before
  witnessed NoDepValues before after undo returned =
    replace
      {p = \outcome => case outcome of
        Left _ => Unit
        Right (next, inverse) => inverse next = before}
      returned (case before of
        MkLocalState (MkToyRuntime False consumer) table => Refl
        MkLocalState (MkToyRuntime True consumer) table => Refl)

public export
providerFinish : StepEffect ToyKey ToyValue ToyRuntime String [] DGamma.Section3Example.toySpecA
providerFinish = MkStepEffect Nothing run witnessed
  where
  run : DepValues ToyKey ToyValue [] ->
        LocalState ToyKey ToyValue ToyRuntime DGamma.Section3Example.toySpecA ->
        Either String
          (LocalState ToyKey ToyValue ToyRuntime DGamma.Section3Example.toySpecA,
           LocalState ToyKey ToyValue ToyRuntime DGamma.Section3Example.toySpecA ->
             LocalState ToyKey ToyValue ToyRuntime DGamma.Section3Example.toySpecA)
  run NoDepValues before = Right (before, id)

  0 witnessed : (cap : DepValues ToyKey ToyValue []) ->
    (before, after : LocalState ToyKey ToyValue ToyRuntime DGamma.Section3Example.toySpecA) ->
    (undo : LocalState ToyKey ToyValue ToyRuntime DGamma.Section3Example.toySpecA ->
            LocalState ToyKey ToyValue ToyRuntime DGamma.Section3Example.toySpecA) ->
    run cap before = Right (after, undo) -> undo after = before
  witnessed NoDepValues before after undo returned =
    replace
      {p = \outcome => case outcome of
        Left _ => Unit
        Right (next, inverse) => inverse next = before}
      returned Refl

public export
consumerInstall : StepEffect ToyKey ToyValue ToyRuntime String
  [ServiceA] DGamma.CalculusChecks.toySpecB
consumerInstall = MkStepEffect Nothing run witnessed
  where
  run : DepValues ToyKey ToyValue [ServiceA] ->
        LocalState ToyKey ToyValue ToyRuntime DGamma.CalculusChecks.toySpecB ->
        Either String
          (LocalState ToyKey ToyValue ToyRuntime DGamma.CalculusChecks.toySpecB,
           LocalState ToyKey ToyValue ToyRuntime DGamma.CalculusChecks.toySpecB ->
             LocalState ToyKey ToyValue ToyRuntime DGamma.CalculusChecks.toySpecB)
  run (OneDepValue service NoDepValues) before =
    let MkLocalState (MkToyRuntime provider consumer) previous = before
        nextConsumer = if service then not consumer else consumer
        after = MkLocalState (MkToyRuntime provider nextConsumer) (ownedB service)
        undo = the
          (LocalState ToyKey ToyValue ToyRuntime DGamma.CalculusChecks.toySpecB ->
           LocalState ToyKey ToyValue ToyRuntime DGamma.CalculusChecks.toySpecB)
          (\(MkLocalState (MkToyRuntime laterProvider laterConsumer) laterTable) =>
            MkLocalState
              (MkToyRuntime laterProvider
                (if service then not laterConsumer else laterConsumer))
              previous)
     in Right (after, undo)

  0 witnessed : (cap : DepValues ToyKey ToyValue [ServiceA]) ->
    (before, after : LocalState ToyKey ToyValue ToyRuntime DGamma.CalculusChecks.toySpecB) ->
    (undo : LocalState ToyKey ToyValue ToyRuntime DGamma.CalculusChecks.toySpecB ->
            LocalState ToyKey ToyValue ToyRuntime DGamma.CalculusChecks.toySpecB) ->
    run cap before = Right (after, undo) -> undo after = before
  witnessed (OneDepValue False NoDepValues) before after undo returned =
    replace
      {p = \outcome => case outcome of
        Left _ => Unit
        Right (next, inverse) => inverse next = before}
      returned (case before of
        MkLocalState (MkToyRuntime provider consumer) table => Refl)
  witnessed (OneDepValue True NoDepValues) before after undo returned =
    replace
      {p = \outcome => case outcome of
        Left _ => Unit
        Right (next, inverse) => inverse next = before}
      returned (case before of
        MkLocalState (MkToyRuntime provider False) table => Refl
        MkLocalState (MkToyRuntime provider True) table => Refl)

public export
raisingStep : StepEffect ToyKey ToyValue ToyRuntime String [] DGamma.CalculusChecks.toyEmptySpec
raisingStep = MkStepEffect Nothing
  (\NoDepValues, local => Left "boom")
  (\NoDepValues, before, after, undo, returned => absurd returned)

public export
providerComponent : Component ToyKey ToyValue ToyRuntime String
providerComponent = MkComponent DGamma.CalculusChecks.toyEmptySpec DGamma.Section3Example.toySpecA
  [providerInstall, providerFinish]

public export
consumerComponent : Component ToyKey ToyValue ToyRuntime String
consumerComponent = MkComponent DGamma.Section3Example.toySpecA DGamma.CalculusChecks.toySpecB [consumerInstall]

public export
emptyConsumerComponent : Component ToyKey ToyValue ToyRuntime String
emptyConsumerComponent = MkComponent DGamma.Section3Example.toySpecA DGamma.CalculusChecks.toyEmptySpec []

public export
failingComponent : Component ToyKey ToyValue ToyRuntime String
failingComponent = MkComponent DGamma.CalculusChecks.toyEmptySpec DGamma.CalculusChecks.toyEmptySpec [raisingStep]

public export
initialSystem : SystemState Nat ToyKey ToyValue ToyRuntime String
initialSystem = MkSystemState (MkToyRuntime False False)
  (emptyContext {key = Nat}
    {value = FiberAt Nat ToyKey ToyValue ToyRuntime String})

public export
tagEq : RuleTag -> RuleTag -> Bool
tagEq OInsertTag OInsertTag = True
tagEq ORetireTag ORetireTag = True
tagEq ORemoveTag ORemoveTag = True
tagEq LBeginTag LBeginTag = True
tagEq LIterTag LIterTag = True
tagEq LFinishTag LFinishTag = True
tagEq LDivertTag LDivertTag = True
tagEq LRaiseTag LRaiseTag = True
tagEq LLeaveTag LLeaveTag = True
tagEq LUnloadTag LUnloadTag = True
tagEq _ _ = False

public export
applyTagged : RuleTag -> Action Nat ToyKey ToyValue ToyRuntime String ->
  SystemState Nat ToyKey ToyValue ToyRuntime String ->
  Maybe (SystemState Nat ToyKey ToyValue ToyRuntime String)
applyTagged expected action state = case checkedApplyAction action state of
  Just (actual, after) => if tagEq expected actual then Just after else Nothing
  Nothing => Nothing

public export
providerBeginRun : Maybe (SystemState Nat ToyKey ToyValue ToyRuntime String)
providerBeginRun = do
  s1 <- applyTagged OInsertTag (OInsert 0 Root providerComponent) initialSystem
  applyTagged LBeginTag (LBegin 0) s1

||| The full replay map carries the table write as well as ambient state.
public export
fullEffectMapCarriesTable : Bool
fullEffectMapCarriesTable = case providerBeginRun of
  Nothing => False
  Just before => case partialEffectMapFor %search %search
    (LAdvance 0) LIterTag before (projectEffectState before) of
      Nothing => False
      Just after => case lookupBinding ServiceA (effectTables after 0) of
        Just True => case effectAmbient after of
          MkToyRuntime True False => True
          _ => False
        _ => False

||| Definition-60 generator regression: one iterator stage exposes its exact
||| per-yield inverse on full EffectState, independently of the final composite
||| accumulator. The inverse restores both ambient state and the actor table.
public export
yieldedInverseGeneratorRuntimeCheck : Bool
yieldedInverseGeneratorRuntimeCheck =
  let origin : EffectState Nat ToyKey ToyValue ToyRuntime
      origin = MkEffectState (MkToyRuntime False False)
        (\actor => emptyContext)
      fiber = freshFiber providerComponent Root
  in case iteratorStepEffect %search %search 0 fiber providerInstall EmptyView
    origin of
    Nothing => False
    Just (after, yielded) =>
      case (effectAmbient after, lookupBinding ServiceA (effectTables after 0)) of
        (MkToyRuntime True False, Just True) => case yielded after of
          Nothing => False
          Just restored =>
            case (effectAmbient restored,
              lookupBinding ServiceA (effectTables restored 0)) of
              (MkToyRuntime False False, Nothing) => True
              _ => False
        _ => False

sameToyBindings : List (Binding ToyKey ToyValue) ->
  List (Binding ToyKey ToyValue) -> Bool
sameToyBindings [] [] = True
sameToyBindings (Bind leftKey leftValue :: leftRest)
  (Bind rightKey rightValue :: rightRest) with (decEq leftKey rightKey)
  sameToyBindings (Bind key leftValue :: leftRest)
    (Bind key rightValue :: rightRest) | Yes Refl =
      leftValue == rightValue && sameToyBindings leftRest rightRest
  sameToyBindings (Bind leftKey leftValue :: leftRest)
    (Bind rightKey rightValue :: rightRest) | No _ = False
sameToyBindings _ _ = False

sameToyLocalRuntime : LocalState ToyKey ToyValue ToyRuntime provision ->
  LocalState ToyKey ToyValue ToyRuntime provision -> Bool
sameToyLocalRuntime (MkLocalState (MkToyRuntime leftProvider leftConsumer)
  leftTable) (MkLocalState (MkToyRuntime rightProvider rightConsumer)
  rightTable) =
    leftProvider == rightProvider && leftConsumer == rightConsumer &&
    sameToyBindings (bindings (ownedValues leftTable))
      (bindings (ownedValues rightTable))

||| Finding-9 executable regression. Two existing effectful provider steps yield
||| two inverses; the pre-repair `undo1 . undo2` accumulator and the repaired
||| inter-undo-normalizing construction recover bit-identical runtime worlds and
||| ordered binding lists from the same unload-normalized state.
public export
interUndoNormalizationRuntimeIdentity : Bool
interUndoNormalizationRuntimeIdentity =
  let initial : LocalState ToyKey ToyValue ToyRuntime
        DGamma.Section3Example.toySpecA
      initial = MkLocalState (MkToyRuntime False False) (ownedA False)
  in case runStepEffect providerInstall NoDepValues initial of
    Left _ => False
    Right (afterFirst, undoFirst) =>
      case runStepEffect providerInstall NoDepValues afterFirst of
        Left _ => False
        Right (afterSecond, undoSecond) =>
          let probe = normalizeLocal DGamma.Section3Example.toySpecA afterSecond
              oldAccumulator = undoFirst . undoSecond
              newAccumulator = pushLocalUndo DGamma.Section3Example.toySpecA
                (pushLocalUndo DGamma.Section3Example.toySpecA id undoFirst)
                undoSecond
          in sameToyLocalRuntime (oldAccumulator probe) (newAccumulator probe)

||| Dynamic-table/capability regression: the provider installs ServiceA and the
||| consumer reads that declared dependency to decide its ambient effect and own
||| ServiceB value.
public export
activationRun : Maybe (SystemState Nat ToyKey ToyValue ToyRuntime String)
activationRun = do
  s1 <- applyTagged OInsertTag (OInsert 0 Root providerComponent) initialSystem
  s2 <- applyTagged OInsertTag (OInsert 1 Root consumerComponent) s1
  s3 <- applyTagged LBeginTag (LBegin 0) s2
  s4 <- applyTagged LIterTag (LAdvance 0) s3
  s5 <- applyTagged LFinishTag (LAdvance 0) s4
  s6 <- applyTagged LBeginTag (LBegin 1) s5
  applyTagged LFinishTag (LAdvance 1) s6

public export
activationUsesResolution : Bool
activationUsesResolution = case activationRun of
  Nothing => False
  Just state => case worldState state of
    MkToyRuntime True True =>
      case valueFromProvider {name = Nat} {key = ToyKey} {value = ToyValue}
        {world = ToyRuntime} {error = String} 0 ServiceA (registry state) of
        Just True => case valueFromProvider {name = Nat} {key = ToyKey}
          {value = ToyValue} {world = ToyRuntime} {error = String}
          1 ServiceB (registry state) of
          Just True => True
          _ => False
        _ => False
    _ => False

||| Covers O-Insert, L-Begin, L-Iter, L-Finish, O-Retire, L-Leave,
||| guarded L-Unload, and O-Remove. The provider is asked to unload while relied
||| is true; success of the scenario requires that attempt to be rejected.
public export
guardedScenario : Maybe (SystemState Nat ToyKey ToyValue ToyRuntime String)
guardedScenario = do
  s1 <- applyTagged OInsertTag (OInsert 0 Root providerComponent) initialSystem
  s2 <- applyTagged OInsertTag (OInsert 1 Root consumerComponent) s1
  s3 <- applyTagged LBeginTag (LBegin 0) s2
  s4 <- applyTagged LIterTag (LAdvance 0) s3
  providerActive <- applyTagged LFinishTag (LAdvance 0) s4
  s6 <- applyTagged LBeginTag (LBegin 1) providerActive
  bothActive <- applyTagged LFinishTag (LAdvance 1) s6
  s8 <- applyTagged ORetireTag (ORetire 0) bothActive
  providerLeaving <- applyTagged LLeaveTag (LLeave 0) s8
  case checkedApplyAction (LUnload 0) providerLeaving of
    Just _ => Nothing
    Nothing => do
      s10 <- applyTagged ORetireTag (ORetire 1) providerLeaving
      s11 <- applyTagged LLeaveTag (LLeave 1) s10
      consumerGone <- applyTagged LUnloadTag (LUnload 1) s11
      providerGone <- applyTagged LUnloadTag (LUnload 0) consumerGone
      s14 <- applyTagged ORemoveTag (ORemove 1) providerGone
      applyTagged ORemoveTag (ORemove 0) s14

public export
guardedScenarioChecks : Bool
guardedScenarioChecks = case guardedScenario of
  Nothing => False
  Just final => case worldState final of
    MkToyRuntime False False => null (bindings (registry final)) && wellFormed final
    _ => False

||| A tiny declarative configuration surface for the CP3 reconciliation
||| example. Each reconciliation phase is a deterministic checked rule program;
||| impossible intermediate configurations return `Nothing`.
public export
data ToyDesiredConfiguration = FullStack | ProviderOnly | EmptyStack

public export
reconcileToy : ToyDesiredConfiguration ->
  SystemState Nat ToyKey ToyValue ToyRuntime String ->
  Maybe (SystemState Nat ToyKey ToyValue ToyRuntime String)
reconcileToy FullStack state = do
  s1 <- applyTagged OInsertTag (OInsert 0 Root providerComponent) state
  s2 <- applyTagged OInsertTag (OInsert 1 Root consumerComponent) s1
  s3 <- applyTagged LBeginTag (LBegin 0) s2
  s4 <- applyTagged LIterTag (LAdvance 0) s3
  s5 <- applyTagged LFinishTag (LAdvance 0) s4
  s6 <- applyTagged LBeginTag (LBegin 1) s5
  applyTagged LFinishTag (LAdvance 1) s6
reconcileToy ProviderOnly state = do
  s1 <- applyTagged ORetireTag (ORetire 1) state
  s2 <- applyTagged LLeaveTag (LLeave 1) s1
  s3 <- applyTagged LUnloadTag (LUnload 1) s2
  applyTagged ORemoveTag (ORemove 1) s3
reconcileToy EmptyStack state = do
  s1 <- applyTagged ORetireTag (ORetire 0) state
  s2 <- applyTagged LLeaveTag (LLeave 0) s1
  s3 <- applyTagged LUnloadTag (LUnload 0) s2
  applyTagged ORemoveTag (ORemove 0) s3

public export
reconciliationScenario : Maybe
  (SystemState Nat ToyKey ToyValue ToyRuntime String,
   SystemState Nat ToyKey ToyValue ToyRuntime String,
   SystemState Nat ToyKey ToyValue ToyRuntime String)
reconciliationScenario = do
  full <- reconcileToy FullStack initialSystem
  providerOnly <- reconcileToy ProviderOnly full
  empty <- reconcileToy EmptyStack providerOnly
  Just (full, providerOnly, empty)

||| Declarative `[provider,consumer] -> [provider] -> []` reconciliation.
||| Support agrees with the active fibers at both quiescent intermediate states,
||| and reversing both effect accumulators returns the unique empty outcome.
public export
reconciliationScenarioChecks : Bool
reconciliationScenarioChecks = case reconciliationScenario of
  Nothing => False
  Just (full, providerOnly, empty) =>
    case (worldState full, worldState providerOnly, worldState empty) of
      (MkToyRuntime True True, MkToyRuntime True False,
       MkToyRuntime False False) =>
        quiet full && quiet providerOnly && quiet empty &&
        isSupported 0 full && isSupported 1 full &&
        isSupported 0 providerOnly && not (isSupported 1 providerOnly) &&
        not (isSupported 0 empty) && not (isSupported 1 empty) &&
        null (bindings (registry empty)) && wellFormed empty
      _ => False

||| State immediately before the failing LAdvance.
public export
raisePrefix : Maybe (SystemState Nat ToyKey ToyValue ToyRuntime String)
raisePrefix = do
  s1 <- applyTagged OInsertTag (OInsert 2 Root failingComponent) initialSystem
  applyTagged LBeginTag (LBegin 2) s1

||| Regression for Table 1: the effect map of an actual L-Raise is identity,
||| not the nowhere-defined replay map.
public export
raiseMapIsIdentity : Bool
raiseMapIsIdentity = case raisePrefix of
  Nothing => False
  Just before => case partialWorldMapFor %search %search
    (LAdvance 2) LRaiseTag before (MkToyRuntime True False) of
      Just (MkToyRuntime True False) => True
      _ => False

||| L-Raise coverage.
public export
raiseRun : Maybe (SystemState Nat ToyKey ToyValue ToyRuntime String)
raiseRun = do
  s2 <- raisePrefix
  s3 <- applyTagged LRaiseTag (LAdvance 2) s2
  applyTagged LUnloadTag (LUnload 2) s3

public export
raiseScenario : Bool
raiseScenario = case raiseRun of
  Nothing => False
  Just final => True

public export
setupStale : Component ToyKey ToyValue ToyRuntime String ->
  Maybe (SystemState Nat ToyKey ToyValue ToyRuntime String)
setupStale consumer = do
  s1 <- applyTagged OInsertTag (OInsert 0 Root providerComponent) initialSystem
  s2 <- applyTagged OInsertTag (OInsert 1 Root consumer) s1
  s3 <- applyTagged LBeginTag (LBegin 0) s2
  s4 <- applyTagged LIterTag (LAdvance 0) s3
  s5 <- applyTagged LFinishTag (LAdvance 0) s4
  s6 <- applyTagged LBeginTag (LBegin 1) s5
  s7 <- applyTagged ORetireTag (ORetire 0) s6
  applyTagged LLeaveTag (LLeave 0) s7

||| Aborting L-Divert coverage and regression for the rejected empty-list
||| L-Finish: LAdvance on the stale empty program must itself divert.
public export
emptyStaleDiverts : Bool
emptyStaleDiverts = case setupStale emptyConsumerComponent of
  Nothing => False
  Just stale => case checkedApplyAction (LAdvance 1) stale of
    Just (LDivertTag, after) => case lookupFiber 1 (registry after) of
      Just fiber => case fiberLifecycle fiber of
        Unloading _ _ _ => True
        _ => False
      Nothing => False
    _ => False

public export
abortDivertScenario : Bool
abortDivertScenario = case setupStale emptyConsumerComponent of
  Nothing => False
  Just stale => case applyTagged LDivertTag (LDivert 1) stale of
    Just _ => True
    Nothing => False

||| Landing L-Divert coverage: the stale nonempty iteration runs, returns its
||| inverse, and lands directly in Unloading.
public export
landingDivertScenario : Bool
landingDivertScenario = case setupStale consumerComponent of
  Nothing => False
  Just stale => case applyTagged LDivertTag (LAdvance 1) stale of
    Just after => case lookupFiber 1 (registry after) of
      Just fiber => case fiberLifecycle fiber of
        Unloading _ _ _ => True
        _ => False
      Nothing => False
    Nothing => False

||| The checked evaluator can package a nonempty proof-indexed LTS step.
public export
proofTraceStarts : Bool
proofTraceStarts = isJust (fire %search %search
  (OInsert 0 Root providerComponent) initialSystem)

||| All ten tags and both L-Divert alternatives are covered across the checks.
public export
allRuleChecks : Bool
allRuleChecks = proofTraceStarts && fullEffectMapCarriesTable &&
  yieldedInverseGeneratorRuntimeCheck && interUndoNormalizationRuntimeIdentity &&
  activationUsesResolution &&
  reconciliationScenarioChecks && guardedScenarioChecks &&
  raiseMapIsIdentity && raiseScenario && emptyStaleDiverts && abortDivertScenario &&
  landingDivertScenario
