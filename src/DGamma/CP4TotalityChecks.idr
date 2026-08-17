module DGamma.CP4TotalityChecks

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4SupportQuiescence
import DGamma.Section3Example
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

public export
counterKeyEq : DecEq ToyKey
counterKeyEq = %search

private
counterEmptySpec : CoeffectSpec ToyKey
counterEmptySpec = MkCoeffectSpec [] UniqueNil

private
counterServiceASpec : CoeffectSpec ToyKey
counterServiceASpec = MkCoeffectSpec [ServiceA]
  (UniqueCons DGamma.Section3Example.notInEmpty UniqueNil)

private
counterServiceATable :
  OwnedTable ToyKey ToyValue DGamma.CP4TotalityChecks.counterServiceASpec
counterServiceATable = MkOwnedTable DGamma.Section3Example.toyAContext sound
  where
    0 sound : (k : ToyKey) ->
      Elem k (bindingKeys (bindings DGamma.Section3Example.toyAContext)) ->
      Elem k (dependencies DGamma.CP4TotalityChecks.counterServiceASpec)
    sound ServiceA Here = Here
    sound ServiceA (There later) = void (DGamma.Section3Example.notInEmpty later)
    sound ServiceB Here impossible
    sound ServiceB (There later) =
      void (DGamma.Section3Example.notInEmpty later)

private
0 rightInjective : Right left = Right right -> left = right
rightInjective Refl = Refl

private
providerFirstRun : DepValues ToyKey ToyValue [] ->
  LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec ->
  Either Unit
    (LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec,
     LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec ->
       LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec)
providerFirstRun NoDepValues before@(MkLocalState world table) =
  Right (MkLocalState False table, \after => before)

private
0 providerFirstWitness :
  (capability : DepValues ToyKey ToyValue []) ->
  (before, after : LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec) ->
  (undo : LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec ->
    LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec) ->
  providerFirstRun capability before = Right (after, undo) ->
  undo after = before
providerFirstWitness NoDepValues before@(MkLocalState world table) after undo
  equation = case rightInjective equation of Refl => Refl

private
providerFirst : StepEffect ToyKey ToyValue Bool Unit [] DGamma.CP4TotalityChecks.counterServiceASpec
providerFirst = MkStepEffect Nothing providerFirstRun providerFirstWitness

||| The old-reading counterexample step: it installs ServiceA after the
||| uninterrupted first step (which forced world=False), but a foreign
||| interleaving that changes world=True makes the actual activation finish
||| without the declared provision.
private
providerConditionalRun : DepValues ToyKey ToyValue [] ->
  LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec ->
  Either Unit
    (LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec,
     LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec ->
       LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec)
providerConditionalRun NoDepValues before@(MkLocalState False table) =
  Right (MkLocalState False DGamma.CP4TotalityChecks.counterServiceATable, \after => before)
providerConditionalRun NoDepValues before@(MkLocalState True table) =
  Right (MkLocalState True emptyOwned, \after => before)

private
0 providerConditionalWitness :
  (capability : DepValues ToyKey ToyValue []) ->
  (before, after : LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec) ->
  (undo : LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec ->
    LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec) ->
  providerConditionalRun capability before = Right (after, undo) ->
  undo after = before
providerConditionalWitness NoDepValues before@(MkLocalState False table) after
  undo equation = case rightInjective equation of Refl => Refl
providerConditionalWitness NoDepValues before@(MkLocalState True table) after
  undo equation = case rightInjective equation of Refl => Refl

private
providerConditional :
  StepEffect ToyKey ToyValue Bool Unit [] DGamma.CP4TotalityChecks.counterServiceASpec
providerConditional = MkStepEffect Nothing providerConditionalRun
  providerConditionalWitness

public export
providerComponent : Component ToyKey ToyValue Bool Unit
providerComponent = MkComponent DGamma.CP4TotalityChecks.counterEmptySpec DGamma.CP4TotalityChecks.counterServiceASpec
  [providerFirst, providerConditional]

0 providerFirstAfter :
  (before, after : LocalState ToyKey ToyValue Bool
    DGamma.CP4TotalityChecks.counterServiceASpec) ->
  (undo : LocalState ToyKey ToyValue Bool
    DGamma.CP4TotalityChecks.counterServiceASpec ->
    LocalState ToyKey ToyValue Bool
      DGamma.CP4TotalityChecks.counterServiceASpec) ->
  providerFirstRun NoDepValues before = Right (after, undo) ->
  after = MkLocalState False (localTable before)
providerFirstAfter before@(MkLocalState world table) after undo equation =
  sym (cong fst (rightInjective equation))

||| The rejected uninterrupted CP3 Definition-69 predicate really is inhabited
||| for the counterexample provider.
public export
0 providerUninterruptedTotal :
  UninterruptedComponentTotalOnProvision
    @{DGamma.CP4TotalityChecks.counterKeyEq}
    DGamma.CP4TotalityChecks.providerComponent
providerUninterruptedTotal NoDepValues before finalState execution ServiceA Here =
  case execution of
    ProgramAdvanced DGamma.CP4TotalityChecks.providerFirst
      [DGamma.CP4TotalityChecks.providerConditional]
      _ after finalState firstUndo firstRan tail =>
        case providerFirstAfter before after firstUndo firstRan of
          Refl => case tail of
            ProgramAdvanced DGamma.CP4TotalityChecks.providerConditional [] _
              finalState finalState secondUndo secondRan ProgramFinished =>
                case cong fst (rightInjective secondRan) of Refl => Refl
providerUninterruptedTotal NoDepValues before finalState execution ServiceB
  provision = case provision of
    Here impossible
    There later => void (DGamma.Section3Example.notInEmpty later)

private
togglerRun : DepValues ToyKey ToyValue [] ->
  LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterEmptySpec ->
  Either Unit
    (LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterEmptySpec,
     LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterEmptySpec ->
       LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterEmptySpec)
togglerRun NoDepValues before@(MkLocalState world table) =
  Right (MkLocalState True table, \after => before)

private
0 togglerWitness :
  (capability : DepValues ToyKey ToyValue []) ->
  (before, after : LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterEmptySpec) ->
  (undo : LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterEmptySpec ->
    LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterEmptySpec) ->
  togglerRun capability before = Right (after, undo) ->
  undo after = before
togglerWitness NoDepValues before@(MkLocalState world table) after undo equation =
  case rightInjective equation of Refl => Refl

private
togglerStep : StepEffect ToyKey ToyValue Bool Unit [] DGamma.CP4TotalityChecks.counterEmptySpec
togglerStep = MkStepEffect Nothing togglerRun togglerWitness

private
togglerComponent : Component ToyKey ToyValue Bool Unit
togglerComponent = MkComponent DGamma.CP4TotalityChecks.counterEmptySpec DGamma.CP4TotalityChecks.counterEmptySpec [togglerStep]

private
consumerComponent : Component ToyKey ToyValue Bool Unit
consumerComponent = MkComponent DGamma.CP4TotalityChecks.counterServiceASpec DGamma.CP4TotalityChecks.counterEmptySpec []

public export
initialState : SystemState Nat ToyKey ToyValue Bool Unit
initialState = MkSystemState False emptyContext

public export
counterexampleActions : List (Action Nat ToyKey ToyValue Bool Unit)
counterexampleActions =
  [ OInsert 0 Root providerComponent
  , OInsert 1 Root togglerComponent
  , OInsert 2 Root consumerComponent
  , LBegin 0
  , LAdvance 0
  , LBegin 1
  , LAdvance 1
  , LAdvance 0
  ]

private
runCheckedActions :
  List (Action Nat ToyKey ToyValue Bool Unit) ->
  SystemState Nat ToyKey ToyValue Bool Unit ->
  Maybe (SystemState Nat ToyKey ToyValue Bool Unit)
runCheckedActions [] state = Just state
runCheckedActions (action :: rest) state = do
  (tag, afterState) <- checkedApplyAction action state
  runCheckedActions rest afterState

private
counterexampleFinal : Maybe (SystemState Nat ToyKey ToyValue Bool Unit)
counterexampleFinal = runCheckedActions counterexampleActions initialState

private
appliedPrefixLength :
  List (Action Nat ToyKey ToyValue Bool Unit) ->
  SystemState Nat ToyKey ToyValue Bool Unit -> Nat
appliedPrefixLength [] state = Z
appliedPrefixLength (action :: rest) state =
  case checkedApplyAction action state of
    Nothing => Z
    Just (tag, afterState) => S (appliedPrefixLength rest afterState)

public export
counterexampleAppliedPrefix : Nat
counterexampleAppliedPrefix = appliedPrefixLength counterexampleActions initialState

private
providerMissingServiceA :
  SystemState Nat ToyKey ToyValue Bool Unit -> Bool
providerMissingServiceA state = case lookupFiber 0 (registry state) of
  Nothing => False
  Just fiber => isActive (fiberLifecycle fiber) &&
    isNothing (lookupBinding ServiceA (ownedValues (fiberTable fiber)))

||| Executable regression for CP4 finding #4. All ten checked actions apply; the
||| endpoint is quiet and failure-free, consumer 2 is supported from P's
||| declaration but remains Inactive because the actual P table lacks ServiceA.
||| Together with `providerUninterruptedTotal`, this refutes the old premise.
public export
oldTotalityInterleavingDivergence : Bool
oldTotalityInterleavingDivergence = case counterexampleFinal of
  Nothing => False
  Just state => quiet state && noFailedFibers state &&
    providerMissingServiceA state && isSupported 2 state &&
    not (supportedActiveAt 2 state)

private
providerAlwaysRun : DepValues ToyKey ToyValue [] ->
  LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec ->
  Either Unit
    (LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec,
     LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec ->
       LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec)
providerAlwaysRun NoDepValues before@(MkLocalState world table) =
  Right (MkLocalState world DGamma.CP4TotalityChecks.counterServiceATable, \after => before)

private
0 providerAlwaysWitness :
  (capability : DepValues ToyKey ToyValue []) ->
  (before, after : LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec) ->
  (undo : LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec ->
    LocalState ToyKey ToyValue Bool DGamma.CP4TotalityChecks.counterServiceASpec) ->
  providerAlwaysRun capability before = Right (after, undo) ->
  undo after = before
providerAlwaysWitness NoDepValues before@(MkLocalState world table) after undo
  equation = case rightInjective equation of Refl => Refl

private
providerAlways : StepEffect ToyKey ToyValue Bool Unit [] DGamma.CP4TotalityChecks.counterServiceASpec
providerAlways = MkStepEffect Nothing providerAlwaysRun providerAlwaysWitness

private
alwaysComponent : Component ToyKey ToyValue Bool Unit
alwaysComponent = MkComponent DGamma.CP4TotalityChecks.counterEmptySpec DGamma.CP4TotalityChecks.counterServiceASpec
  [providerFirst, providerAlways]

public export
alwaysActions : List (Action Nat ToyKey ToyValue Bool Unit)
alwaysActions =
  [ OInsert 0 Root alwaysComponent
  , OInsert 1 Root togglerComponent
  , OInsert 2 Root consumerComponent
  , LBegin 0
  , LAdvance 0
  , LBegin 1
  , LAdvance 1
  , LAdvance 0
  , LBegin 2
  , LAdvance 2
  ]

||| Non-vacuity regression for the repaired reading: the same ambient
||| interleaving is accepted when P's actual second iteration always installs
||| ServiceA, and the consumer then reaches Active at a quiet endpoint.
public export
repairedTotalityInterleavingCheck : Bool
repairedTotalityInterleavingCheck =
  case runCheckedActions alwaysActions initialState of
    Nothing => False
    Just state => quiet state && noFailedFibers state &&
      isSupported 2 state && supportedActiveAt 2 state &&
      case lookupFiber 0 (registry state) of
        Nothing => False
        Just fiber => fiberTotalOnProvision fiber

||| The repaired Definition-69 witness is constructively produced for the
||| genuinely total provider under the same foreign ambient interleaving. The
||| runtime check above confirms this value is `Just`; its contained trace and
||| totality certificate are both indexed by the actual checked endpoints.
public export
0 repairedTraceTotalityWitness :
  Maybe (CertifiedActionTrace Nat ToyKey Bool Unit ToyValue %search
    DGamma.CP4TotalityChecks.counterKeyEq
    DGamma.CP4TotalityChecks.initialState)
repairedTraceTotalityWitness = buildCertifiedActionTrace %search counterKeyEq
  alwaysActions initialState

||| The concrete old-reading counterexample is rejected by the repaired
||| trace-indexed producer exactly at its actual provider-finish boundary.
public export
0 counterexampleTraceTotalityRejected :
  buildCertifiedActionTrace (the (DecEq Nat) %search)
    DGamma.CP4TotalityChecks.counterKeyEq
    DGamma.CP4TotalityChecks.counterexampleActions
    DGamma.CP4TotalityChecks.initialState = Nothing
counterexampleTraceTotalityRejected = Refl

public export
counterexampleDiagnostics : List Bool
counterexampleDiagnostics = case counterexampleFinal of
  Nothing => []
  Just state =>
    [ quiet state
    , noFailedFibers state
    , providerMissingServiceA state
    , isSupported 2 state
    , not (supportedActiveAt 2 state)
    ]

public export
allCP4TotalityChecks : Bool
allCP4TotalityChecks = oldTotalityInterleavingDivergence &&
  repairedTotalityInterleavingCheck
