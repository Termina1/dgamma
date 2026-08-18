module DGamma.CP4AccumulatorControlChecks

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import Data.List.Elem

%default total

ControlKey : Type
ControlKey = Nat

ControlValue : ControlKey -> Type
ControlValue _ = Unit

0 singletonFreshA : Not (Elem (the Nat 0) [])
singletonFreshA present = absurd present

0 singletonFreshB : Not (Elem (the Nat 0) [])
singletonFreshB Here impossible
singletonFreshB (There later) impossible

ControlProvision : CoeffectSpec ControlKey
ControlProvision = MkCoeffectSpec [the Nat 0]
  (UniqueCons singletonFreshA UniqueNil)

LeftControlContext : CoeffectContext ControlKey ControlValue
LeftControlContext = MkCoeffectContext [Bind (the Nat 0) ()]
  (UniqueCons singletonFreshA UniqueNil)

RightControlContext : CoeffectContext ControlKey ControlValue
RightControlContext = MkCoeffectContext [Bind (the Nat 0) ()]
  (UniqueCons singletonFreshB UniqueNil)

0 singletonOwnedSound : (key : ControlKey) ->
  Elem key [the Nat 0] -> Elem key [the Nat 0]
singletonOwnedSound key present = present

LeftControlTable : OwnedTable ControlKey ControlValue ControlProvision
LeftControlTable = MkOwnedTable
  (MkCoeffectContext [Bind (the Nat 0) ()]
    (UniqueCons singletonFreshA UniqueNil))
  singletonOwnedSound

RightControlTable : OwnedTable ControlKey ControlValue ControlProvision
RightControlTable = MkOwnedTable
  (MkCoeffectContext [Bind (the Nat 0) ()]
    (UniqueCons singletonFreshB UniqueNil))
  singletonOwnedSound

LeftControlLocal : LocalState ControlKey ControlValue Unit ControlProvision
LeftControlLocal = MkLocalState () LeftControlTable

RightControlLocal : LocalState ControlKey ControlValue Unit ControlProvision
RightControlLocal = MkLocalState () RightControlTable

LeftProofDistinctAccumulator :
  LocalState ControlKey ControlValue Unit ControlProvision ->
  LocalState ControlKey ControlValue Unit ControlProvision
LeftProofDistinctAccumulator input = LeftControlLocal

RightProofDistinctAccumulator :
  LocalState ControlKey ControlValue Unit ControlProvision ->
  LocalState ControlKey ControlValue Unit ControlProvision
RightProofDistinctAccumulator input = RightControlLocal

||| Rejected CP3 relation, retained only as a diagnostic proposition.
public export
OldExactAccumulatorRelated :
  (LocalState ControlKey ControlValue Unit ControlProvision ->
    LocalState ControlKey ControlValue Unit ControlProvision) ->
  (LocalState ControlKey ControlValue Unit ControlProvision ->
    LocalState ControlKey ControlValue Unit ControlProvision) -> Type
OldExactAccumulatorRelated left right = (input : LocalState ControlKey
  ControlValue Unit ControlProvision) -> left input = right input

||| The old layer asks for proof-bearing state equality at every input.
public export
0 oldExactAccumulatorDemandsStateEquality :
  OldExactAccumulatorRelated LeftProofDistinctAccumulator
    RightProofDistinctAccumulator ->
  (input : LocalState ControlKey ControlValue Unit ControlProvision) ->
  LeftProofDistinctAccumulator input = RightProofDistinctAccumulator input
oldExactAccumulatorDemandsStateEquality exact input = exact input

||| Finding-12 positive witness: the same two proof-distinct accumulator outputs
||| agree on every observable runtime field.
public export
0 proofDistinctAccumulatorsRuntimeRelated :
  AccumulatorRelated LeftProofDistinctAccumulator
    RightProofDistinctAccumulator
proofDistinctAccumulatorsRuntimeRelated input =
  MkLocalStateRuntimeRelated Refl Refl

ControlComponent : Component ControlKey ControlValue Unit Unit
ControlComponent = MkComponent ControlProvision ControlProvision []

ControlView : View Nat [the Nat 0]
ControlView = ProviderView 1 EmptyView

LeftControlFiber : Fiber Nat ControlKey ControlValue Unit Unit
LeftControlFiber = MkFiber ControlComponent Root False LeftControlTable
  (Active LeftProofDistinctAccumulator ControlView)

RightControlFiber : Fiber Nat ControlKey ControlValue Unit Unit
RightControlFiber = MkFiber ControlComponent Root False RightControlTable
  (Active RightProofDistinctAccumulator ControlView)

||| Non-vacuity at the public Eq-53 control layer, not merely its accumulator
||| subrelation.
public export
0 proofDistinctFiberControlsRuntimeRelated :
  FiberControlRelated LeftControlFiber RightControlFiber
proofDistinctFiberControlsRuntimeRelated =
  FibersControlRelated Root Root False False LeftControlTable RightControlTable
    (Active LeftProofDistinctAccumulator ControlView)
    (Active RightProofDistinctAccumulator ControlView)
    Refl Refl
    (ActiveControls {error = Unit}
      proofDistinctAccumulatorsRuntimeRelated Refl)

public export
proofDistinctAccumulatorRuntimeCheck : Bool
proofDistinctAccumulatorRuntimeCheck =
  length (bindings (ownedValues (localTable
    (LeftProofDistinctAccumulator LeftControlLocal)))) ==
  length (bindings (ownedValues (localTable
    (RightProofDistinctAccumulator LeftControlLocal))))
