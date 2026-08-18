module DGamma.CP4RuntimeBindingsChecks

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP4RuntimeBindings
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

ProofName : Type
ProofName = Nat

ProofKey : Type
ProofKey = Nat

ProofValue : ProofKey -> Type
ProofValue _ = Nat

proofNameEq : DecEq ProofName
proofNameEq = %search

proofKeyEq : DecEq ProofKey
proofKeyEq = %search

proofComponent : Component ProofKey ProofValue Nat Nat
proofComponent = MkComponent emptySpec emptySpec []

proofFiber : Fiber ProofName ProofKey ProofValue Nat Nat
proofFiber = freshFiber proofComponent Root

proofEntries : List
  (Binding ProofName (FiberAt ProofName ProofKey ProofValue Nat Nat))
proofEntries = [Bind 0 proofFiber]

0 noSingletonTailLeft : Not (Elem (the ProofName 0) [])
noSingletonTailLeft present impossible

0 emptyTailImpossible : Elem (the ProofName 0) [] -> Void
emptyTailImpossible present impossible

||| A deliberately separately-defined proof term.  The two certificates have
||| the same proposition but are not identified by any proof-irrelevance axiom.
0 noSingletonTailRight : Not (Elem (the ProofName 0) [])
noSingletonTailRight present = void (emptyTailImpossible present)

0 leftSingletonUnique : UniqueKeys [the ProofName 0]
leftSingletonUnique = UniqueCons noSingletonTailLeft UniqueNil

0 rightSingletonUnique : UniqueKeys [the ProofName 0]
rightSingletonUnique = UniqueCons noSingletonTailRight UniqueNil

leftProofContext : Registry ProofName ProofKey ProofValue Nat Nat
leftProofContext = MkCoeffectContext proofEntries leftSingletonUnique

rightProofContext : Registry ProofName ProofKey ProofValue Nat Nat
rightProofContext = MkCoeffectContext proofEntries rightSingletonUnique

leftProofState : SystemState ProofName ProofKey ProofValue Nat Nat
leftProofState = MkSystemState 7 leftProofContext

rightProofState : SystemState ProofName ProofKey ProofValue Nat Nat
rightProofState = MkSystemState 7 rightProofContext

||| Pinned rationale for runtime-snapshot replay: exact ordered bindings and
||| ambient state coincide even though the intrinsic uniqueness certificates
||| are separately defined proof terms.
public export
0 proofDistinctRuntimeSnapshot :
  runtimeSnapshot leftProofState = runtimeSnapshot rightProofState
proofDistinctRuntimeSnapshot = Refl

public export
0 proofDistinctRetireObservation :
  observeActionResult
    (applyAction @{proofNameEq} @{proofKeyEq} (ORetire 0) leftProofState) =
  observeActionResult
    (applyAction @{proofNameEq} @{proofKeyEq} (ORetire 0) rightProofState)
proofDistinctRetireObservation = applyActionObservationCoherent proofNameEq
  proofKeyEq
  (ORetire 0) leftProofState rightProofState proofDistinctRuntimeSnapshot

0 leftRetireRaw :
  applyAction @{proofNameEq} @{proofKeyEq} (ORetire 0) leftProofState =
  Just (ORetireTag,
    MkSystemState 7
      (replaceBinding @{proofNameEq} 0 (retireFiber proofFiber)
        leftProofContext))
leftRetireRaw = Refl

||| The keystone transport returns a real evaluator step, not only an equality
||| between projected observations.
public export
0 proofDistinctRetireTransport :
  ActionRuntimeTransport ProofName ProofKey Nat Nat ProofValue proofNameEq
    proofKeyEq
    (ORetire 0) rightProofState ORetireTag
    (MkSystemState 7
      (replaceBinding @{proofNameEq} 0 (retireFiber proofFiber)
        leftProofContext))
proofDistinctRetireTransport = transportApplyActionAcrossRuntimeSnapshot
  proofNameEq proofKeyEq (ORetire 0) leftProofState rightProofState proofDistinctRuntimeSnapshot
  ORetireTag
  (MkSystemState 7
    (replaceBinding @{proofNameEq} 0 (retireFiber proofFiber)
      leftProofContext))
  leftRetireRaw
