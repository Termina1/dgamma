module DGamma.R174O17ProvisionCollisionCandidate

import DGamma.Core
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4SupportQuiescence
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.Metatheory
import DGamma.Section3Example
import DGamma.Unified
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| The parent has no provision; its tagged iterator can license a child.
||| This does not by itself construct a RegistrationProtocol/Discipline.
public export
r174ProvisionParentStep : StepEffect ToyKey ToyValue ToyRuntime String [] DGamma.CalculusChecks.toyEmptySpec
r174ProvisionParentStep = MkStepEffect (Just 0)
  (\NoDepValues, before => Right (before, Prelude.id))
  (\NoDepValues, before, after, undo, returned, canonical =>
    replace {p = \outcome => case outcome of
      Left _ => Unit
      Right (next, inverse) => inverse (normalizeLocal DGamma.CalculusChecks.toyEmptySpec next) = before}
      returned canonical)

public export
r174ProvisionParent : Component ToyKey ToyValue ToyRuntime String
r174ProvisionParent = MkComponent DGamma.CalculusChecks.toyEmptySpec
  DGamma.CalculusChecks.toyEmptySpec [r174ProvisionParentStep]

||| Execute all eight ACTUAL checked actions, certifying transition totality
||| simultaneously. Names 1 and 2 use the genuine installing provider program.
||| The next count equation must exclude this empty fallback before any claim
||| of input inhabitation. The production builder is proof-erased.
public export
0 r174ProvisionExecution : CertifiedActionTrace Nat ToyKey ToyRuntime String ToyValue %search %search
  (MkSystemState (MkToyRuntime False False) emptyContext)
r174ProvisionExecution = fromMaybe
  (MkCertifiedActionTrace (MkSystemState (MkToyRuntime False False) emptyContext)
    NoTransitions TraceComponentsTotalEnd)
  (buildCertifiedActionTrace %search %search
    [OInsert 0 Root r174ProvisionParent, LBegin 0,
     OInsert 1 (ChildOf 0) providerComponent, ORetire 1, ORemove 1,
     OInsert 2 Root providerComponent, ORetire 2, LAdvance 0]
    (MkSystemState (MkToyRuntime False False) emptyContext))
