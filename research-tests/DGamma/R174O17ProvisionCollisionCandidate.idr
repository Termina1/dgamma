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
