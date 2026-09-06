module DGamma.R174O17ProvisionCollisionUnique

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
import DGamma.R174O17ProvisionCollisionCandidate
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Strong whole-trace uniqueness really holds for the provision candidate.
||| Full RegistrationDiscipline/independence/closing-free O17 inputs remain open.
export
0 r174ProvisionUniqueInsertions :
  (UniqueRawNameInsertions Nat ToyKey ToyRuntime String ToyValue %search %search
    (certifiedTrace r174ProvisionExecution))
r174ProvisionUniqueInsertions = MkUniqueRawNameInsertions
  {name = Nat} {key = ToyKey} {world = ToyRuntime} {error = String} {value = ToyValue}
  {nameEq = %search} {keyEq = %search}
  {initial = MkSystemState (MkToyRuntime False False) emptyContext}
  {finalState = certifiedFinal r174ProvisionExecution}
  {trace = certifiedTrace r174ProvisionExecution}
  (\selected, leftParent, rightParent, leftComponent, rightComponent, left, right =>
    trans (r174ProvisionBirthPosition selected (locatedActionOrdinal left)
      (rawInsertionNameAtLocated Nat ToyKey ToyRuntime String ToyValue
        (certifiedTrace r174ProvisionExecution) selected leftParent leftComponent left))
      (sym (r174ProvisionBirthPosition selected (locatedActionOrdinal right)
        (rawInsertionNameAtLocated Nat ToyKey ToyRuntime String ToyValue
          (certifiedTrace r174ProvisionExecution) selected rightParent rightComponent right))))
