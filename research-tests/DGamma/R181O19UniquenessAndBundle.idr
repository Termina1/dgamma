module DGamma.R181O19UniquenessAndBundle

import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP3Support
import DGamma.CP4Support
import DGamma.CP4SupportSolution
import DGamma.CP4SupportQuiescence
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorEndpoint
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.Metatheory
import DGamma.Section3Example
import DGamma.R179O19ObservedExecution
import DGamma.R180O19ObservedCompletion
import DGamma.R181O19SafetyCompletion
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| F5: R173 fixture-style ownership of EVERY actual insertion position.
||| Only (ordinal0,name0) and (ordinal1,name1) occur. The actual seven-edge spine
||| is inspected; no certified Maybe-builder count or global freshness is assumed.
public export
0 r181ActualBirthPosition : (selected, ordinal : Nat) ->
  (rawInsertionNameAt Nat ToyKey ToyRuntime String ToyValue ordinal r181WholeTrace =
    Just selected) -> ordinal = selected
r181ActualBirthPosition selected Z observed = case observed of Refl => Refl
r181ActualBirthPosition selected (S Z) observed = case observed of Refl => Refl
r181ActualBirthPosition selected (S (S Z)) observed = case observed of Refl impossible
r181ActualBirthPosition selected (S (S (S Z))) observed = case observed of Refl impossible
r181ActualBirthPosition selected (S (S (S (S Z)))) observed = case observed of Refl impossible
r181ActualBirthPosition selected (S (S (S (S (S Z))))) observed = case observed of Refl impossible
r181ActualBirthPosition selected (S (S (S (S (S (S Z)))))) observed = case observed of Refl impossible
r181ActualBirthPosition selected (S (S (S (S (S (S (S later))))))) observed =
  case observed of Refl impossible

||| F6: strong original whole-trace raw uniqueness, quantified over arbitrary
||| ROOT OR GENERATED located OInsert occurrences, not just known endpoint names.
public export
0 r181OriginalUniqueInsertions : UniqueRawNameInsertions Nat ToyKey ToyRuntime String
  ToyValue (the (DecEq Nat) %search) (the (DecEq ToyKey) %search) r181WholeTrace
r181OriginalUniqueInsertions = MkUniqueRawNameInsertions
  (\selected, leftParent, rightParent, leftComponent, rightComponent, left, right =>
    trans (r181ActualBirthPosition selected (locatedActionOrdinal left)
      (rawInsertionNameAtLocated Nat ToyKey ToyRuntime String ToyValue r181WholeTrace
        selected leftParent leftComponent left))
      (sym (r181ActualBirthPosition selected (locatedActionOrdinal right)
        (rawInsertionNameAtLocated Nat ToyKey ToyRuntime String ToyValue r181WholeTrace
          selected rightParent rightComponent right))))
