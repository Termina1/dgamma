module DGamma.R174O17ProvisionProtocol

import DGamma.Core
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Section3Example
import DGamma.Unified
import Data.Bool
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| A genuine provider program is the only yielded catalog component.
public export
r174ProvisionCatalog : Nat -> Maybe (Component ToyKey ToyValue ToyRuntime String)
r174ProvisionCatalog Z = Just providerComponent
r174ProvisionCatalog (S tag) = Nothing

||| Admit only dependency-free components. Tag-free programs have rank 1;
||| programs with a yield tag have rank 0, so our installing child outranks its
||| yielding parent. No equality comparison of effect functions is needed.
public export
r174ProvisionRank : Component ToyKey ToyValue ToyRuntime String -> Maybe Nat
r174ProvisionRank (MkComponent (MkCoeffectSpec [] unique) provision program) =
  if allRecursive (\step => isNothing (registrationYieldTag step)) program
    then Just 1 else Just 0
r174ProvisionRank (MkComponent (MkCoeffectSpec (key :: rest) unique) provision program) = Nothing

0 r174AllRecursiveContainsFalse :
  (item : Type) -> (predicate : item -> Bool) ->
  (selected : item) -> (items : List item) ->
  Elem selected items -> predicate selected = False ->
  allRecursive predicate items = False
r174AllRecursiveContainsFalse item predicate selected [] present false = case present of Here impossible; There later impossible
r174AllRecursiveContainsFalse item predicate _ (head :: rest) Here false = rewrite false in Refl
r174AllRecursiveContainsFalse item predicate selected (head :: rest) (There later) false =
  rewrite r174AllRecursiveContainsFalse item predicate selected rest later false in
    andFalseFalse (predicate head)

0 r174ProvisionYieldRanks :
  (parent, child : Component ToyKey ToyValue ToyRuntime String) ->
  (step : StepEffect ToyKey ToyValue ToyRuntime String
    (dependencies (componentDependencies parent)) (componentProvisions parent)) ->
  (tag, parentRank, childRank : Nat) ->
  Elem step (componentProgram parent) ->
  r174ProvisionRank parent = Just parentRank ->
  r174ProvisionRank child = Just childRank ->
  registrationYieldTag step = Just tag ->
  r174ProvisionCatalog tag = Just child -> LT parentRank childRank
r174ProvisionYieldRanks (MkComponent (MkCoeffectSpec [] unique) provision program)
  child step Z parentRank childRank present parentRanked childRanked tagged cataloged =
    case cataloged of
      Refl => case trans
        (sym (cong (\free => the (Maybe Nat) (if free then Just 1 else Just 0))
          (r174AllRecursiveContainsFalse
            (StepEffect ToyKey ToyValue ToyRuntime String [] provision)
            (\source => isNothing (registrationYieldTag source)) step program present
            (cong isNothing tagged)))) parentRanked of
          Refl => case childRanked of Refl => LTESucc LTEZero
r174ProvisionYieldRanks (MkComponent (MkCoeffectSpec [] unique) provision program)
  child step (S tag) parentRank childRank present parentRanked childRanked tagged cataloged =
    case cataloged of Refl impossible
r174ProvisionYieldRanks (MkComponent (MkCoeffectSpec (key :: rest) unique) provision program)
  child step tag parentRank childRank present parentRanked childRanked tagged cataloged =
    case parentRanked of Refl impossible

||| Unlike the historical empty-key fixture, keys exist and providers declare
||| K. It is the admitted CONSUMER dependency list, not the key type, that is empty.
0 r174ProvisionPrecedenceRanks :
  (provider, consumer : Component ToyKey ToyValue ToyRuntime String) ->
  (providerRank, consumerRank : Nat) ->
  r174ProvisionRank provider = Just providerRank ->
  r174ProvisionRank consumer = Just consumerRank ->
  (key : ToyKey) -> Elem key (dependencies (componentProvisions provider)) ->
  Elem key (dependencies (componentDependencies consumer)) ->
  LT providerRank consumerRank
r174ProvisionPrecedenceRanks provider
  (MkComponent (MkCoeffectSpec [] unique) provision program)
  providerRank consumerRank providerRanked consumerRanked key provides depends =
    case depends of Here impossible; There later impossible
r174ProvisionPrecedenceRanks provider
  (MkComponent (MkCoeffectSpec (head :: rest) unique) provision program)
  providerRank consumerRank providerRanked consumerRanked key provides depends =
    case consumerRanked of Refl impossible
