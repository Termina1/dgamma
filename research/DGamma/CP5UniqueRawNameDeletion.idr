module DGamma.CP5UniqueRawNameDeletion

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5UniqueRawNameInsertions
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

0 uniqueMapSuccessorNotZero : (observed : Maybe Nat) -> (map S observed = Just Z) -> Void
uniqueMapSuccessorNotZero Nothing same = case same of Refl impossible
uniqueMapSuccessorNotZero (Just earlier) same = case same of Refl impossible

0 uniqueMapSuccessorJust : (observed : Maybe Nat) -> (earlier : Nat) ->
  (map S observed = Just (S earlier)) -> (observed = Just earlier)
uniqueMapSuccessorJust Nothing earlier same = case same of Refl impossible
uniqueMapSuccessorJust (Just actual) earlier same = case same of Refl => Refl

||| No survivor positions collapse under the executable retained-position map.
0 uniqueSubsequenceSourceInjective :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {nameEq : DecEq name} ->
  {deletable : Nat -> GenerationEnvironment name -> Action name key value world error -> Type} ->
  {ordinal : Nat} -> {live : GenerationEnvironment name} ->
  {sourceFirst, sourceFinal, targetFirst, targetFinal : SystemState name key value world error} ->
  {source : Transitions sourceFirst sourceFinal} -> {target : Transitions targetFirst targetFinal} ->
  (subsequence : GenerationActionSubsequence nameEq deletable ordinal live source target) ->
  (left, right, sourceIndex : Nat) ->
  (generationSubsequenceSourceOrdinal subsequence left = Just sourceIndex) ->
  (generationSubsequenceSourceOrdinal subsequence right = Just sourceIndex) -> (left = right)
uniqueSubsequenceSourceInjective name key world error value GenerationActionSubsequenceEnd left right sourceIndex leftExact rightExact =
  case leftExact of Refl impossible
uniqueSubsequenceSourceInjective name key world error value (KeepGenerationAction sh st th tt kept action tail) Z Z sourceIndex leftExact rightExact = Refl
uniqueSubsequenceSourceInjective name key world error value (KeepGenerationAction sh st th tt kept action tail) Z (S right) sourceIndex leftExact rightExact =
  case leftExact of Refl => void (uniqueMapSuccessorNotZero (generationSubsequenceSourceOrdinal tail right) rightExact)
uniqueSubsequenceSourceInjective name key world error value (KeepGenerationAction sh st th tt kept action tail) (S left) Z sourceIndex leftExact rightExact =
  case rightExact of Refl => void (uniqueMapSuccessorNotZero (generationSubsequenceSourceOrdinal tail left) leftExact)
uniqueSubsequenceSourceInjective name key world error value (KeepGenerationAction sh st th tt kept action tail) (S left) (S right) Z leftExact rightExact =
  void (uniqueMapSuccessorNotZero (generationSubsequenceSourceOrdinal tail left) leftExact)
uniqueSubsequenceSourceInjective name key world error value (KeepGenerationAction sh st th tt kept action tail) (S left) (S right) (S sourceIndex) leftExact rightExact =
  cong S (uniqueSubsequenceSourceInjective name key world error value tail left right sourceIndex
    (uniqueMapSuccessorJust (generationSubsequenceSourceOrdinal tail left) sourceIndex leftExact)
    (uniqueMapSuccessorJust (generationSubsequenceSourceOrdinal tail right) sourceIndex rightExact))
uniqueSubsequenceSourceInjective name key world error value (DeleteGenerationAction sh st deleted tail) left right Z leftExact rightExact =
  void (uniqueMapSuccessorNotZero (generationSubsequenceSourceOrdinal tail left) leftExact)
uniqueSubsequenceSourceInjective name key world error value (DeleteGenerationAction sh st deleted tail) left right (S sourceIndex) leftExact rightExact =
  uniqueSubsequenceSourceInjective name key world error value tail left right sourceIndex
    (uniqueMapSuccessorJust (generationSubsequenceSourceOrdinal tail left) sourceIndex leftExact)
    (uniqueMapSuccessorJust (generationSubsequenceSourceOrdinal tail right) sourceIndex rightExact)
