module DGamma.CP5O20WholeClosingJoinSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5O20RetainedClosingIndexSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Both coordinates of a successful native subsequence lookup are inside
||| their OWN physical segment. These bounds separate the three segments.
export
0 o20SubsequenceOrdinalBounds :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {deletable : Nat -> GenerationEnvironment name -> Action name key value world error -> Type} ->
  {ordinal : Nat} -> {live : GenerationEnvironment name} ->
  {first, finalState, otherFirst, otherFinal : SystemState name key value world error} ->
  {trace : Transitions first finalState} -> {survivor : Transitions otherFirst otherFinal} ->
  (kept : GenerationActionSubsequence nameEq deletable ordinal live trace survivor) ->
  (targetIndex, sourceIndex : Nat) ->
  (generationSubsequenceSourceOrdinal kept targetIndex = Just sourceIndex) ->
  (LT targetIndex (transitionCount survivor), LT sourceIndex (transitionCount trace))
o20SubsequenceOrdinalBounds GenerationActionSubsequenceEnd targetIndex sourceIndex exact = absurd exact
o20SubsequenceOrdinalBounds (KeepGenerationAction step rest target later outside same tail) Z sourceIndex exact =
  (LTESucc LTEZero,
   replace {p = \source => LT source (S (transitionCount rest))}
     (justInjective exact) (LTESucc LTEZero))
o20SubsequenceOrdinalBounds (KeepGenerationAction step rest target later outside same tail) (S targetIndex) sourceIndex exact =
  case o20MappedSuccessorPredecessor (generationSubsequenceSourceOrdinal tail targetIndex) sourceIndex exact of
    (earlier ** (shift, origin)) =>
      case o20SubsequenceOrdinalBounds tail targetIndex earlier origin of
        (targetBound, sourceBound) =>
          (LTESucc targetBound,
           replace {p = \source => LT source (S (transitionCount rest))} (sym shift) (LTESucc sourceBound))
o20SubsequenceOrdinalBounds (DeleteGenerationAction step rest deleted tail) targetIndex sourceIndex exact =
  case o20MappedSuccessorPredecessor (generationSubsequenceSourceOrdinal tail targetIndex) sourceIndex exact of
    (earlier ** (shift, origin)) =>
      case o20SubsequenceOrdinalBounds tail targetIndex earlier origin of
        (targetBound, sourceBound) =>
          (targetBound,
           replace {p = \source => LT source (S (transitionCount rest))} (sym shift) (LTESucc sourceBound))
