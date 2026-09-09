module DGamma.CP5O20NativeDisappearanceSkipSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5O20WholeClosingJoinSpike
import DGamma.CP5O20RetainedClosingIndexSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Control.Relation
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Executable SOURCE-to-survivor physical position map for the actual native
||| filtering derivation. A deleted head consumes one SOURCE edge and no
||| target edge. Nothing denotes a removed or out-of-range source slot; it is
||| never an assertion that the source step is a zero-length native path.
public export
o20SubsequenceTargetOrdinal :
  {0 name, key, world, error : Type} -> {0 value : key -> Type} ->
  {0 nameEq : DecEq name} ->
  {0 deletable : Nat -> GenerationEnvironment name -> Action name key value world error -> Type} ->
  {0 ordinal : Nat} -> {0 live : GenerationEnvironment name} ->
  {0 first, finalState, otherFirst, otherFinal : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} -> {0 survivor : Transitions otherFirst otherFinal} ->
  GenerationActionSubsequence nameEq deletable ordinal live trace survivor -> Nat -> Maybe Nat
o20SubsequenceTargetOrdinal GenerationActionSubsequenceEnd source = Nothing
o20SubsequenceTargetOrdinal (KeepGenerationAction step rest target later outside same tail) Z = Just Z
o20SubsequenceTargetOrdinal (KeepGenerationAction step rest target later outside same tail) (S source) =
  map S (o20SubsequenceTargetOrdinal tail source)
o20SubsequenceTargetOrdinal (DeleteGenerationAction step rest deleted tail) Z = Nothing
o20SubsequenceTargetOrdinal (DeleteGenerationAction step rest deleted tail) (S source) =
  o20SubsequenceTargetOrdinal tail source

||| Both partial inverses are proved over the actual keep/delete derivation.
||| Successful target lookup is EXACTLY the existing source embedding law.
||| Thus Nothing can certify a physical disappearance, not an arbitrary skip.
export
0 o20SubsequenceOrdinalsInverse :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {deletable : Nat -> GenerationEnvironment name -> Action name key value world error -> Type} ->
  {ordinal : Nat} -> {live : GenerationEnvironment name} ->
  {first, finalState, otherFirst, otherFinal : SystemState name key value world error} ->
  {trace : Transitions first finalState} -> {survivor : Transitions otherFirst otherFinal} ->
  (kept : GenerationActionSubsequence nameEq deletable ordinal live trace survivor) ->
  (source, target : Nat) ->
  ((generationSubsequenceSourceOrdinal kept target = Just source -> o20SubsequenceTargetOrdinal kept source = Just target),
   (o20SubsequenceTargetOrdinal kept source = Just target -> generationSubsequenceSourceOrdinal kept target = Just source))
o20SubsequenceOrdinalsInverse GenerationActionSubsequenceEnd source target = (absurd, absurd)
o20SubsequenceOrdinalsInverse (KeepGenerationAction step rest next later outside same tail) Z Z =
  (\exact => Refl, \exact => Refl)
o20SubsequenceOrdinalsInverse (KeepGenerationAction step rest next later outside same tail) Z (S target) =
  (\exact => case o20MappedSuccessorPredecessor (generationSubsequenceSourceOrdinal tail target) Z exact of
    (earlier ** (shift, origin)) => absurd shift,
   \exact => absurd (justInjective exact))
o20SubsequenceOrdinalsInverse (KeepGenerationAction step rest next later outside same tail) (S source) Z =
  (\exact => absurd (justInjective exact),
   \exact => case o20MappedSuccessorPredecessor (o20SubsequenceTargetOrdinal tail source) Z exact of
     (earlier ** (shift, origin)) => absurd shift)
o20SubsequenceOrdinalsInverse (KeepGenerationAction step rest next later outside same tail) (S source) (S target) =
  (\exact => case o20MappedSuccessorPredecessor (generationSubsequenceSourceOrdinal tail target) (S source) exact of
     (earlier ** (shift, origin)) => cong (map S)
       (fst (o20SubsequenceOrdinalsInverse tail source target)
         (trans origin (cong Just (sym (injective shift))))),
   \exact => case o20MappedSuccessorPredecessor (o20SubsequenceTargetOrdinal tail source) (S target) exact of
     (earlier ** (shift, origin)) => cong (map S)
       (snd (o20SubsequenceOrdinalsInverse tail source target)
         (trans origin (cong Just (sym (injective shift))))))
o20SubsequenceOrdinalsInverse (DeleteGenerationAction step rest deleted tail) Z target =
  (\exact => case o20MappedSuccessorPredecessor (generationSubsequenceSourceOrdinal tail target) Z exact of
     (earlier ** (shift, origin)) => absurd shift,
   absurd)
o20SubsequenceOrdinalsInverse (DeleteGenerationAction step rest deleted tail) (S source) target =
  (\exact => case o20MappedSuccessorPredecessor (generationSubsequenceSourceOrdinal tail target) (S source) exact of
     (earlier ** (shift, origin)) => fst (o20SubsequenceOrdinalsInverse tail source target)
       (trans origin (cong Just (sym (injective shift)))),
   \exact => cong (map S) (snd (o20SubsequenceOrdinalsInverse tail source target) exact))
