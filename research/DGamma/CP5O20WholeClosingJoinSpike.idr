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
import Control.Relation
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

||| Exact cancellation and preservation of a common physical segment offset.
export
0 o20OffsetStrictOrder :
  (offset, left, right : Nat) ->
  (LT left right -> LT (offset + left) (offset + right),
   LT (offset + left) (offset + right) -> LT left right)
o20OffsetStrictOrder Z left right = (\ordered => ordered, \ordered => ordered)
o20OffsetStrictOrder (S offset) left right =
  case o20OffsetStrictOrder offset left right of
    (forward, backward) =>
      (\ordered => LTESucc (forward ordered), \ordered => backward (fromLteSucc ordered))

||| Reflect source order across ALL nine before/center/after combinations.
||| Both embeddings are the result's exact native subsequence equations.
||| Cross-segment target order follows from native segment bounds, never
||| from equal-action identification or an independently chosen target order.
export
0 o20WholeEmbeddingReflectsSourceOrder :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, finalState : SystemState name key value world error} ->
  {trace : Transitions initial finalState} -> {selected : name} ->
  {episode : LocatedClosedEpisode name key world error value nameEq keyEq selected trace} ->
  {registered : List (RegistrationGeneration name)} -> {startOrdinal : Nat} ->
  {startLive : GenerationEnvironment name} ->
  (result : DeletionResult name key world error value nameEq keyEq trace selected episode registered startOrdinal startLive) ->
  (leftTarget, rightTarget, leftSource, rightSource : Nat) ->
  DeletionSurvivingOrdinalEmbedding result leftTarget leftSource ->
  DeletionSurvivingOrdinalEmbedding result rightTarget rightSource ->
  LT leftSource rightSource -> LT leftTarget rightTarget
o20WholeEmbeddingReflectsSourceOrder result _ _ _ _
  (DeletionBeforeEmbedding {survivingOrdinal = lt} {originalOrdinal = ls} leftExact)
  (DeletionBeforeEmbedding {survivingOrdinal = rt} {originalOrdinal = rs} rightExact) ordered =
    o20SubsequenceReflectsSourceOrder (beforeDeletion result) lt rt ls rs leftExact rightExact ordered
o20WholeEmbeddingReflectsSourceOrder result _ _ _ _
  (DeletionBeforeEmbedding {survivingOrdinal = lt} {originalOrdinal = ls} leftExact)
  (DeletionEpisodeEmbedding {survivingOrdinal = rt} {originalOrdinal = rs} rightExact) ordered =
    transitive (fst (o20SubsequenceOrdinalBounds (beforeDeletion result) lt ls leftExact))
      (lteAddRight (deletionSurvivingBeforeCount result))
o20WholeEmbeddingReflectsSourceOrder result _ _ _ _
  (DeletionBeforeEmbedding {survivingOrdinal = lt} {originalOrdinal = ls} leftExact)
  (DeletionAfterEmbedding {survivingOrdinal = rt} {originalOrdinal = rs} rightExact) ordered =
    transitive (fst (o20SubsequenceOrdinalBounds (beforeDeletion result) lt ls leftExact))
      (transitive (lteAddRight (deletionSurvivingBeforeCount result))
        (lteAddRight (deletionSurvivingBeforeCount result + deletionSurvivingEpisodeCount result)))
o20WholeEmbeddingReflectsSourceOrder result _ _ _ _
  (DeletionEpisodeEmbedding {survivingOrdinal = lt} {originalOrdinal = ls} leftExact)
  (DeletionBeforeEmbedding {survivingOrdinal = rt} {originalOrdinal = rs} rightExact) ordered =
    void (succNotLTEpred (transitive
      (transitive ordered (lteSuccLeft (snd (o20SubsequenceOrdinalBounds (beforeDeletion result) rt rs rightExact))))
      (lteAddRight (deletionOriginalBeforeCount result))))
o20WholeEmbeddingReflectsSourceOrder result _ _ _ _
  (DeletionEpisodeEmbedding {survivingOrdinal = lt} {originalOrdinal = ls} leftExact)
  (DeletionEpisodeEmbedding {survivingOrdinal = rt} {originalOrdinal = rs} rightExact) ordered =
    fst (o20OffsetStrictOrder (deletionSurvivingBeforeCount result) lt rt)
      (o20SubsequenceReflectsSourceOrder (episodeDeletion result) lt rt ls rs leftExact rightExact
        (snd (o20OffsetStrictOrder (deletionOriginalBeforeCount result) ls rs) ordered))
o20WholeEmbeddingReflectsSourceOrder result _ _ _ _
  (DeletionEpisodeEmbedding {survivingOrdinal = lt} {originalOrdinal = ls} leftExact)
  (DeletionAfterEmbedding {survivingOrdinal = rt} {originalOrdinal = rs} rightExact) ordered =
    transitive (fst (o20OffsetStrictOrder (deletionSurvivingBeforeCount result) lt (deletionSurvivingEpisodeCount result))
      (fst (o20SubsequenceOrdinalBounds (episodeDeletion result) lt ls leftExact)))
      (lteAddRight (deletionSurvivingBeforeCount result + deletionSurvivingEpisodeCount result))
o20WholeEmbeddingReflectsSourceOrder result _ _ _ _
  (DeletionAfterEmbedding {survivingOrdinal = lt} {originalOrdinal = ls} leftExact)
  (DeletionBeforeEmbedding {survivingOrdinal = rt} {originalOrdinal = rs} rightExact) ordered =
    void (succNotLTEpred (transitive
      (transitive ordered (lteSuccLeft (snd (o20SubsequenceOrdinalBounds (beforeDeletion result) rt rs rightExact))))
      (transitive (lteAddRight (deletionOriginalBeforeCount result))
        (lteAddRight (deletionOriginalBeforeCount result + deletionOriginalEpisodeCount result)))))
o20WholeEmbeddingReflectsSourceOrder result _ _ _ _
  (DeletionAfterEmbedding {survivingOrdinal = lt} {originalOrdinal = ls} leftExact)
  (DeletionEpisodeEmbedding {survivingOrdinal = rt} {originalOrdinal = rs} rightExact) ordered =
    void (succNotLTEpred (transitive
      (transitive ordered (lteSuccLeft
        (fst (o20OffsetStrictOrder (deletionOriginalBeforeCount result) rs (deletionOriginalEpisodeCount result))
          (snd (o20SubsequenceOrdinalBounds (episodeDeletion result) rt rs rightExact)))))
      (lteAddRight (deletionOriginalBeforeCount result + deletionOriginalEpisodeCount result))))
o20WholeEmbeddingReflectsSourceOrder result _ _ _ _
  (DeletionAfterEmbedding {survivingOrdinal = lt} {originalOrdinal = ls} leftExact)
  (DeletionAfterEmbedding {survivingOrdinal = rt} {originalOrdinal = rs} rightExact) ordered =
    fst (o20OffsetStrictOrder ((deletionSurvivingBeforeCount result + deletionSurvivingEpisodeCount result)) lt rt)
      (o20SubsequenceReflectsSourceOrder (afterDeletion result) lt rt ls rs leftExact rightExact
        (snd (o20OffsetStrictOrder ((deletionOriginalBeforeCount result + deletionOriginalEpisodeCount result)) ls rs) ordered))
