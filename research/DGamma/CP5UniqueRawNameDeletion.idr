module DGamma.CP5UniqueRawNameDeletion

import DGamma.Calculus
import DGamma.Metatheory
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

0 uniqueSubsequenceSourceBound :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {nameEq : DecEq name} ->
  {deletable : Nat -> GenerationEnvironment name -> Action name key value world error -> Type} ->
  {ordinal : Nat} -> {live : GenerationEnvironment name} ->
  {sourceFirst, sourceFinal, targetFirst, targetFinal : SystemState name key value world error} ->
  {source : Transitions sourceFirst sourceFinal} -> {target : Transitions targetFirst targetFinal} ->
  (subsequence : GenerationActionSubsequence nameEq deletable ordinal live source target) ->
  (targetIndex, sourceIndex : Nat) ->
  (generationSubsequenceSourceOrdinal subsequence targetIndex = Just sourceIndex) ->
  (LT sourceIndex (transitionCount source))
uniqueSubsequenceSourceBound name key world error value GenerationActionSubsequenceEnd targetIndex sourceIndex exact =
  case exact of Refl impossible
uniqueSubsequenceSourceBound name key world error value (KeepGenerationAction sh st th tt kept action tail) Z sourceIndex exact =
  case exact of Refl => LTESucc LTEZero
uniqueSubsequenceSourceBound name key world error value (KeepGenerationAction sh st th tt kept action tail) (S targetIndex) Z exact =
  void (uniqueMapSuccessorNotZero (generationSubsequenceSourceOrdinal tail targetIndex) exact)
uniqueSubsequenceSourceBound name key world error value (KeepGenerationAction sh st th tt kept action tail) (S targetIndex) (S sourceIndex) exact =
  LTESucc (uniqueSubsequenceSourceBound name key world error value tail targetIndex sourceIndex
    (uniqueMapSuccessorJust (generationSubsequenceSourceOrdinal tail targetIndex) sourceIndex exact))
uniqueSubsequenceSourceBound name key world error value (DeleteGenerationAction sh st deleted tail) targetIndex Z exact =
  void (uniqueMapSuccessorNotZero (generationSubsequenceSourceOrdinal tail targetIndex) exact)
uniqueSubsequenceSourceBound name key world error value (DeleteGenerationAction sh st deleted tail) targetIndex (S sourceIndex) exact =
  LTESucc (uniqueSubsequenceSourceBound name key world error value tail targetIndex sourceIndex
    (uniqueMapSuccessorJust (generationSubsequenceSourceOrdinal tail targetIndex) sourceIndex exact))

0 uniqueBelowOffsetDistinct : (small, bound, later : Nat) ->
  (LT small bound) -> (Not (small = bound + later))
uniqueBelowOffsetDistinct small bound later below same =
  LTImpliesNotGTE below (replace {p = \actual => LTE bound actual}
    (sym same) (lteAddRight {m = later} bound))

0 uniqueShiftedBelowOffsetDistinct : (offset, small, bound, later : Nat) ->
  (LT small bound) -> (Not (offset + small = (offset + bound) + later))
uniqueShiftedBelowOffsetDistinct offset small bound later below same =
  uniqueBelowOffsetDistinct small bound later below
    (plusLeftCancel offset small (bound + later)
      (trans same (sym (plusAssociative offset bound later))))

||| All three deletion regions jointly have an injective source-position map.
0 uniqueDeletionEmbeddingInjective :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} -> {selected : name} ->
  {episode : LocatedClosedEpisode name key world error value nameEq keyEq selected original} ->
  {registered : List (RegistrationGeneration name)} ->
  {episodeStartOrdinal : Nat} -> {episodeStartLive : GenerationEnvironment name} ->
  (result : DeletionResult name key world error value nameEq keyEq original selected episode registered episodeStartOrdinal episodeStartLive) ->
  (leftTarget, rightTarget, leftSource, rightSource : Nat) ->
  DeletionSurvivingOrdinalEmbedding result leftTarget leftSource ->
  DeletionSurvivingOrdinalEmbedding result rightTarget rightSource ->
  (leftSource = rightSource) -> (leftTarget = rightTarget)
uniqueDeletionEmbeddingInjective name key world error value result _ _ _ _
  (DeletionBeforeEmbedding {survivingOrdinal = li} {originalOrdinal = ls} leftExact)
  (DeletionBeforeEmbedding {survivingOrdinal = ri} {originalOrdinal = rs} rightExact) same =
  uniqueSubsequenceSourceInjective name key world error value (beforeDeletion result) li ri ls leftExact
      (trans rightExact (cong Just (sym same)))
uniqueDeletionEmbeddingInjective name key world error value result _ _ _ _
  (DeletionBeforeEmbedding {survivingOrdinal = li} {originalOrdinal = ls} leftExact)
  (DeletionEpisodeEmbedding {survivingOrdinal = ri} {originalOrdinal = rs} rightExact) same =
  void (uniqueBelowOffsetDistinct ls (deletionOriginalBeforeCount result) rs
      (uniqueSubsequenceSourceBound name key world error value (beforeDeletion result) li ls leftExact) same)
uniqueDeletionEmbeddingInjective name key world error value result _ _ _ _
  (DeletionBeforeEmbedding {survivingOrdinal = li} {originalOrdinal = ls} leftExact)
  (DeletionAfterEmbedding {survivingOrdinal = ri} {originalOrdinal = rs} rightExact) same =
  void (uniqueBelowOffsetDistinct ls (deletionOriginalBeforeCount result) (deletionOriginalEpisodeCount result + rs)
      (uniqueSubsequenceSourceBound name key world error value (beforeDeletion result) li ls leftExact) (trans same (sym (plusAssociative (deletionOriginalBeforeCount result) (deletionOriginalEpisodeCount result) rs))))
uniqueDeletionEmbeddingInjective name key world error value result _ _ _ _
  (DeletionEpisodeEmbedding {survivingOrdinal = li} {originalOrdinal = ls} leftExact)
  (DeletionBeforeEmbedding {survivingOrdinal = ri} {originalOrdinal = rs} rightExact) same =
  void (uniqueBelowOffsetDistinct rs (deletionOriginalBeforeCount result) ls
      (uniqueSubsequenceSourceBound name key world error value (beforeDeletion result) ri rs rightExact) (sym same))
uniqueDeletionEmbeddingInjective name key world error value result _ _ _ _
  (DeletionEpisodeEmbedding {survivingOrdinal = li} {originalOrdinal = ls} leftExact)
  (DeletionEpisodeEmbedding {survivingOrdinal = ri} {originalOrdinal = rs} rightExact) same =
  cong (deletionSurvivingBeforeCount result +) (uniqueSubsequenceSourceInjective name key world error value (episodeDeletion result) li ri ls leftExact
      (trans rightExact (cong Just (sym (plusLeftCancel (deletionOriginalBeforeCount result) ls rs same)))))
uniqueDeletionEmbeddingInjective name key world error value result _ _ _ _
  (DeletionEpisodeEmbedding {survivingOrdinal = li} {originalOrdinal = ls} leftExact)
  (DeletionAfterEmbedding {survivingOrdinal = ri} {originalOrdinal = rs} rightExact) same =
  void (uniqueShiftedBelowOffsetDistinct (deletionOriginalBeforeCount result) ls
      (deletionOriginalEpisodeCount result) rs (uniqueSubsequenceSourceBound name key world error value (episodeDeletion result) li ls leftExact) same)
uniqueDeletionEmbeddingInjective name key world error value result _ _ _ _
  (DeletionAfterEmbedding {survivingOrdinal = li} {originalOrdinal = ls} leftExact)
  (DeletionBeforeEmbedding {survivingOrdinal = ri} {originalOrdinal = rs} rightExact) same =
  void (uniqueBelowOffsetDistinct rs (deletionOriginalBeforeCount result) (deletionOriginalEpisodeCount result + ls)
      (uniqueSubsequenceSourceBound name key world error value (beforeDeletion result) ri rs rightExact) (trans (sym same) (sym (plusAssociative (deletionOriginalBeforeCount result) (deletionOriginalEpisodeCount result) ls))))
uniqueDeletionEmbeddingInjective name key world error value result _ _ _ _
  (DeletionAfterEmbedding {survivingOrdinal = li} {originalOrdinal = ls} leftExact)
  (DeletionEpisodeEmbedding {survivingOrdinal = ri} {originalOrdinal = rs} rightExact) same =
  void (uniqueShiftedBelowOffsetDistinct (deletionOriginalBeforeCount result) rs
      (deletionOriginalEpisodeCount result) ls (uniqueSubsequenceSourceBound name key world error value (episodeDeletion result) ri rs rightExact) (sym same))
uniqueDeletionEmbeddingInjective name key world error value result _ _ _ _
  (DeletionAfterEmbedding {survivingOrdinal = li} {originalOrdinal = ls} leftExact)
  (DeletionAfterEmbedding {survivingOrdinal = ri} {originalOrdinal = rs} rightExact) same =
  cong ((deletionSurvivingBeforeCount result + deletionSurvivingEpisodeCount result) +) (uniqueSubsequenceSourceInjective name key world error value (afterDeletion result) li ri ls leftExact
      (trans rightExact (cong Just (sym (plusLeftCancel (deletionOriginalBeforeCount result + deletionOriginalEpisodeCount result) ls rs same)))))

0 uniqueInsertionsFromDeletionCertificate :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) -> (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq selected original) ->
  (registered : List (RegistrationGeneration name)) ->
  (episodeStartOrdinal : Nat) -> (episodeStartLive : GenerationEnvironment name) ->
  (result : DeletionResult name key world error value nameEq keyEq original selected episode registered episodeStartOrdinal episodeStartLive) ->
  DeletionOperationalOccurrenceCertificate name key world error value nameEq keyEq original selected episode registered episodeStartOrdinal episodeStartLive result ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  UniqueRawNameInsertions name key world error value nameEq keyEq (survivingTrace result)
uniqueInsertionsFromDeletionCertificate name key world error value nameEq keyEq original selected episode registered episodeStartOrdinal episodeStartLive result certificate unique =
  MkUniqueRawNameInsertions
    (\actor, leftParent, rightParent, leftComponent, rightComponent, left, right =>
      uniqueDeletionEmbeddingInjective name key world error value result
        (locatedActionOrdinal left) (locatedActionOrdinal right)
        (locatedActionOrdinal (replayActionOrigin (deletionOperationalCorrespondence certificate) left))
        (locatedActionOrdinal (replayActionOrigin (deletionOperationalCorrespondence certificate) right))
        (everySurvivingOccurrenceEmbedded certificate left) (everySurvivingOccurrenceEmbedded certificate right)
        (uniqueInsertionPosition unique actor leftParent rightParent leftComponent rightComponent
          (replayActionOrigin (deletionOperationalCorrespondence certificate) left)
          (replayActionOrigin (deletionOperationalCorrespondence certificate) right)))
