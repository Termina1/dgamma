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

||| The selected actor's actually observed lifecycle edge has NO target slot
||| in its center filter. This is a native deletion classification, not a
||| preservation callback or an assumed disappearance/zero-edge equation.
export
0 o20SelectedLifecycleTargetAbsent :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  {ordinal : Nat} -> {live : GenerationEnvironment name} ->
  {first, finalState, otherFirst, otherFinal : SystemState name key value world error} ->
  {trace : Transitions first finalState} -> {survivor : Transitions otherFirst otherFinal} ->
  (kept : GenerationActionSubsequence nameEq (EpisodeGenerationDeletedActor nameEq selected registered)
    ordinal live trace survivor) ->
  (source : Nat) -> (action : Action name key value world error) ->
  (rawClosingActionAt name key world error value source trace = Just action) ->
  (actionOwner action = selected) -> (isLifecycleAction action = True) ->
  (o20SubsequenceTargetOrdinal kept source = Nothing)
o20SelectedLifecycleTargetAbsent name key world error value nameEq selected registered
  GenerationActionSubsequenceEnd source action exact owner lifecycle = absurd exact
o20SelectedLifecycleTargetAbsent name key world error value nameEq selected registered
  (KeepGenerationAction (Fired stepNameEq stepKeyEq sourceAction tag checked) rest next later outside same tail)
  Z action exact owner lifecycle =
    void (outside (DeleteEpisodeGenerationLifecycle
      (trans (cong actionOwner (justInjective exact)) owner)
      (trans (cong isLifecycleAction (justInjective exact)) lifecycle)))
o20SelectedLifecycleTargetAbsent name key world error value nameEq selected registered
  (KeepGenerationAction step rest next later outside same tail) (S source) action exact owner lifecycle =
    cong (map S) (o20SelectedLifecycleTargetAbsent name key world error value nameEq selected registered
      tail source action exact owner lifecycle)
o20SelectedLifecycleTargetAbsent name key world error value nameEq selected registered
  (DeleteGenerationAction step rest deleted tail) Z action exact owner lifecycle = Refl
o20SelectedLifecycleTargetAbsent name key world error value nameEq selected registered
  (DeleteGenerationAction step rest deleted tail) (S source) action exact owner lifecycle =
    o20SelectedLifecycleTargetAbsent name key world error value nameEq selected registered
      tail source action exact owner lifecycle

||| WHOLE before/center/after disappearance of every actually observed
||| selected-center lifecycle slot. The foreign segments cannot supply that
||| physical source coordinate, even when identical raw actions recur there.
||| This refutes a target occurrence embedding, NOT the existence of a native
||| source step (the observation and its bound witness that real source step).
export
0 o20WholeSelectedLifecycleDisappears :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, finalState : SystemState name key value world error} ->
  {trace : Transitions initial finalState} -> {selected : name} ->
  {episode : LocatedClosedEpisode name key world error value nameEq keyEq selected trace} ->
  {registered : List (RegistrationGeneration name)} -> {startOrdinal : Nat} ->
  {startLive : GenerationEnvironment name} ->
  (result : DeletionResult name key world error value nameEq keyEq trace selected episode registered startOrdinal startLive) ->
  (centerIndex : Nat) -> (action : Action name key value world error) ->
  (rawClosingActionAt name key world error value centerIndex
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode))) (closedTransitions (locatedEpisode episode))) = Just action) ->
  (actionOwner action = selected) -> (isLifecycleAction action = True) ->
  (source, target : Nat) -> (source = deletionOriginalBeforeCount result + centerIndex) ->
  Not (DeletionSurvivingOrdinalEmbedding result target source)
o20WholeSelectedLifecycleDisappears name key world error value result centerIndex action exact owner lifecycle _ _ sourceExact
  (DeletionBeforeEmbedding {survivingOrdinal} {originalOrdinal} origin) =
    succNotLTEpred (transitive (snd (o20SubsequenceOrdinalBounds (beforeDeletion result) survivingOrdinal originalOrdinal origin))
      (replace {p = LTE (deletionOriginalBeforeCount result)} (sym sourceExact)
        (lteAddRight (deletionOriginalBeforeCount result))))
o20WholeSelectedLifecycleDisappears name key world error value {nameEq} {selected} {registered}
  result centerIndex action exact owner lifecycle _ _ sourceExact
  (DeletionEpisodeEmbedding {survivingOrdinal} {originalOrdinal} origin) =
    absurd (trans (sym (trans
      (cong (o20SubsequenceTargetOrdinal (episodeDeletion result))
        (plusLeftCancel (deletionOriginalBeforeCount result) originalOrdinal centerIndex sourceExact))
      (o20SelectedLifecycleTargetAbsent name key world error value nameEq selected registered
        (episodeDeletion result) centerIndex action exact owner lifecycle)))
      (fst (o20SubsequenceOrdinalsInverse (episodeDeletion result) originalOrdinal survivingOrdinal) origin))
o20WholeSelectedLifecycleDisappears name key world error value {episode}
  result centerIndex action exact owner lifecycle _ _ sourceExact
  (DeletionAfterEmbedding {survivingOrdinal} {originalOrdinal} origin) =
    succNotLTEpred (transitive
      (replace {p = \source => LT source (deletionOriginalBeforeCount result + deletionOriginalEpisodeCount result)}
        (sym sourceExact)
        (fst (o20OffsetStrictOrder (deletionOriginalBeforeCount result) centerIndex (deletionOriginalEpisodeCount result))
          (o20ClosingIndexInsideTrace name key world error value
            (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode))) (closedTransitions (locatedEpisode episode)))
            centerIndex action exact)))
      (lteAddRight (deletionOriginalBeforeCount result + deletionOriginalEpisodeCount result)))
