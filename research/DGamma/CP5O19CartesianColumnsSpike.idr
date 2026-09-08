module DGamma.CP5O19CartesianColumnsSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceRankObservationSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19MixedRowDispatcherSpike
import DGamma.CP5O19CartesianLengthSpike
import DGamma.CP5O19PairObservationSpike
import DGamma.CP5O19CartesianWordRowSpike
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Exact executable cut of an ACTUAL trace by its two source action words.
||| Both dependent stateful pieces, their authentic decomposition, word
||| equations and prefix count are owned by this SAME produced cut.
public export
record O19WordCut
  (name, key, world, error : Type) (value : key -> Type)
  (leftWord, rightWord : List (Action name key value world error))
  {first, last : SystemState name key value world error}
  (trace : Transitions first last) where
  constructor MkO19WordCut
  cutMiddle : SystemState name key value world error
  cutPrefix : Transitions first cutMiddle
  cutSuffix : Transitions cutMiddle last
  0 cutDecomposition : appendTransitions cutPrefix cutSuffix = trace
  0 cutLeftWord : o19ActionWord cutPrefix = leftWord
  0 cutRightWord : o19ActionWord cutSuffix = rightWord
  0 cutLeftCount : transitionCount cutPrefix = length leftWord

||| Extend an EXPLICIT produced cut by its actual observed source head.
||| All count/decomposition/word proofs see this same cut and constructor.
export
0 o19WordCutPrepend :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, last : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle last) ->
  (wanted : Action name key value world error) -> (leftWord, rightWord : List (Action name key value world error)) ->
  (transitionAction step = wanted) -> O19WordCut name key world error value leftWord rightWord rest ->
  O19WordCut name key world error value (wanted :: leftWord) rightWord (MoreTransitions step rest)
o19WordCutPrepend step rest wanted leftWord rightWord exact
  (MkO19WordCut between leading suffix decomposition leftExact rightExact count) =
    MkO19WordCut between (MoreTransitions step leading) suffix (cong (MoreTransitions step) decomposition)
      (trans (cong (\action => action :: o19ActionWord leading) exact) (cong (wanted ::) leftExact)) rightExact (cong S count)

||| Construct the ACTUAL dependent cut by the exact residual source word.
||| Both spines shrink structurally; no length-only reconstruction, guessed
||| state, cut oracle or computed-existential case is used.
export
0 o19CutByWord :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, last : SystemState name key value world error} ->
  (leftWord, rightWord : List (Action name key value world error)) ->
  (trace : Transitions first last) -> (o19ActionWord trace = leftWord ++ rightWord) ->
  O19WordCut name key world error value leftWord rightWord trace
o19CutByWord {first} [] rightWord trace exact =
  MkO19WordCut first NoTransitions trace Refl Refl exact Refl
o19CutByWord (wanted :: restWord) rightWord NoTransitions exact =
  void (uninhabited (cong length exact))
o19CutByWord (wanted :: restWord) rightWord (MoreTransitions step rest) exact =
  o19WordCutPrepend step rest wanted restWord rightWord (fst (consInjective exact))
    (o19CutByWord restWord rightWord rest (snd (consInjective exact)))

||| Structural exact action word of dependent trace concatenation.
export
0 o19ActionWordAppend :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, last : SystemState name key value world error} ->
  (left : Transitions first middle) -> (right : Transitions middle last) ->
  o19ActionWord (appendTransitions left right) = o19ActionWord left ++ o19ActionWord right
o19ActionWordAppend NoTransitions right = Refl
o19ActionWordAppend (MoreTransitions step rest) right =
  cong ((transitionAction step) ::) (o19ActionWordAppend rest right)

||| Flat two-sided SOURCE-label transport. The actual replay origin supplies
||| both action/tag/actor equations; no guard or future classification callback
||| is introduced, and observations are eliminated by their own constructors.
export
0 o19SourcePairRelabel :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (leftParent, rightParent : name) ->
  {originalLeftBefore, originalLeftAfter, originalRightBefore, originalRightAfter,
   leftBefore, leftAfter, rightBefore, rightAfter : SystemState name key value world error} ->
  (originalLeft : Transition originalLeftBefore originalLeftAfter) -> (originalRight : Transition originalRightBefore originalRightAfter) ->
  (left : Transition leftBefore leftAfter) -> (right : Transition rightBefore rightAfter) ->
  (transitionAction left = transitionAction originalLeft) -> (transitionTag left = transitionTag originalLeft) ->
  (transitionActor left = transitionActor originalLeft) ->
  (transitionAction right = transitionAction originalRight) -> (transitionTag right = transitionTag originalRight) ->
  (transitionActor right = transitionActor originalRight) ->
  O19SourcePairObservation name key world error value leftParent rightParent originalLeft originalRight ->
  O19SourcePairObservation name key world error value leftParent rightParent left right
o19SourcePairRelabel leftParent rightParent originalLeft originalRight left right leftAction leftTag leftActor rightAction rightTag rightActor
  (SourceAA leftActivation rightActivation leftOwner rightOwner) =
    SourceAA (o19PaperActivationRelabel originalLeft left leftAction leftTag leftActivation)
      (o19PaperActivationRelabel originalRight right rightAction rightTag rightActivation) (trans leftActor leftOwner) (trans rightActor rightOwner)
o19SourcePairRelabel leftParent rightParent originalLeft originalRight left right leftAction leftTag leftActor rightAction rightTag rightActor
  (SourceOA child component inserted rightActivation rightOwner childSafe) =
    SourceOA child component (trans leftAction inserted) (o19PaperActivationRelabel originalRight right rightAction rightTag rightActivation)
      (trans rightActor rightOwner) childSafe
o19SourcePairRelabel leftParent rightParent originalLeft originalRight left right leftAction leftTag leftActor rightAction rightTag rightActor
  (SourceAO child component inserted leftActivation distinct licensing) =
    SourceAO child component (trans rightAction inserted) (o19PaperActivationRelabel originalLeft left leftAction leftTag leftActivation)
      (\same => distinct (trans same leftActor))
      (\licensor, sameParent, sameActor => licensing licensor sameParent (trans (sym leftActor) sameActor))
o19SourcePairRelabel leftParent rightParent originalLeft originalRight left right leftAction leftTag leftActor rightAction rightTag rightActor
  (SourceOO leftChild rightChild leftComponent rightComponent leftInsert rightInsert distinct leftLicense rightLicense tag) =
    SourceOO leftChild rightChild leftComponent rightComponent (trans leftAction leftInsert) (trans rightAction rightInsert)
      distinct leftLicense rightLicense (trans rightTag tag)

||| Supervisor-approved INTERNAL static-class bridge. Classify only ORIGINAL
||| located occurrences in the two fixed source words, then derive current
||| source classes through the ACTUAL replay origins and preserved tags.
||| Discharging originalClasses from authoritative O19 blocks is a HARD open
||| prerequisite to any public O19 body, not an added public theorem premise.
export
0 o19OriginalPairAtReplayOrigins :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (leftParent, rightParent : name) -> (leftWord, rightWord : List (Action name key value world error)) ->
  {initial, originalFinal, currentFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) -> (current : Transitions initial currentFinal) ->
  (correspondence : ActionRegistrationReplayCorrespondence name key world error value original current) ->
  (0 originalClasses : {leftAction, rightAction : Action name key value world error} ->
    (leftOccurrence : LocatedActionOccurrence leftAction original) ->
    (rightOccurrence : LocatedActionOccurrence rightAction original) ->
    Elem leftAction leftWord -> Elem rightAction rightWord ->
    O19SourcePairObservation name key world error value leftParent rightParent
      (locatedTransition leftOccurrence) (locatedTransition rightOccurrence)) ->
  {leftAction, rightAction : Action name key value world error} ->
  (leftOccurrence : LocatedActionOccurrence leftAction current) -> (rightOccurrence : LocatedActionOccurrence rightAction current) ->
  Elem leftAction leftWord -> Elem rightAction rightWord ->
  O19SourcePairObservation name key world error value leftParent rightParent
    (locatedTransition leftOccurrence) (locatedTransition rightOccurrence)
o19OriginalPairAtReplayOrigins leftParent rightParent leftWord rightWord original current correspondence originalClasses
  leftOccurrence rightOccurrence leftIn rightIn =
    o19SourcePairRelabel leftParent rightParent
      (locatedTransition (replayActionOrigin correspondence leftOccurrence)) (locatedTransition (replayActionOrigin correspondence rightOccurrence))
      (locatedTransition leftOccurrence) (locatedTransition rightOccurrence)
      (trans (locatedAction leftOccurrence) (sym (locatedAction (replayActionOrigin correspondence leftOccurrence))))
      (sym (replayActionTagPreserved correspondence leftOccurrence))
      (trans (o19TransitionActorOwner (locatedTransition leftOccurrence))
        (trans (cong actionOwner (trans (locatedAction leftOccurrence) (sym (locatedAction (replayActionOrigin correspondence leftOccurrence)))))
          (sym (o19TransitionActorOwner (locatedTransition (replayActionOrigin correspondence leftOccurrence))))))
      (trans (locatedAction rightOccurrence) (sym (locatedAction (replayActionOrigin correspondence rightOccurrence))))
      (sym (replayActionTagPreserved correspondence rightOccurrence))
      (trans (o19TransitionActorOwner (locatedTransition rightOccurrence))
        (trans (cong actionOwner (trans (locatedAction rightOccurrence) (sym (locatedAction (replayActionOrigin correspondence rightOccurrence)))))
          (sym (o19TransitionActorOwner (locatedTransition (replayActionOrigin correspondence rightOccurrence))))))
      (originalClasses (replayActionOrigin correspondence leftOccurrence) (replayActionOrigin correspondence rightOccurrence) leftIn rightIn)
