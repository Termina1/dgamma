module DGamma.CP5O20RootStageAttachmentSpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5SupportedBirthCoverageSpike
import DGamma.CP5RootOrchestrationTransportSpike
import DGamma.CP5UniqueRawNameInsertions
import Decidable.Equality
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20RootOrdinalBoundarySpike
import DGamma.CP5O20RootReplayLawProducerSpike
import DGamma.CP5O20CanonicalOrdinalAttachmentSpike
import Data.Nat

%default total
%unbound_implicits off

||| One actual opposite root insertion together with its physical ordinal
||| equation, relative to the explicit right scanner offset. This packet
||| does not contain a paired stage sequence or an endpoint relation.
public export
record O20RootBirthMatch
  (name, key, world, error : Type) (value : key -> Type)
  (mapping : RegistrationGenerationBijection name)
  (root : name) (component : Component key value world error)
  (leftOrdinal, rightOrdinal : Nat)
  {rightFirst, rightFinal : SystemState name key value world error}
  (right : Transitions rightFirst rightFinal) where
  constructor MkO20RootBirthMatch
  0 matchedRootBirth : LocatedActionOccurrence (OInsert root Root component) right
  0 matchedRootOrdinal :
    (generationForward mapping (MkRegistrationGeneration root leftOrdinal) =
      MkRegistrationGeneration root (rightOrdinal + locatedActionOrdinal matchedRootBirth))

||| Prepending one physical right edge shifts the occurrence count, not its
||| absolute scanner stamp. The same located birth is extended structurally.
export
0 o20RootMatchPrepend :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {mapping : RegistrationGenerationBijection name} ->
  {root : name} -> {component : Component key value world error} ->
  {leftOrdinal : Nat} -> (rightOrdinal : Nat) ->
  {rightFirst, rightMiddle, rightFinal : SystemState name key value world error} ->
  (step : Transition rightFirst rightMiddle) ->
  (rest : Transitions rightMiddle rightFinal) ->
  O20RootBirthMatch name key world error value mapping root component
    leftOrdinal (S rightOrdinal) rest ->
  O20RootBirthMatch name key world error value mapping root component
    leftOrdinal rightOrdinal (MoreTransitions step rest)
o20RootMatchPrepend {root} rightOrdinal step rest (MkO20RootBirthMatch birth exact) =
  MkO20RootBirthMatch
    (MkLocatedActionOccurrence (actionBeforeState birth) (actionAfterState birth)
      (MoreTransitions step (beforeActionOccurrence birth))
      (locatedTransition birth) (afterActionOccurrence birth) (locatedAction birth)
      (cong (MoreTransitions step) (actionOccurrenceDecomposition birth)))
    (trans exact (cong (MkRegistrationGeneration root)
      (plusSuccRightSucc rightOrdinal (locatedActionOrdinal birth))))

||| A matched external-root head supplies its own occurrence and stamp.
||| The explicit action equation transports the requested root/component.
export
0 o20RootMatchHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (mapping : RegistrationGenerationBijection name) ->
  (actual, root : name) ->
  (actualComponent, component : Component key value world error) ->
  (leftOrdinal, rightOrdinal : Nat) ->
  {rightFirst, rightMiddle, rightFinal : SystemState name key value world error} ->
  (step : Transition rightFirst rightMiddle) ->
  (rest : Transitions rightMiddle rightFinal) ->
  (transitionAction step = OInsert actual Root actualComponent) ->
  (OInsert actual Root actualComponent = OInsert root Root component) ->
  (generationForward mapping (MkRegistrationGeneration actual leftOrdinal) =
    MkRegistrationGeneration actual rightOrdinal) ->
  O20RootBirthMatch name key world error value mapping root component
    (leftOrdinal + Z) rightOrdinal (MoreTransitions step rest)
o20RootMatchHead mapping actual _ actualComponent _ leftOrdinal rightOrdinal
  step rest action Refl matched =
  MkO20RootBirthMatch
    (MkLocatedActionOccurrence _ _ NoTransitions step rest action Refl)
    (trans (cong (\ordinal => generationForward mapping
      (MkRegistrationGeneration actual ordinal)) (plusZeroRightNeutral leftOrdinal))
      (trans matched (cong (MkRegistrationGeneration actual)
        (sym (plusZeroRightNeutral rightOrdinal)))))

||| Internal Nat eliminator for a non-root left head. Its recursive argument
||| is the tail induction result, not a canonical pairing assumption.
export
0 o20RootMatchSkipLeft :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (mapping : RegistrationGenerationBijection name) ->
  (leftOrdinal, rightOrdinal : Nat) ->
  {leftFirst, leftMiddle, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (step : Transition leftFirst leftMiddle) -> (rest : Transitions leftMiddle leftFinal) ->
  (right : Transitions rightFirst rightFinal) ->
  (action : Action name key value world error) ->
  (transitionAction step = action) -> (isExternalRootBirthAction action = False) ->
  (root : name) -> (component : Component key value world error) ->
  ((position : Nat) ->
    (rawClosingActionAt name key world error value position rest = Just (OInsert root Root component)) ->
    O20RootBirthMatch name key world error value mapping root component
      ((S leftOrdinal) + position) rightOrdinal right) ->
  (position : Nat) ->
  (rawClosingActionAt name key world error value position (MoreTransitions step rest) =
    Just (OInsert root Root component)) ->
  O20RootBirthMatch name key world error value mapping root component
    (leftOrdinal + position) rightOrdinal right
o20RootMatchSkipLeft {name} {key} {world} {error} {value} mapping leftOrdinal rightOrdinal
  step rest right action exact notRoot root component recurse Z observed =
  absurd (trans (sym (cong isExternalRootBirthAction
    (trans (sym exact) (coveredHeadActionObserved name key world error value
      step rest (OInsert root Root component) observed)))) notRoot)
o20RootMatchSkipLeft {name} {key} {world} {error} {value} mapping leftOrdinal rightOrdinal
  step rest right action exact notRoot root component recurse (S position) observed =
  replace {p = \ordinal => O20RootBirthMatch name key world error value mapping
    root component ordinal rightOrdinal right}
    (plusSuccRightSucc leftOrdinal position) (recurse position observed)

||| Internal Nat eliminator at matched root heads. The head uses the stored
||| external-root equation; the tail extends the same recursive right birth.
export
0 o20RootMatchMatchedLeft :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (mapping : RegistrationGenerationBijection name) ->
  (leftOrdinal, rightOrdinal : Nat) ->
  {leftFirst, leftMiddle, leftFinal, rightFirst, rightMiddle, rightFinal : SystemState name key value world error} ->
  (leftStep : Transition leftFirst leftMiddle) -> (leftRest : Transitions leftMiddle leftFinal) ->
  (rightStep : Transition rightFirst rightMiddle) -> (rightRest : Transitions rightMiddle rightFinal) ->
  (actual : name) -> (actualComponent : Component key value world error) ->
  (transitionAction leftStep = OInsert actual Root actualComponent) ->
  (transitionAction rightStep = OInsert actual Root actualComponent) ->
  (generationForward mapping (MkRegistrationGeneration actual leftOrdinal) =
    MkRegistrationGeneration actual rightOrdinal) ->
  (root : name) -> (component : Component key value world error) ->
  ((position : Nat) ->
    (rawClosingActionAt name key world error value position leftRest = Just (OInsert root Root component)) ->
    O20RootBirthMatch name key world error value mapping root component
      ((S leftOrdinal) + position) (S rightOrdinal) rightRest) ->
  (position : Nat) ->
  (rawClosingActionAt name key world error value position (MoreTransitions leftStep leftRest) =
    Just (OInsert root Root component)) ->
  O20RootBirthMatch name key world error value mapping root component
    (leftOrdinal + position) rightOrdinal (MoreTransitions rightStep rightRest)
o20RootMatchMatchedLeft {name} {key} {world} {error} {value} mapping leftOrdinal rightOrdinal
  leftStep leftRest rightStep rightRest actual actualComponent leftExact rightExact matched
  root component recurse Z observed =
  o20RootMatchHead mapping actual root actualComponent component leftOrdinal rightOrdinal
    rightStep rightRest rightExact
    (trans (sym leftExact) (coveredHeadActionObserved name key world error value
      leftStep leftRest (OInsert root Root component) observed)) matched
o20RootMatchMatchedLeft {name} {key} {world} {error} {value} mapping leftOrdinal rightOrdinal
  leftStep leftRest rightStep rightRest actual actualComponent leftExact rightExact matched
  root component recurse (S position) observed =
  replace {p = \ordinal => O20RootBirthMatch name key world error value mapping
    root component ordinal rightOrdinal (MoreTransitions rightStep rightRest)}
    (plusSuccRightSucc leftOrdinal position)
    (o20RootMatchPrepend rightOrdinal rightStep rightRest (recurse position observed))

||| Structural recursion over the actual external-root correspondence emits
||| an opposite birth and its exact stamp simultaneously. The left action is
||| explicitly observed; no opposite occurrence or matching oracle is input.
export
0 o20RootBirthMatchObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (mapping : RegistrationGenerationBijection name) ->
  (leftOrdinal, rightOrdinal : Nat) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  ExternalRootBirthCorrespondence mapping leftOrdinal left rightOrdinal right ->
  (root : name) -> (component : Component key value world error) ->
  (position : Nat) ->
  (rawClosingActionAt name key world error value position left = Just (OInsert root Root component)) ->
  O20RootBirthMatch name key world error value mapping root component
    (leftOrdinal + position) rightOrdinal right
o20RootBirthMatchObserved mapping leftOrdinal rightOrdinal _ _
  ExternalRootBirthCorrespondenceEnd root component position observed = absurd observed
o20RootBirthMatchObserved mapping leftOrdinal rightOrdinal _ right
  (SkipLeftNonExternalRootBirth action step rest exact nonRoot later) root component position observed =
  o20RootMatchSkipLeft mapping leftOrdinal rightOrdinal step rest right action exact nonRoot root component
    (o20RootBirthMatchObserved mapping (S leftOrdinal) rightOrdinal rest right later root component)
    position observed
o20RootBirthMatchObserved mapping leftOrdinal rightOrdinal left _
  (SkipRightNonExternalRootBirth action step rest exact nonRoot later) root component position observed =
  o20RootMatchPrepend rightOrdinal step rest
    (o20RootBirthMatchObserved mapping leftOrdinal (S rightOrdinal) left rest later root component position observed)
o20RootBirthMatchObserved mapping leftOrdinal rightOrdinal _ _
  (MatchExternalRootBirth {root = actual} {component = actualComponent}
    leftStep leftRest rightStep rightRest leftExact rightExact matched later) root component position observed =
  o20RootMatchMatchedLeft mapping leftOrdinal rightOrdinal leftStep leftRest rightStep rightRest
    actual actualComponent leftExact rightExact matched root component
    (o20RootBirthMatchObserved mapping (S leftOrdinal) (S rightOrdinal) leftRest rightRest later root component)
    position observed

||| A real left root location supplies the library action observation at its
||| own ordinal. The opposite location and mapped ordinal are producer-owned.
export
0 o20RootBirthMatchLocated :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (mapping : RegistrationGenerationBijection name) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  ExternalRootBirthCorrespondence mapping Z left Z right ->
  (root : name) -> (component : Component key value world error) ->
  (birth : LocatedActionOccurrence (OInsert root Root component) left) ->
  O20RootBirthMatch name key world error value mapping root component
    (locatedActionOrdinal birth) Z right
o20RootBirthMatchLocated {name} {key} {world} {error} {value} mapping left right matching root component birth =
  o20RootBirthMatchObserved mapping Z Z left right matching root component
    (locatedActionOrdinal birth)
    (rawClosingActionAtLocated name key world error value left (OInsert root Root component) birth)

||| Same-external-inputs retains each actual root insertion as a native
||| located action, including roots absent at the endpoint. No support or
||| current raw-name bijection is used in this historical retention lemma.
export
0 o20RetainedRootBirth :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {sourceFirst, sourceFinal, targetFirst, targetFinal : SystemState name key value world error} ->
  (source : Transitions sourceFirst sourceFinal) -> (target : Transitions targetFirst targetFinal) ->
  SameExternalOrchestration nameEq source target ->
  (root : name) -> (component : Component key value world error) ->
  (birth : LocatedActionOccurrence (OInsert root Root component) source) ->
  LocatedActionOccurrence (OInsert root Root component) target
o20RetainedRootBirth {name} {key} {world} {error} {value} nameEq source target external root component birth =
  rootActionLocated name key world error value nameEq target (OInsert root Root component)
    (rootActionForward name key world error value nameEq source target external (OInsert root Root component)
      (rootActionFromLocated name key world error value nameEq source (OInsert root Root component)
        birth (RootInsertStep (locatedAction birth))))

||| A replayed root's actual opposite birth with both original-origin and
||| conjugated physical-ordinal equations. Roots keep their external names;
||| this record does not assert agreement with an endpoint-only raw map.
public export
record O20AttachedRootBirth
  (name, key, world, error : Type) (value : key -> Type)
  {leftFirst, leftFinal, rightFirst, rightFinal, leftNowFirst, leftNowFinal, rightNowFirst, rightNowFinal : SystemState name key value world error}
  {left : Transitions leftFirst leftFinal} {right : Transitions rightFirst rightFinal}
  {leftNow : Transitions leftNowFirst leftNowFinal} {rightNow : Transitions rightNowFirst rightNowFinal}
  (leftReplay : ActionRegistrationReplayCorrespondence name key world error value left leftNow)
  (rightReplay : ActionRegistrationReplayCorrespondence name key world error value right rightNow)
  (original : RegistrationGenerationBijection name)
  (root : name) (component : Component key value world error)
  (leftBirth : LocatedActionOccurrence (OInsert root Root component) leftNow) where
  constructor MkO20AttachedRootBirth
  0 attachedRootRightBirth : LocatedActionOccurrence (OInsert root Root component) rightNow
  0 attachedRootOriginalEquation :
    (generationForward original (MkRegistrationGeneration root
      (locatedActionOrdinal (replayActionOrigin leftReplay leftBirth))) =
      MkRegistrationGeneration root
        (locatedActionOrdinal (replayActionOrigin rightReplay attachedRootRightBirth)))
  0 attachedRootPhysicalEquation :
    (generationForward (o20ReplayOrdinalBijection (replayGenerationRenaming leftReplay)
      original (replayGenerationRenaming rightReplay))
      (MkRegistrationGeneration root (locatedActionOrdinal leftBirth)) =
      MkRegistrationGeneration root (locatedActionOrdinal attachedRootRightBirth))

||| Internal assembly at one retained right root. Right-original uniqueness
||| identifies its replay origin by ordinal, never by dependent state equality.
||| Both equations refer to the same explicit right replay occurrence.
export
0 o20AttachRootAtRetainedBirth :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {leftFirst, leftFinal, rightFirst, rightFinal, leftNowFirst, leftNowFinal, rightNowFirst, rightNowFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
  {leftNow : Transitions leftNowFirst leftNowFinal} -> {rightNow : Transitions rightNowFirst rightNowFinal} ->
  (leftReplay : ActionRegistrationReplayCorrespondence name key world error value left leftNow) ->
  (rightReplay : ActionRegistrationReplayCorrespondence name key world error value right rightNow) ->
  O20RootReplayOrdinals name key world error value leftReplay ->
  O20RootReplayOrdinals name key world error value rightReplay ->
  (original : RegistrationGenerationBijection name) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (root : name) -> (component : Component key value world error) ->
  (leftBirth : LocatedActionOccurrence (OInsert root Root component) leftNow) ->
  (rightOriginalBirth : LocatedActionOccurrence (OInsert root Root component) right) ->
  (generationForward original (MkRegistrationGeneration root
    (locatedActionOrdinal (replayActionOrigin leftReplay leftBirth))) =
    MkRegistrationGeneration root (locatedActionOrdinal rightOriginalBirth)) ->
  (rightBirth : LocatedActionOccurrence (OInsert root Root component) rightNow) ->
  O20AttachedRootBirth name key world error value leftReplay rightReplay original root component leftBirth
o20AttachRootAtRetainedBirth leftReplay rightReplay leftLaw rightLaw original unique
  root component leftBirth rightOriginalBirth matched rightBirth =
  MkO20AttachedRootBirth rightBirth
    (trans matched (cong (MkRegistrationGeneration root)
      (uniqueInsertionPosition unique root Root Root component component
        rightOriginalBirth (replayActionOrigin rightReplay rightBirth))))
    (o20RootOrdinalsAttached leftReplay rightReplay leftLaw rightLaw original leftBirth rightBirth
      (trans matched (cong (MkRegistrationGeneration root)
        (uniqueInsertionPosition unique root Root Root component component
          rightOriginalBirth (replayActionOrigin rightReplay rightBirth)))))

||| Eliminate the actual original root-match packet and retain that same
||| right birth through the supplied native external-input replay.
export
0 o20AttachRootMatchPacket :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal, leftNowFirst, leftNowFinal, rightNowFirst, rightNowFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} ->
  (right : Transitions rightFirst rightFinal) ->
  {leftNow : Transitions leftNowFirst leftNowFinal} ->
  (rightNow : Transitions rightNowFirst rightNowFinal) ->
  (leftReplay : ActionRegistrationReplayCorrespondence name key world error value left leftNow) ->
  (rightReplay : ActionRegistrationReplayCorrespondence name key world error value right rightNow) ->
  O20RootReplayOrdinals name key world error value leftReplay ->
  O20RootReplayOrdinals name key world error value rightReplay ->
  SameExternalOrchestration nameEq right rightNow ->
  (original : RegistrationGenerationBijection name) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (root : name) -> (component : Component key value world error) ->
  (leftBirth : LocatedActionOccurrence (OInsert root Root component) leftNow) ->
  O20RootBirthMatch name key world error value original root component
    (locatedActionOrdinal (replayActionOrigin leftReplay leftBirth)) Z right ->
  O20AttachedRootBirth name key world error value leftReplay rightReplay original root component leftBirth
o20AttachRootMatchPacket nameEq keyEq right rightNow leftReplay rightReplay leftLaw rightLaw
  external original unique root component leftBirth (MkO20RootBirthMatch rightBirth matched) =
  o20AttachRootAtRetainedBirth {nameEq} {keyEq} leftReplay rightReplay leftLaw rightLaw
    original unique root component leftBirth rightBirth matched
    (o20RetainedRootBirth nameEq right rightNow external root component rightBirth)

||| Every actual left canonical root obtains an actual right canonical root
||| and both exact ordinal equations from accepted capital. R196 C6 supplies
||| both root laws; no opposite birth, original matching or law is assumed.
export
0 o20CanonicalRootOrdinalAttachment :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (inputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq left) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq right) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (root : name) -> (component : Component key value world error) ->
  (leftBirth : LocatedActionOccurrence (OInsert root Root component)
    (canonicalTrace (canonicalSchedule leftCapital))) ->
  O20AttachedRootBirth name key world error value
    (canonicalOccurrenceCorrespondence leftCapital) (canonicalOccurrenceCorrespondence rightCapital)
    (generatedGenerationBijection inputs) root component leftBirth
o20CanonicalRootOrdinalAttachment nameEq keyEq protocol left right inputs leftCapital rightCapital unique
  root component leftBirth =
  o20AttachRootMatchPacket nameEq keyEq right (canonicalTrace (canonicalSchedule rightCapital))
    (canonicalOccurrenceCorrespondence leftCapital) (canonicalOccurrenceCorrespondence rightCapital)
    (o20CanonicalRootReplayOrdinals leftCapital) (o20CanonicalRootReplayOrdinals rightCapital)
    (sameInputs (canonicalSchedule rightCapital)) (generatedGenerationBijection inputs) unique root component leftBirth
    (o20RootBirthMatchLocated (generatedGenerationBijection inputs) left right
      (externalRootGenerationsCoupled inputs) root component
      (replayActionOrigin (canonicalOccurrenceCorrespondence leftCapital) leftBirth))
