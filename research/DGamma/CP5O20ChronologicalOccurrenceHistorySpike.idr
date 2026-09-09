module DGamma.CP5O20ChronologicalOccurrenceHistorySpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5O20GlobalActivationHistorySpike
import DGamma.CP5O20InsertOccurrenceHistorySpike
import DGamma.CP5O20OccurrenceStampedHistorySpike
import DGamma.CP5O20NativeInsertEnvironmentSpike
import DGamma.CP5O20StampedOrdinalNecessitySpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Prepend the actual native edge to an authentic retained event birth.
||| Its own suffix remains literally unchanged, so the real no-Unload witness
||| survives. Arithmetic transports only the physical insertion count.
export
0 o20ChronologicalBirthPrepend :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (ordinal : Nat) -> (edge : Transition first middle) -> (rest : Transitions middle finalState) ->
  (event : RegistrationEvent name key world error value) ->
  (birth : ScannedRegistrationBirth name key world error value (S ordinal) rest event **
    SurvivingRegistration event (afterActionOccurrence (scannedLocatedBirth birth))) ->
  (birth : ScannedRegistrationBirth name key world error value ordinal (MoreTransitions edge rest) event **
    SurvivingRegistration event (afterActionOccurrence (scannedLocatedBirth birth)))
o20ChronologicalBirthPrepend name key world error value ordinal edge rest event
  (MkScannedRegistrationBirth (MkLocatedActionOccurrence before afterState earlier located later shape decomposition) stamp ** retained) =
    (MkScannedRegistrationBirth
      (MkLocatedActionOccurrence before afterState (MoreTransitions edge earlier) located later shape
        (cong (MoreTransitions edge) decomposition))
      (trans stamp (cong (MkRegistrationGeneration (eventChild event))
        (plusSuccRightSucc ordinal (transitionCount earlier)))) ** retained)

||| Every retained event in either R203 native ORIGINAL chronology yields
||| its real occurrence, exact original stamp and its OWN open parent suffix.
||| The proof follows actual ordinary/deleted/retained edges; it never zips
||| arbitrary event lists or substitutes iterator position for physical count.
export
0 o20NativeChronologicalBirth :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (ordinal : Nat) -> (index : RegistrationIndexState name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> (finalIndex : RegistrationIndexState name) ->
  (events : List (RegistrationEvent name key world error value)) ->
  O20NativeActivationScan nameEq ordinal index trace finalIndex events ->
  (event : RegistrationEvent name key world error value) -> Elem event events ->
  (birth : ScannedRegistrationBirth name key world error value ordinal trace event **
    SurvivingRegistration event (afterActionOccurrence (scannedLocatedBirth birth)))
o20NativeChronologicalBirth name key world error value nameEq ordinal
  (MkRegistrationIndexState live activations counts discarded) trace finalIndex events scan event member =
    case scan of
      O20ActivationScanEnd => absurd member
      O20ActivationScanOrdinary action edge rest shape ordinary later =>
        o20ChronologicalBirthPrepend name key world error value ordinal edge rest event
          (o20NativeChronologicalBirth name key world error value nameEq (S ordinal)
            (advanceRegistrationIndex @{nameEq} ordinal action (MkRegistrationIndexState live activations counts discarded))
            rest finalIndex events later event member)
      O20ActivationScanDeleted {child} {parent} {component} edge rest shape closed later =>
        o20ChronologicalBirthPrepend name key world error value ordinal edge rest event
          (o20NativeChronologicalBirth name key world error value nameEq (S ordinal)
            (advanceDeletedRegistrationIndex @{nameEq} ordinal child parent component (MkRegistrationIndexState live activations counts discarded))
            rest finalIndex events later event member)
      O20ActivationScanRetained {child} {parent} {component} {events = laterEvents} edge rest shape retained later =>
        case member of
          Here => (scannedRegistrationBirthHead name key world error value nameEq ordinal
            (MkRegistrationIndexState live activations counts discarded) child parent component edge rest shape ** retained)
          There remaining =>
            o20ChronologicalBirthPrepend name key world error value ordinal edge rest event
              (o20NativeChronologicalBirth name key world error value nameEq (S ordinal)
                (advanceSurvivingRegistrationIndex @{nameEq} ordinal child parent component (MkRegistrationIndexState live activations counts discarded))
                rest finalIndex laterEvents later event remaining)

||| Zip TWO actual scanned birth occurrences into a native runtime history
||| at their computed prefix environments. The accepted event match supplies
||| component/generation/position equality; raw-name images remain EXPLICIT
||| local hypotheses, never inferred for removed or vestigial original births.
export
0 o20MatchedScannedBirthOccurrenceHistory :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (mapping : RegistrationGenerationBijection name) -> (renaming : NameBijection name) ->
  AlignedTransitions name key world error value nameEq keyEq left ->
  AlignedTransitions name key world error value nameEq keyEq right ->
  (leftEvent, rightEvent : RegistrationEvent name key world error value) ->
  RegistrationEventMatch mapping leftEvent rightEvent ->
  (eventChild rightEvent = renameForward renaming (eventChild leftEvent)) ->
  (eventParent rightEvent = renameForward renaming (eventParent leftEvent)) ->
  (leftBirth : ScannedRegistrationBirth name key world error value Z left leftEvent) ->
  (rightBirth : ScannedRegistrationBirth name key world error value Z right rightEvent) ->
  O20OccurrenceStampedHistory name key world error value nameEq keyEq mapping renaming left right
    (o20ScannedFinalLive nameEq Z [] (beforeActionOccurrence (scannedLocatedBirth leftBirth)))
    (o20ScannedFinalLive nameEq Z [] (beforeActionOccurrence (scannedLocatedBirth rightBirth)))
    (putCurrentGeneration @{nameEq} (eventChild leftEvent)
      (MkRegistrationGeneration (eventChild leftEvent) (locatedActionOrdinal (scannedLocatedBirth leftBirth)))
      (o20ScannedFinalLive nameEq Z [] (beforeActionOccurrence (scannedLocatedBirth leftBirth))))
    (putCurrentGeneration @{nameEq} (renameForward renaming (eventChild leftEvent))
      (MkRegistrationGeneration (renameForward renaming (eventChild leftEvent)) (locatedActionOrdinal (scannedLocatedBirth rightBirth)))
      (o20ScannedFinalLive nameEq Z [] (beforeActionOccurrence (scannedLocatedBirth rightBirth))))
    (actionBeforeState (scannedLocatedBirth leftBirth)) (actionBeforeState (scannedLocatedBirth rightBirth))
    (actionAfterState (scannedLocatedBirth leftBirth)) (actionAfterState (scannedLocatedBirth rightBirth))
o20MatchedScannedBirthOccurrenceHistory nameEq keyEq left right mapping renaming leftAligned rightAligned
  leftEvent rightEvent matched childSame parentSame leftBirth rightBirth =
    o20LocatedInsertOccurrenceHistory nameEq keyEq renaming left right leftAligned rightAligned
      (eventChild leftEvent) (eventComponent leftEvent) (ChildOf (eventParent leftEvent))
      (ChildOf (renameForward renaming (eventParent leftEvent))) (ChildrenRelated Refl)
      (scannedLocatedBirth leftBirth)
      (MkLocatedActionOccurrence (actionBeforeState (scannedLocatedBirth rightBirth)) (actionAfterState (scannedLocatedBirth rightBirth))
        (beforeActionOccurrence (scannedLocatedBirth rightBirth)) (locatedTransition (scannedLocatedBirth rightBirth))
        (afterActionOccurrence (scannedLocatedBirth rightBirth))
        (trans (locatedAction (scannedLocatedBirth rightBirth))
          (rewrite childSame in rewrite parentSame in rewrite sym (matchedComponent matched) in Refl))
        (actionOccurrenceDecomposition (scannedLocatedBirth rightBirth)))
      (trans (cong (generationForward mapping) (sym (scannedBirthStampExact leftBirth)))
        (trans (matchedChildGeneration matched) (trans (scannedBirthStampExact rightBirth)
          (cong (\actor => MkRegistrationGeneration actor (locatedActionOrdinal (scannedLocatedBirth rightBirth))) childSame))))

||| Produce BOTH accepted ORIGINAL native chronologies and a runtime-pair
||| producer for every chosen matching retained event pair in those very lists.
||| Births, openness and prefix environments are produced, not supplied.
||| Event matching and two local raw-name equations remain explicit; there is
||| no assertion of global zip order, canonical transport or a whole history.
export
0 o20AcceptedChronologicalOccurrencePairs :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (mapping : RegistrationGenerationBijection name) -> (renaming : NameBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  AlignedTransitions name key world error value nameEq keyEq left ->
  AlignedTransitions name key world error value nameEq keyEq right ->
  (leftEvents : List (RegistrationEvent name key world error value) **
    (rightEvents : List (RegistrationEvent name key world error value) **
      (O20NativeActivationScan nameEq Z emptyRegistrationIndex left (leftFinalIndex registrations) leftEvents,
       O20NativeActivationScan nameEq Z emptyRegistrationIndex right (rightFinalIndex registrations) rightEvents,
       (leftEvent, rightEvent : RegistrationEvent name key world error value) ->
       Elem leftEvent leftEvents -> Elem rightEvent rightEvents ->
       RegistrationEventMatch mapping leftEvent rightEvent ->
       (eventChild rightEvent = renameForward renaming (eventChild leftEvent)) ->
       (eventParent rightEvent = renameForward renaming (eventParent leftEvent)) ->
       (leftBirth : ScannedRegistrationBirth name key world error value Z left leftEvent **
         (rightBirth : ScannedRegistrationBirth name key world error value Z right rightEvent **
           (SurvivingRegistration leftEvent (afterActionOccurrence (scannedLocatedBirth leftBirth)),
            SurvivingRegistration rightEvent (afterActionOccurrence (scannedLocatedBirth rightBirth)),
  O20OccurrenceStampedHistory name key world error value nameEq keyEq mapping renaming left right
    (o20ScannedFinalLive nameEq Z [] (beforeActionOccurrence (scannedLocatedBirth leftBirth)))
    (o20ScannedFinalLive nameEq Z [] (beforeActionOccurrence (scannedLocatedBirth rightBirth)))
    (putCurrentGeneration @{nameEq} (eventChild leftEvent)
      (MkRegistrationGeneration (eventChild leftEvent) (locatedActionOrdinal (scannedLocatedBirth leftBirth)))
      (o20ScannedFinalLive nameEq Z [] (beforeActionOccurrence (scannedLocatedBirth leftBirth))))
    (putCurrentGeneration @{nameEq} (renameForward renaming (eventChild leftEvent))
      (MkRegistrationGeneration (renameForward renaming (eventChild leftEvent)) (locatedActionOrdinal (scannedLocatedBirth rightBirth)))
      (o20ScannedFinalLive nameEq Z [] (beforeActionOccurrence (scannedLocatedBirth rightBirth))))
    (actionBeforeState (scannedLocatedBirth leftBirth)) (actionBeforeState (scannedLocatedBirth rightBirth))
    (actionAfterState (scannedLocatedBirth leftBirth)) (actionAfterState (scannedLocatedBirth rightBirth))))))))
o20AcceptedChronologicalOccurrencePairs {name} {key} {world} {error} {value} nameEq keyEq
  left right mapping renaming registrations leftAligned rightAligned =
    case o20AcceptedActivationHistories nameEq left right mapping registrations of
      (leftEvents ** (rightEvents ** (leftScan, rightScan, leftPositions, rightPositions, leftCounts, rightCounts))) =>
        (leftEvents ** (rightEvents ** (leftScan, rightScan,
          \leftEvent, rightEvent, leftMember, rightMember, matched, childSame, parentSame =>
            case o20NativeChronologicalBirth name key world error value nameEq Z emptyRegistrationIndex
              left (leftFinalIndex registrations) leftEvents leftScan leftEvent leftMember of
              (leftBirth ** leftOpen) =>
                case o20NativeChronologicalBirth name key world error value nameEq Z emptyRegistrationIndex
                  right (rightFinalIndex registrations) rightEvents rightScan rightEvent rightMember of
                  (rightBirth ** rightOpen) =>
                    (leftBirth ** (rightBirth ** (leftOpen, rightOpen,
                      o20MatchedScannedBirthOccurrenceHistory nameEq keyEq left right mapping renaming leftAligned rightAligned
                        leftEvent rightEvent matched childSame parentSame leftBirth rightBirth))))))
