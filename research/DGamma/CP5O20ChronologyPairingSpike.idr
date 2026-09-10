module DGamma.CP5O20ChronologyPairingSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O20GlobalActivationHistorySpike
import Prelude.Types
import Prelude.Basics
import Prelude.EqOrd
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Exact-list PERMUTATION pairing of retained native events. E8 permits
||| asynchronous pending matches, so global physical order is not equated.
||| Match steps carry the actual generation/component/activation/position law;
||| rotation steps move one occurrence, never insert/delete an unmatched event.
||| This is not a canonical ordered zip, native runtime history or A6 cut.
public export
data O20ChronologyPairing :
  {0 name, key, world, error : Type} -> {0 value : key -> Type} ->
  RegistrationGenerationBijection name ->
  List (RegistrationEvent name key world error value) ->
  List (RegistrationEvent name key world error value) -> Type where
  ChronologyPairEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {mapping : RegistrationGenerationBijection name} ->
    O20ChronologyPairing {name} {key} {world} {error} {value} mapping [] []
  ChronologyPairMatch :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {mapping : RegistrationGenerationBijection name} ->
    {left, right : List (RegistrationEvent name key world error value)} ->
    (leftEvent, rightEvent : RegistrationEvent name key world error value) ->
    (0 matched : RegistrationEventMatch mapping leftEvent rightEvent) ->
    (0 later : O20ChronologyPairing mapping left right) ->
    O20ChronologyPairing mapping (leftEvent :: left) (rightEvent :: right)
  ChronologyPairLeftRotate :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {mapping : RegistrationGenerationBijection name} ->
    {right : List (RegistrationEvent name key world error value)} ->
    (earlier : List (RegistrationEvent name key world error value)) ->
    (event : RegistrationEvent name key world error value) ->
    (suffix : List (RegistrationEvent name key world error value)) ->
    (0 later : O20ChronologyPairing mapping (event :: (earlier ++ suffix)) right) ->
    O20ChronologyPairing mapping (earlier ++ (event :: suffix)) right
  ChronologyPairRightRotate :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {mapping : RegistrationGenerationBijection name} ->
    {left : List (RegistrationEvent name key world error value)} ->
    (earlier : List (RegistrationEvent name key world error value)) ->
    (event : RegistrationEvent name key world error value) ->
    (suffix : List (RegistrationEvent name key world error value)) ->
    (0 later : O20ChronologyPairing mapping left (event :: (earlier ++ suffix))) ->
    O20ChronologyPairing mapping left (earlier ++ (event :: suffix))

||| Move the selected occurrence through the single-event rotation. Elem
||| witnesses, rather than value equality or decidable event equality, are used.
export
0 o20ChronologyRotateMember :
  {element : Type} -> {selected, event : element} -> (earlier, suffix : List element) ->
  Elem selected (event :: (earlier ++ suffix)) -> Elem selected (earlier ++ (event :: suffix))
o20ChronologyRotateMember [] suffix member = member
o20ChronologyRotateMember (head :: rest) suffix Here =
  There (o20ChronologyRotateMember rest suffix Here)
o20ChronologyRotateMember (head :: rest) suffix (There Here) = Here
o20ChronologyRotateMember (head :: rest) suffix (There (There later)) =
  There (o20ChronologyRotateMember rest suffix (There later))

||| Reverse occurrence transport observes the recursively produced Elem
||| witness. No event equality test or occurrence collapse is introduced.
export
0 o20ChronologyUnrotateMember :
  {element : Type} -> {selected, event : element} -> (earlier, suffix : List element) ->
  Elem selected (earlier ++ (event :: suffix)) -> Elem selected (event :: (earlier ++ suffix))
o20ChronologyUnrotateMember [] suffix member = member
o20ChronologyUnrotateMember (head :: rest) suffix Here = There Here
o20ChronologyUnrotateMember (head :: rest) suffix (There later) =
  beneath (o20ChronologyUnrotateMember rest suffix later)
  where
    0 beneath : {item : Type} -> {selected, event, head : item} -> {items : List item} ->
      Elem selected (event :: items) -> Elem selected (event :: (head :: items))
    beneath Here = Here
    beneath (There older) = There (There older)

||| A rotation has exactly the same number of concrete event occurrences.
export
0 o20ChronologyRotationLength :
  {element : Type} -> (earlier : List element) -> (event : element) -> (suffix : List element) ->
  length (earlier ++ (event :: suffix)) = S (length (earlier ++ suffix))
o20ChronologyRotationLength [] event suffix = Refl
o20ChronologyRotationLength (head :: rest) event suffix =
  cong S (o20ChronologyRotationLength rest event suffix)

||| Every occurrence in the EXACT left list gets a right-list occurrence and
||| the original component/generation/activation/position match certificate.
export
0 o20ChronologyLeftCovered :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {mapping : RegistrationGenerationBijection name} ->
  {left, right : List (RegistrationEvent name key world error value)} ->
  O20ChronologyPairing mapping left right ->
  (selected : RegistrationEvent name key world error value) -> Elem selected left ->
  (other : RegistrationEvent name key world error value **
    (Elem other right, RegistrationEventMatch mapping selected other))
o20ChronologyLeftCovered ChronologyPairEnd selected member = absurd member
o20ChronologyLeftCovered (ChronologyPairMatch leftEvent rightEvent matched later) _ Here =
  (rightEvent ** (Here, matched))
o20ChronologyLeftCovered (ChronologyPairMatch leftEvent rightEvent matched later) selected (There member) =
  case o20ChronologyLeftCovered later selected member of
    (other ** (present, related)) => (other ** (There present, related))
o20ChronologyLeftCovered (ChronologyPairLeftRotate earlier event suffix later) selected member =
  o20ChronologyLeftCovered later selected (o20ChronologyUnrotateMember {event} earlier suffix member)
o20ChronologyLeftCovered (ChronologyPairRightRotate earlier event suffix later) selected member =
  case o20ChronologyLeftCovered later selected member of
    (other ** (present, related)) =>
      (other ** (o20ChronologyRotateMember {event} earlier suffix present, related))

||| Bilateral coverage, still at the two literal lists. This is NOT the
||| separately blocked predecessor ALL-name-cut obligation called A6.
export
0 o20ChronologyRightCovered :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {mapping : RegistrationGenerationBijection name} ->
  {left, right : List (RegistrationEvent name key world error value)} ->
  O20ChronologyPairing mapping left right ->
  (selected : RegistrationEvent name key world error value) -> Elem selected right ->
  (other : RegistrationEvent name key world error value **
    (Elem other left, RegistrationEventMatch mapping other selected))
o20ChronologyRightCovered ChronologyPairEnd selected member = absurd member
o20ChronologyRightCovered (ChronologyPairMatch leftEvent rightEvent matched later) _ Here =
  (leftEvent ** (Here, matched))
o20ChronologyRightCovered (ChronologyPairMatch leftEvent rightEvent matched later) selected (There member) =
  case o20ChronologyRightCovered later selected member of
    (other ** (present, related)) => (other ** (There present, related))
o20ChronologyRightCovered (ChronologyPairLeftRotate earlier event suffix later) selected member =
  case o20ChronologyRightCovered later selected member of
    (other ** (present, related)) =>
      (other ** (o20ChronologyRotateMember {event} earlier suffix present, related))
o20ChronologyRightCovered (ChronologyPairRightRotate earlier event suffix later) selected member =
  o20ChronologyRightCovered later selected (o20ChronologyUnrotateMember {event} earlier suffix member)

||| Every match consumes one occurrence per side; rotations preserve count.
||| This does not equate native trace lengths or erase skipped physical edges.
export
0 o20ChronologyPairingLength :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {mapping : RegistrationGenerationBijection name} ->
  {left, right : List (RegistrationEvent name key world error value)} ->
  O20ChronologyPairing mapping left right -> length left = length right
o20ChronologyPairingLength ChronologyPairEnd = Refl
o20ChronologyPairingLength (ChronologyPairMatch leftEvent rightEvent matched later) =
  cong S (o20ChronologyPairingLength later)
o20ChronologyPairingLength (ChronologyPairLeftRotate earlier event suffix later) =
  trans (o20ChronologyRotationLength earlier event suffix) (o20ChronologyPairingLength later)
o20ChronologyPairingLength (ChronologyPairRightRotate earlier event suffix later) =
  trans (o20ChronologyPairingLength later) (sym (o20ChronologyRotationLength earlier event suffix))

||| UNCONDITIONAL producer from E8's actual asynchronous derivation. Both
||| native scans and their exact-list pairing are built in the SAME recursion.
||| Pending events are represented explicitly; every real ordinary/deleted
||| edge is kept in its source scan. No chosen lists, zip, coverage or runtime
||| endpoint cut is a premise. Global order may differ by the recorded rotations.
public export
0 o20NativeChronologiesPaired :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {mapping : RegistrationGenerationBijection name} ->
  {leftOrdinal, rightOrdinal : Nat} ->
  {leftIndex, rightIndex, leftFinalIndex, rightFinalIndex : RegistrationIndexState name} ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
  {pendingLeft, pendingRight : List (RegistrationEvent name key world error value)} ->
  RegistrationTraceCorrespondence nameEq mapping leftOrdinal leftIndex left leftFinalIndex
    rightOrdinal rightIndex right rightFinalIndex pendingLeft pendingRight ->
  (leftEvents : List (RegistrationEvent name key world error value) **
    (rightEvents : List (RegistrationEvent name key world error value) **
      (O20NativeActivationScan nameEq leftOrdinal leftIndex left leftFinalIndex leftEvents,
       O20NativeActivationScan nameEq rightOrdinal rightIndex right rightFinalIndex rightEvents,
       O20ChronologyPairing mapping (pendingLeft ++ leftEvents) (pendingRight ++ rightEvents))))
o20NativeChronologiesPaired RegistrationCorrespondenceEnd =
  ([] ** ([] ** (O20ActivationScanEnd, O20ActivationScanEnd, ChronologyPairEnd)))
o20NativeChronologiesPaired (SkipLeftNonRegistration action edge rest shape ordinary later) =
  case o20NativeChronologiesPaired later of
    (leftEvents ** (rightEvents ** (leftScan, rightScan, paired))) =>
      (leftEvents ** (rightEvents ** (O20ActivationScanOrdinary action edge rest shape ordinary leftScan, rightScan, paired)))
o20NativeChronologiesPaired (SkipRightNonRegistration action edge rest shape ordinary later) =
  case o20NativeChronologiesPaired later of
    (leftEvents ** (rightEvents ** (leftScan, rightScan, paired))) =>
      (leftEvents ** (rightEvents ** (leftScan, O20ActivationScanOrdinary action edge rest shape ordinary rightScan, paired)))
o20NativeChronologiesPaired (DiscardLeftDeletedRegistration edge rest shape deleted later) =
  case o20NativeChronologiesPaired later of
    (leftEvents ** (rightEvents ** (leftScan, rightScan, paired))) =>
      (leftEvents ** (rightEvents ** (O20ActivationScanDeleted edge rest shape deleted leftScan, rightScan, paired)))
o20NativeChronologiesPaired (DiscardRightDeletedRegistration edge rest shape deleted later) =
  case o20NativeChronologiesPaired later of
    (leftEvents ** (rightEvents ** (leftScan, rightScan, paired))) =>
      (leftEvents ** (rightEvents ** (leftScan, O20ActivationScanDeleted edge rest shape deleted rightScan, paired)))
o20NativeChronologiesPaired {nameEq} {leftOrdinal} {leftIndex} {pendingLeft}
  (QueueLeftGeneratedRegistration {child} {parent} {component} edge rest shape retained later) =
    case o20NativeChronologiesPaired later of
      (leftEvents ** (rightEvents ** (leftScan, rightScan, paired))) =>
        (registrationEventAt @{nameEq} leftOrdinal leftIndex child parent component :: leftEvents **
          (rightEvents ** (O20ActivationScanRetained edge rest shape retained leftScan, rightScan,
            ChronologyPairLeftRotate pendingLeft
              (registrationEventAt @{nameEq} leftOrdinal leftIndex child parent component) leftEvents paired)))
o20NativeChronologiesPaired {nameEq} {rightOrdinal} {rightIndex} {pendingRight}
  (QueueRightGeneratedRegistration {child} {parent} {component} edge rest shape retained later) =
    case o20NativeChronologiesPaired later of
      (leftEvents ** (rightEvents ** (leftScan, rightScan, paired))) =>
        (leftEvents **
          (registrationEventAt @{nameEq} rightOrdinal rightIndex child parent component :: rightEvents **
            (leftScan, O20ActivationScanRetained edge rest shape retained rightScan,
              ChronologyPairRightRotate pendingRight
                (registrationEventAt @{nameEq} rightOrdinal rightIndex child parent component) rightEvents paired)))
o20NativeChronologiesPaired {nameEq} {leftOrdinal} {leftIndex} {pendingLeft}
  (MatchLeftWithPendingRight {child} {parent} {component} edge rest shape retained rightPrefix rightEvent rightSuffix matched later) =
    case o20NativeChronologiesPaired later of
      (leftEvents ** (rightEvents ** (leftScan, rightScan, paired))) =>
        (registrationEventAt @{nameEq} leftOrdinal leftIndex child parent component :: leftEvents **
          (rightEvents ** (O20ActivationScanRetained edge rest shape retained leftScan, rightScan,
            rewrite sym (appendAssociative rightPrefix (rightEvent :: rightSuffix) rightEvents) in
              ChronologyPairLeftRotate pendingLeft
                (registrationEventAt @{nameEq} leftOrdinal leftIndex child parent component) leftEvents
                (ChronologyPairRightRotate rightPrefix rightEvent (rightSuffix ++ rightEvents)
                  (ChronologyPairMatch (registrationEventAt @{nameEq} leftOrdinal leftIndex child parent component)
                    rightEvent matched
                    (rewrite appendAssociative rightPrefix rightSuffix rightEvents in paired))))))
o20NativeChronologiesPaired {nameEq} {rightOrdinal} {rightIndex} {pendingRight}
  (MatchRightWithPendingLeft {child} {parent} {component} edge rest shape retained leftPrefix leftEvent leftSuffix matched later) =
    case o20NativeChronologiesPaired later of
      (leftEvents ** (rightEvents ** (leftScan, rightScan, paired))) =>
        (leftEvents **
          (registrationEventAt @{nameEq} rightOrdinal rightIndex child parent component :: rightEvents **
            (leftScan, O20ActivationScanRetained edge rest shape retained rightScan,
              rewrite sym (appendAssociative leftPrefix (leftEvent :: leftSuffix) leftEvents) in
                ChronologyPairLeftRotate leftPrefix leftEvent (leftSuffix ++ leftEvents)
                  (ChronologyPairRightRotate pendingRight
                    (registrationEventAt @{nameEq} rightOrdinal rightIndex child parent component) rightEvents
                    (ChronologyPairMatch leftEvent
                      (registrationEventAt @{nameEq} rightOrdinal rightIndex child parent component) matched
                      (rewrite appendAssociative leftPrefix leftSuffix leftEvents in paired))))))

||| Named actual-list interface. Runtime event words remain unrestricted;
||| scans and matching are erased specifications. Initial scans are literally
||| at0/empty; final indexes are the supplied correspondence's actual indexes.
public export
record O20PairedNativeChronologies
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (mapping : RegistrationGenerationBijection name)
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error}
  (left : Transitions leftFirst leftFinal) (right : Transitions rightFirst rightFinal)
  (leftIndex, rightIndex : RegistrationIndexState name) where
  constructor MkO20PairedNativeChronologies
  leftChronology : List (RegistrationEvent name key world error value)
  rightChronology : List (RegistrationEvent name key world error value)
  0 leftChronologyScan : O20NativeActivationScan nameEq Z emptyRegistrationIndex left leftIndex leftChronology
  0 rightChronologyScan : O20NativeActivationScan nameEq Z emptyRegistrationIndex right rightIndex rightChronology
  0 chronologyPairing : O20ChronologyPairing mapping leftChronology rightChronology
