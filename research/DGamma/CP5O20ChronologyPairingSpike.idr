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
