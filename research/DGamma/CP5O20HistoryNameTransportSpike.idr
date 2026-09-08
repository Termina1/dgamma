module DGamma.CP5O20HistoryNameTransportSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| History-indexed target name. Unlike the current endpoint bijection, this
||| computation retains the insertion ordinal, including a removed generation.
public export
o20HistoricalTarget :
  {name : Type} -> RegistrationGenerationBijection name ->
  RegistrationGeneration name -> name
o20HistoricalTarget mapping generation = generationName (generationForward mapping generation)

||| Two actual historical insertions coupled by the accepted generation map.
||| Current raw-name equality and endpoint presence are deliberately absent:
||| removed generations retain their authentic birth stamps and locations.
public export
record O20HistoryBirthPair
  (name, key, world, error : Type) (value : key -> Type)
  (mapping : RegistrationGenerationBijection name)
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error}
  (left : Transitions leftFirst leftFinal) (right : Transitions rightFirst rightFinal)
  (leftName, rightName : name) where
  constructor MkO20HistoryBirthPair
  historyLeftStamp : RegistrationGeneration name
  historyRightStamp : RegistrationGeneration name
  0 historyLeftBirth : CurrentGenerationBirth name key world error value left leftName historyLeftStamp
  0 historyRightBirth : CurrentGenerationBirth name key world error value right rightName historyRightStamp
  0 historyStampsMatched : (generationForward mapping historyLeftStamp = historyRightStamp)

||| The history-indexed computation selects the actual opposite birth name.
||| This equation uses authentic insertion stamps, not current presence.
export
0 o20HistoryTargetOwned :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {mapping : RegistrationGenerationBijection name} ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
  {leftName, rightName : name} ->
  (paired : O20HistoryBirthPair name key world error value mapping left right leftName rightName) ->
  (o20HistoricalTarget mapping (historyLeftStamp paired) = rightName)
o20HistoryTargetOwned paired =
  trans (cong generationName (historyStampsMatched paired))
    (cong generationName (currentBirthStampExact (historyRightBirth paired)))

||| Current lookup observations yield both actual historical births through
||| the accepted scanners. Only the observed generation match is used here.
export
0 o20HistoryCurrentPair :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  (leftName, rightName : name) -> (leftStamp, rightStamp : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} leftName (leftFinalGenerations registrations) = Just leftStamp) ->
  (lookupCurrentGeneration @{nameEq} rightName (rightFinalGenerations registrations) = Just rightStamp) ->
  (generationForward mapping leftStamp = rightStamp) ->
  O20HistoryBirthPair name key world error value mapping left right leftName rightName
o20HistoryCurrentPair {name} {key} {world} {error} {value} nameEq left right mapping registrations
  leftName rightName leftStamp rightStamp leftCurrent rightCurrent matched =
    MkO20HistoryBirthPair leftStamp rightStamp
      (acceptedLeftCurrentBirth name key world error value nameEq left right mapping registrations leftName leftStamp leftCurrent)
      (acceptedRightCurrentBirth name key world error value nameEq left right mapping registrations rightName rightStamp rightCurrent) matched

||| Eliminate only the observed successful current-generation packet. The
||| actual birth witnesses are extracted by A4, never supplied by the caller.
export
0 o20HistoryCurrentPacket :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  (leftName, rightName : name) -> (leftStamp : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} leftName (leftFinalGenerations registrations) = Just leftStamp) ->
  (rightStamp : RegistrationGeneration name **
    ((generationForward mapping leftStamp = rightStamp),
     (lookupCurrentGeneration @{nameEq} rightName (rightFinalGenerations registrations) = Just rightStamp))) ->
  O20HistoryBirthPair name key world error value mapping left right leftName rightName
o20HistoryCurrentPacket nameEq left right mapping registrations leftName rightName leftStamp leftCurrent
  (rightStamp ** (matched, rightCurrent)) =
    o20HistoryCurrentPair nameEq left right mapping registrations leftName rightName leftStamp rightStamp leftCurrent rightCurrent matched

||| The supported-side success packet pins the history-indexed target to the
||| supplied current raw image. The accepted right scanner owns its name.
export
0 o20HistoryEndpointPacketAgrees :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  (rightName : name) -> (leftStamp : RegistrationGeneration name) ->
  (rightStamp : RegistrationGeneration name **
    ((generationForward mapping leftStamp = rightStamp),
     (lookupCurrentGeneration @{nameEq} rightName (rightFinalGenerations registrations) = Just rightStamp))) ->
  (o20HistoricalTarget mapping leftStamp = rightName)
o20HistoryEndpointPacketAgrees {name} {key} {world} {error} {value} nameEq left right mapping registrations
  rightName leftStamp (rightStamp ** (matched, rightCurrent)) =
    trans (cong generationName matched)
      (cong generationName (currentBirthStampExact
        (acceptedRightCurrentBirth name key world error value nameEq left right mapping registrations rightName rightStamp rightCurrent)))
