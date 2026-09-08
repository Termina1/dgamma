module DGamma.CP5O20HistoryNameTransportSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O20AllNameSynchronizationSpike
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

||| Eliminate the observed endpoint choice. Supported names cannot take the
||| full vestigial branch; the success branch authenticates its current image.
export
0 o20HistorySupportedChoice :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  (current : CurrentEndpointRenaming nameEq keyEq mapping left right registrations) ->
  (selected : name) -> (leftStamp : RegistrationGeneration name) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} selected leftFinal = True) ->
  Either
    (VestigialEndpointGeneration name key world error value nameEq keyEq
      (leftFinalGenerations registrations) (leftDeletedGenerations registrations) selected leftFinal)
    (rightStamp : RegistrationGeneration name **
      ((generationForward mapping leftStamp = rightStamp),
       (lookupCurrentGeneration @{nameEq} (renameForward (currentNameBijection current) selected)
         (rightFinalGenerations registrations) = Just rightStamp))) ->
  (o20HistoricalTarget mapping leftStamp = renameForward (currentNameBijection current) selected)
o20HistorySupportedChoice nameEq keyEq left right mapping registrations current selected leftStamp supported (Left vestigial) =
  absurd (trans (sym supported) (vestigialUnsupported vestigial))
o20HistorySupportedChoice nameEq keyEq left right mapping registrations current selected leftStamp supported (Right matched) =
  o20HistoryEndpointPacketAgrees nameEq left right mapping registrations
    (renameForward (currentNameBijection current) selected) leftStamp matched

||| Endpoint agreement for every supported current generation. The current
||| coupling choice is obtained from the supplied accepted endpoint record;
||| no raw-name equation or opposite birth is an input. Mere presence alone
||| would not exclude the full vestigial alternative.
export
0 o20HistorySupportedEndpoint :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  (current : CurrentEndpointRenaming nameEq keyEq mapping left right registrations) ->
  (selected : name) -> (leftStamp : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} selected (leftFinalGenerations registrations) = Just leftStamp) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} selected leftFinal = True) ->
  (o20HistoricalTarget mapping leftStamp = renameForward (currentNameBijection current) selected)
o20HistorySupportedEndpoint nameEq keyEq left right mapping registrations current selected leftStamp found supported =
  o20HistorySupportedChoice nameEq keyEq left right mapping registrations current selected leftStamp supported
    (leftCurrentGenerationMapped current selected leftStamp found)

||| Internal physical cut indexed by the LIVE generation environments. Its
||| all-name runtime bijection is internal, NOT the supplied endpoint map.
||| Live births authenticate its action on names; absent historical births
||| remain in O20HistoryBirthPair rather than constraining the current map.
||| This is an invariant specification, not arbitrary-trace extraction.
public export
record O20HistoryCut
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (mapping : RegistrationGenerationBijection name)
  (leftLive, rightLive : GenerationEnvironment name)
  (left, right : SystemState name key value world error) where
  constructor MkO20HistoryCut
  historyCutBijection : NameBijection name
  0 historyCutRuntime : O20AllNameCut name key world error value nameEq historyCutBijection left right
  0 historyCutForward : (selected : name) -> (stamp : RegistrationGeneration name) ->
    (lookupCurrentGeneration @{nameEq} selected leftLive = Just stamp) ->
    (renameForward historyCutBijection selected = o20HistoricalTarget mapping stamp)
  0 historyCutBackward : (selected : name) -> (stamp : RegistrationGeneration name) ->
    (lookupCurrentGeneration @{nameEq} selected rightLive = Just stamp) ->
    (renameBackward historyCutBijection selected = generationName (generationBackward mapping stamp))
