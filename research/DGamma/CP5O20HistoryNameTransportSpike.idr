module DGamma.CP5O20HistoryNameTransportSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP5O20PairedRemovalSpike
import Data.Maybe
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

||| Any owned internal cut at the accepted final generation environments
||| agrees with the supplied current bijection on supported current names.
||| This does not rebase the whole all-name control relation or cover a
||| present vestigial remainder; those are separate endpoint obligations.
export
0 o20HistoryCutSupportedAgreement :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  (current : CurrentEndpointRenaming nameEq keyEq mapping left right registrations) ->
  (paired : O20HistoryCut name key world error value nameEq mapping
    (leftFinalGenerations registrations) (rightFinalGenerations registrations) leftFinal rightFinal) ->
  (selected : name) -> (stamp : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} selected (leftFinalGenerations registrations) = Just stamp) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} selected leftFinal = True) ->
  (renameForward (historyCutBijection paired) selected = renameForward (currentNameBijection current) selected)
o20HistoryCutSupportedAgreement nameEq keyEq left right mapping registrations current paired selected stamp found supported =
  trans (historyCutForward paired selected stamp found)
    (o20HistorySupportedEndpoint nameEq keyEq left right mapping registrations current selected stamp found supported)

||| The actual empty origin inhabits the history cut for ANY internal
||| bijection. The generation clauses are empty-domain eliminations.
export
0 o20HistoryEmptyOrigin :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (mapping : RegistrationGenerationBijection name) ->
  (renaming : NameBijection name) -> (initial : SystemState name key value world error) ->
  (bindings (registry initial) = []) ->
  O20HistoryCut name key world error value nameEq mapping [] [] initial initial
o20HistoryEmptyOrigin nameEq mapping renaming initial empty =
  MkO20HistoryCut renaming (o20AllNameEmptyOrigin nameEq renaming initial empty)
    (\selected, stamp, found => absurd found) (\selected, stamp, found => absurd found)

||| Deleting a unique live generation cannot reveal a different shadow birth.
||| Every surviving current lookup is the exact pre-deletion lookup.
export
0 o20HistoryLookupBeforeRemove :
  {name : Type} -> (nameEq : DecEq name) -> (removed, selected : name) ->
  (live : GenerationEnvironment name) -> GenerationEnvironmentNamesUnique live ->
  (stamp : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} selected (deleteCurrentGeneration @{nameEq} removed live) = Just stamp) ->
  (lookupCurrentGeneration @{nameEq} selected live = Just stamp)
o20HistoryLookupBeforeRemove nameEq removed selected live unique stamp found =
  case decEq @{nameEq} selected removed of
    Yes same => void (nothingIsNotJust
      (trans (sym (lookupDeleteCurrentSelf nameEq removed live unique))
        (trans (cong (\query => lookupCurrentGeneration @{nameEq} query
          (deleteCurrentGeneration @{nameEq} removed live)) (sym same)) found)))
    No different => trans
      (sym (lookupAdvanceGenerationOther {key = Unit} {value = \_ => Unit} {world = Unit} {error = Unit}
        nameEq 0 (ORemove removed) selected different live)) found

||| Actual paired Remove preserves the history-indexed internal cut. The
||| removed generation leaves the live domain, so no endpoint raw-name match
||| is imposed on its historical birth. Both native checks remain explicit.
export
0 o20HistoryRemoveCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (mapping : RegistrationGenerationBijection name) -> (actor : name) ->
  (leftLive, rightLive : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique leftLive -> GenerationEnvironmentNamesUnique rightLive ->
  (leftWorld, rightWorld : world) -> (leftRegistry, rightRegistry : Registry name key value world error) ->
  (paired : O20HistoryCut name key world error value nameEq mapping leftLive rightLive
    (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry)) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (ORemove actor) (MkSystemState leftWorld leftRegistry) =
    Just (ORemoveTag, MkSystemState leftWorld (deleteBinding @{nameEq} actor leftRegistry))) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (ORemove (renameForward (historyCutBijection paired) actor)) (MkSystemState rightWorld rightRegistry) =
    Just (ORemoveTag, MkSystemState rightWorld
      (deleteBinding @{nameEq} (renameForward (historyCutBijection paired) actor) rightRegistry))) ->
  O20HistoryCut name key world error value nameEq mapping
    (deleteCurrentGeneration @{nameEq} actor leftLive)
    (deleteCurrentGeneration @{nameEq} (renameForward (historyCutBijection paired) actor) rightLive)
    (MkSystemState leftWorld (deleteBinding @{nameEq} actor leftRegistry))
    (MkSystemState rightWorld (deleteBinding @{nameEq} (renameForward (historyCutBijection paired) actor) rightRegistry))
o20HistoryRemoveCut nameEq keyEq mapping actor leftLive rightLive leftUnique rightUnique
  leftWorld rightWorld leftRegistry rightRegistry (MkO20HistoryCut renaming runtime forward backward) leftChecked rightChecked =
    MkO20HistoryCut renaming
      (o20PairedObservedRemoveCut nameEq keyEq renaming actor leftWorld rightWorld leftRegistry rightRegistry leftChecked rightChecked runtime)
      (\selected, stamp, found => forward selected stamp
        (o20HistoryLookupBeforeRemove nameEq actor selected leftLive leftUnique stamp found))
      (\selected, stamp, found => backward selected stamp
        (o20HistoryLookupBeforeRemove nameEq (renameForward renaming actor) selected rightLive rightUnique stamp found))

||| Historical generation stamp of an actual generated registration. This
||| constructor conversion does not inspect a concrete nested trace builder.
export
0 o20GeneratedHistoryBirth :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, finalState : SystemState name key value world error} ->
  {trace : Transitions initial finalState} -> {child, parent : name} ->
  {component : Component key value world error} ->
  (birth : LocatedGeneratedRegistration child parent component trace) ->
  CurrentGenerationBirth name key world error value trace child (registrationGeneration birth)
o20GeneratedHistoryBirth {parent} {component}
  (MkLocatedGeneratedRegistration before afterState earlier step later actionExact decomposition) =
    MkCurrentGenerationBirth (ChildOf parent) component
      (MkLocatedActionOccurrence before afterState earlier step later actionExact decomposition) Refl

||| Full current-generation partition: either an AUTHENTIC present vestigial
||| remainder, or exact history/current-name agreement. Unlike support-only
||| A7, this does not discard the valid unsupported-but-present branch.
export
0 o20HistoryEndpointChoice :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  (current : CurrentEndpointRenaming nameEq keyEq mapping left right registrations) ->
  (selected : name) -> (stamp : RegistrationGeneration name) ->
  Either
    (VestigialEndpointGeneration name key world error value nameEq keyEq
      (leftFinalGenerations registrations) (leftDeletedGenerations registrations) selected leftFinal)
    (rightStamp : RegistrationGeneration name **
      ((generationForward mapping stamp = rightStamp),
       (lookupCurrentGeneration @{nameEq} (renameForward (currentNameBijection current) selected)
         (rightFinalGenerations registrations) = Just rightStamp))) ->
  Either
    (VestigialEndpointGeneration name key world error value nameEq keyEq
      (leftFinalGenerations registrations) (leftDeletedGenerations registrations) selected leftFinal)
    (o20HistoricalTarget mapping stamp = renameForward (currentNameBijection current) selected)
o20HistoryEndpointChoice nameEq keyEq left right mapping registrations current selected stamp (Left vestigial) = Left vestigial
o20HistoryEndpointChoice nameEq keyEq left right mapping registrations current selected stamp (Right matched) =
  Right (o20HistoryEndpointPacketAgrees nameEq left right mapping registrations
    (renameForward (currentNameBijection current) selected) stamp matched)

||| The actual accepted current-generation scanner owns the complete endpoint
||| partition. Mere presence does not imply raw-name agreement: only the
||| non-vestigial branch does. Both alternatives retain exact original indices.
export
0 o20HistoryEndpointPartition :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  (current : CurrentEndpointRenaming nameEq keyEq mapping left right registrations) ->
  (selected : name) -> (stamp : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} selected (leftFinalGenerations registrations) = Just stamp) ->
  Either
    (VestigialEndpointGeneration name key world error value nameEq keyEq
      (leftFinalGenerations registrations) (leftDeletedGenerations registrations) selected leftFinal)
    (o20HistoricalTarget mapping stamp = renameForward (currentNameBijection current) selected)
o20HistoryEndpointPartition nameEq keyEq left right mapping registrations current selected stamp found =
  o20HistoryEndpointChoice nameEq keyEq left right mapping registrations current selected stamp
    (leftCurrentGenerationMapped current selected stamp found)

||| Exact history/current agreement for ANY non-vestigial current generation,
||| including unsupported present fibers. The full inert discarded-generation
||| alternative, not presence alone, is what must be excluded.
export
0 o20HistoryNonVestigialEndpoint :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  (current : CurrentEndpointRenaming nameEq keyEq mapping left right registrations) ->
  (selected : name) -> (stamp : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} selected (leftFinalGenerations registrations) = Just stamp) ->
  Not (VestigialEndpointGeneration name key world error value nameEq keyEq
    (leftFinalGenerations registrations) (leftDeletedGenerations registrations) selected leftFinal) ->
  (o20HistoricalTarget mapping stamp = renameForward (currentNameBijection current) selected)
o20HistoryNonVestigialEndpoint nameEq keyEq left right mapping registrations current selected stamp found nonVestigial =
  either (\vestigial => void (nonVestigial vestigial)) (\same => same)
    (o20HistoryEndpointPartition nameEq keyEq left right mapping registrations current selected stamp found)
