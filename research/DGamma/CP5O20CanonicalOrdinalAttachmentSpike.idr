module DGamma.CP5O20CanonicalOrdinalAttachmentSpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20SupportedBirthBridgeSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import Decidable.Equality

%default total
%unbound_implicits off

||| Conjugate the accepted ORIGINAL generation map by the two actual replay
||| maps. This executable bijection acts on canonical insertion ordinals;
||| the original map alone need not act on those reordered ordinals.
public export
o20ReplayOrdinalBijection :
  {name : Type} ->
  (leftReplay, original, rightReplay : RegistrationGenerationBijection name) ->
  RegistrationGenerationBijection name
o20ReplayOrdinalBijection leftReplay original rightReplay =
  MkRegistrationGenerationBijection
    (\stamp => generationForward rightReplay (generationForward original (generationBackward leftReplay stamp)))
    (\stamp => generationForward leftReplay (generationBackward original (generationBackward rightReplay stamp)))
    (\stamp => trans
      (cong (\middle => generationForward leftReplay (generationBackward original middle))
        (generationLeftInverse rightReplay (generationForward original (generationBackward leftReplay stamp))))
      (trans (cong (generationForward leftReplay) (generationLeftInverse original (generationBackward leftReplay stamp)))
        (generationRightInverse leftReplay stamp)))
    (\stamp => trans
      (cong (\middle => generationForward rightReplay (generationForward original middle))
        (generationLeftInverse leftReplay (generationBackward original (generationBackward rightReplay stamp))))
      (trans (cong (generationForward rightReplay) (generationRightInverse original (generationBackward rightReplay stamp)))
        (generationRightInverse rightReplay stamp)))

||| Transport an authentic original-stamp equation to canonical coordinates.
||| The two replay equations are explicit here; the next occurrence producer
||| discharges them from the actual correspondence rather than assuming them.
export
0 o20ReplayOrdinalMatched :
  {name : Type} ->
  (leftReplay, original, rightReplay : RegistrationGenerationBijection name) ->
  (leftOrigin, rightOrigin, leftStamp, rightStamp : RegistrationGeneration name) ->
  (generationForward leftReplay leftOrigin = leftStamp) ->
  (generationForward rightReplay rightOrigin = rightStamp) ->
  (generationForward original leftOrigin = rightOrigin) ->
  (generationForward (o20ReplayOrdinalBijection leftReplay original rightReplay) leftStamp = rightStamp)
o20ReplayOrdinalMatched leftReplay original rightReplay leftOrigin rightOrigin leftStamp rightStamp leftExact rightExact matched =
  trans
    (cong (\stamp => generationForward rightReplay (generationForward original stamp))
      (trans (cong (generationBackward leftReplay) (sym leftExact)) (generationLeftInverse leftReplay leftOrigin)))
    (trans (cong (generationForward rightReplay) matched) rightExact)

||| Actual generated occurrences own both replay equations. Only their
||| original generation matching is input; canonical birth ordinals are the
||| exact counts of the occurrences' physical preceding traces.
export
0 o20GeneratedOrdinalsAttached :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {leftFirst, leftFinal, rightFirst, rightFinal, leftNowFirst, leftNowFinal, rightNowFirst, rightNowFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
  {leftNow : Transitions leftNowFirst leftNowFinal} -> {rightNow : Transitions rightNowFirst rightNowFinal} ->
  (leftReplay : ActionRegistrationReplayCorrespondence name key world error value left leftNow) ->
  (rightReplay : ActionRegistrationReplayCorrespondence name key world error value right rightNow) ->
  (original : RegistrationGenerationBijection name) ->
  {leftChild, leftParent, rightChild, rightParent : name} ->
  {leftComponent, rightComponent : Component key value world error} ->
  (leftBirth : LocatedGeneratedRegistration leftChild leftParent leftComponent leftNow) ->
  (rightBirth : LocatedGeneratedRegistration rightChild rightParent rightComponent rightNow) ->
  (generationForward original (registrationGeneration (replayGeneratedRegistrationOrigin leftReplay leftBirth)) =
    registrationGeneration (replayGeneratedRegistrationOrigin rightReplay rightBirth)) ->
  (generationForward (o20ReplayOrdinalBijection (replayGenerationRenaming leftReplay) original (replayGenerationRenaming rightReplay))
    (registrationGeneration leftBirth) = registrationGeneration rightBirth)
o20GeneratedOrdinalsAttached leftReplay rightReplay original leftBirth rightBirth matched =
  o20ReplayOrdinalMatched (replayGenerationRenaming leftReplay) original (replayGenerationRenaming rightReplay)
    (registrationGeneration (replayGeneratedRegistrationOrigin leftReplay leftBirth))
    (registrationGeneration (replayGeneratedRegistrationOrigin rightReplay rightBirth))
    (registrationGeneration leftBirth) (registrationGeneration rightBirth)
    (replayGeneratedOrdinalPreserved leftReplay leftBirth) (replayGeneratedOrdinalPreserved rightReplay rightBirth) matched

||| One fixed-name generated birth attachment with BOTH original-origin and
||| physical replay-stamp equations. All three proof fields are erased.
||| This record does not contain a whole paired execution or an endpoint cut.
public export
record O20AttachedGeneratedBirth
  (name, key, world, error : Type) (value : key -> Type)
  {leftFirst, leftFinal, rightFirst, rightFinal, leftNowFirst, leftNowFinal, rightNowFirst, rightNowFinal : SystemState name key value world error}
  {left : Transitions leftFirst leftFinal} {right : Transitions rightFirst rightFinal}
  {leftNow : Transitions leftNowFirst leftNowFinal} {rightNow : Transitions rightNowFirst rightNowFinal}
  (leftReplay : ActionRegistrationReplayCorrespondence name key world error value left leftNow)
  (rightReplay : ActionRegistrationReplayCorrespondence name key world error value right rightNow)
  (original : RegistrationGenerationBijection name) (renaming : NameBijection name)
  (child, parent : name) (component : Component key value world error)
  (leftBirth : LocatedGeneratedRegistration child parent component leftNow) where
  constructor MkO20AttachedGeneratedBirth
  0 attachedRightBirth : LocatedGeneratedRegistration (renameForward renaming child) (renameForward renaming parent) component rightNow
  0 attachedOriginalEquation :
    (generationForward original (registrationGeneration (replayGeneratedRegistrationOrigin leftReplay leftBirth)) =
      registrationGeneration (replayGeneratedRegistrationOrigin rightReplay attachedRightBirth))
  0 attachedPhysicalEquation :
    (generationForward (o20ReplayOrdinalBijection (replayGenerationRenaming leftReplay) original (replayGenerationRenaming rightReplay))
      (registrationGeneration leftBirth) = registrationGeneration attachedRightBirth)

||| Eliminate one authentic opposite-birth packet and construct both equations
||| simultaneously, using that SAME occurrence in the two dependent fields.
export
0 o20AttachGeneratedBirthPacket :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {leftFirst, leftFinal, rightFirst, rightFinal, leftNowFirst, leftNowFinal, rightNowFirst, rightNowFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
  {leftNow : Transitions leftNowFirst leftNowFinal} -> {rightNow : Transitions rightNowFirst rightNowFinal} ->
  (leftReplay : ActionRegistrationReplayCorrespondence name key world error value left leftNow) ->
  (rightReplay : ActionRegistrationReplayCorrespondence name key world error value right rightNow) ->
  (original : RegistrationGenerationBijection name) -> (renaming : NameBijection name) ->
  (child, parent : name) -> (component : Component key value world error) ->
  (leftBirth : LocatedGeneratedRegistration child parent component leftNow) ->
  (rightBirth : LocatedGeneratedRegistration (renameForward renaming child) (renameForward renaming parent) component rightNow **
    (generationForward original (registrationGeneration (replayGeneratedRegistrationOrigin leftReplay leftBirth)) =
      registrationGeneration (replayGeneratedRegistrationOrigin rightReplay rightBirth))) ->
  O20AttachedGeneratedBirth name key world error value leftReplay rightReplay original renaming child parent component leftBirth
o20AttachGeneratedBirthPacket leftReplay rightReplay original renaming child parent component leftBirth (rightBirth ** matched) =
  MkO20AttachedGeneratedBirth rightBirth matched
    (o20GeneratedOrdinalsAttached leftReplay rightReplay original leftBirth rightBirth matched)

||| Accepted supported-birth capital produces the opposite canonical birth and
||| BOTH original and actual canonical-ordinal equations. The supported scope
||| remains explicit; unsupported histories and whole stage alignment are not
||| asserted by this single-occurrence producer.
export
0 o20SupportedCanonicalOrdinalAttachment :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (inputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq left) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq right) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  GeneratedOrchestrationMatched name key world error value nameEq left right (generatedGenerationBijection inputs) ->
  (child, parent : name) -> (component : Component key value world error) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} child leftFinal = True) ->
  (leftBirth : LocatedGeneratedRegistration child parent component (canonicalTrace (canonicalSchedule leftCapital))) ->
  O20AttachedGeneratedBirth name key world error value
    (canonicalOccurrenceCorrespondence leftCapital) (canonicalOccurrenceCorrespondence rightCapital)
    (generatedGenerationBijection inputs) (expectedBridgeBijection inputs) child parent component leftBirth
o20SupportedCanonicalOrdinalAttachment name key world error value nameEq keyEq protocol left right inputs leftCapital rightCapital
  leftUnique rightUnique matched child parent component supported leftBirth =
    o20AttachGeneratedBirthPacket (canonicalOccurrenceCorrespondence leftCapital) (canonicalOccurrenceCorrespondence rightCapital)
      (generatedGenerationBijection inputs) (expectedBridgeBijection inputs) child parent component leftBirth
      (supportedCanonicalBirthBridge name key world error value nameEq keyEq protocol left right inputs leftCapital rightCapital
        leftUnique rightUnique matched child parent component supported leftBirth)
