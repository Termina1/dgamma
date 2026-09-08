module DGamma.CP5O20CanonicalOrdinalAttachmentSpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
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
