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
