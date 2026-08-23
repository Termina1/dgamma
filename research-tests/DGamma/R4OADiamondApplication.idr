module DGamma.R4OADiamondApplication

import DGamma.Calculus
import DGamma.CP3
import DGamma.Metatheory
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

0 applyReverseMixedOrientation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal, earlyRightFinal :
    SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (earlyRight : Transition first earlyRightFinal) ->
  transitionAction earlyRight = transitionAction right ->
  transitionTag earlyRight = transitionTag right ->
  PaperOrchestrationStep left -> PaperActivationStep right ->
  Not (transitionActor left = transitionActor right) ->
  ((child : name) -> (parent : Parent name) ->
    (component : Component key value world error) ->
    transitionAction left = OInsert child parent component ->
    Not (transitionActor right = child)) ->
  ((child, parent : name) ->
    (component : Component key value world error) ->
    transitionAction left = OInsert child (ChildOf parent) component ->
    Not (transitionActor right = parent)) ->
  registryWellFormed @{nameEq} @{keyEq} first = True ->
  TraceIndependent name key world error value keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
applyReverseMixedOrientation nameEq keyEq left right earlyRight actionEq tagEq
  leftO rightA distinct childSafe parentSafe wellFormed independent =
    DGamma.CP5ConfluenceLocalDiamondSpike.orchestrationActivationDiamondSpike
      nameEq keyEq left right earlyRight actionEq tagEq leftO rightA distinct
      childSafe parentSafe wellFormed independent
