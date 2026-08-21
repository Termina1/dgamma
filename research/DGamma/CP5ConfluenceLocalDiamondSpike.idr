module DGamma.CP5ConfluenceLocalDiamondSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionRelationalBoundary
import Decidable.Equality

%default total

||| Exactly the three paper-Lemma-71 activation rules.  The host collapses
||| L-Iter and L-Finish into the action LAdvance and distinguishes them by tag.
public export
data PaperActivationStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> Type where
  PaperBeginStep :
    transitionAction transition = LBegin actor ->
    transitionTag transition = LBeginTag ->
    PaperActivationStep transition
  PaperIterStep :
    transitionAction transition = LAdvance actor ->
    transitionTag transition = LIterTag ->
    PaperActivationStep transition
  PaperFinishStep :
    transitionAction transition = LAdvance actor ->
    transitionTag transition = LFinishTag ->
    PaperActivationStep transition

||| The three explicit host orchestration rules.
public export
data PaperOrchestrationStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> Type where
  PaperInsertStep :
    transitionAction transition = OInsert actor parent component ->
    PaperOrchestrationStep transition
  PaperRetireStep :
    transitionAction transition = ORetire actor ->
    PaperOrchestrationStep transition
  PaperRemoveStep :
    transitionAction transition = ORemove actor ->
    PaperOrchestrationStep transition

||| Relational local diamond suitable for splicing by replay rather than by
||| forbidden equality of function-valued effect tables and accumulators.
public export
record LocalRelationalDiamond
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {first, middle, originalFinal : SystemState name key value world error}
  (left : Transition first middle)
  (right : Transition middle originalFinal) where
  constructor MkLocalRelationalDiamond
  swappedMiddle : SystemState name key value world error
  swappedFinal : SystemState name key value world error
  movedRight : Transition first swappedMiddle
  movedLeft : Transition swappedMiddle swappedFinal
  0 movedRightAction : transitionAction movedRight = transitionAction right
  0 movedLeftAction : transitionAction movedLeft = transitionAction left
  0 swappedEffects : EffectStateRelated keyEq
    (projectEffectState @{nameEq} originalFinal)
    (projectEffectState @{nameEq} swappedFinal)
  0 swappedControls : OrderedRegistryControlsRelated name key world error value
    (bindings (registry originalFinal)) (bindings (registry swappedFinal))
  0 swappedWellFormed : registryWellFormed @{nameEq} @{keyEq} swappedFinal = True

||| Candidate for paper Lemma 71(1).  The explicit early firing is the paper's
||| premise that the second activation is already applicable before the first.
||| The remaining proof should combine two actual effect generators from the
||| pairwise-independent universe with per-tag control/applicability frames.
public export
0 activationActivationDiamondSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal, earlyRightFinal :
    SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (earlyRight : Transition first earlyRightFinal) ->
  transitionAction earlyRight = transitionAction right ->
  PaperActivationStep left -> PaperActivationStep right ->
  Not (transitionActor left = transitionActor right) ->
  registryWellFormed @{nameEq} @{keyEq} first = True ->
  TraceIndependent name key world error value keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
activationActivationDiamondSpike = ?activationActivationDiamondSpike_rhs

||| Candidate for paper Lemma 71(2).  `foreignToRegistrationParent` is the host
||| specialization of "the activation does not register n" for generated
||| O-Insert: the moved activation is not the parent whose current iterator head
||| licenses the child birth.  Root insertion and retire/remove do not need this
||| field, so the premise is deliberately conditional on the action shape.
public export
0 activationOrchestrationDiamondSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal : SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  PaperActivationStep left -> PaperOrchestrationStep right ->
  Not (transitionActor left = transitionActor right) ->
  ((child, parent : name) ->
    (component : Component key value world error) ->
    transitionAction right = OInsert child (ChildOf parent) component ->
    Not (transitionActor left = parent)) ->
  registryWellFormed @{nameEq} @{keyEq} first = True ->
  TraceIndependent name key world error value keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
activationOrchestrationDiamondSpike = ?activationOrchestrationDiamondSpike_rhs
