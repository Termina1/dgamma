module DGamma.CP4IndependenceNonVacuity

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import Decidable.Equality

%default total

0 singletonOccursActor :
  (occurrence : OccursIn selected (MoreTransitions head NoTransitions)) ->
  transitionActor selected = transitionActor head
singletonOccursActor OccursHere = Refl
singletonOccursActor (OccursLater later) = void (noOccurrenceInEmpty later)

0 firedOwner :
  (transition : Transition first last) ->
  transitionActor transition = actionOwner (transitionAction transition)
firedOwner (Fired nameEq keyEq (OInsert actor parent component) tag checked) = Refl
firedOwner (Fired nameEq keyEq (ORetire actor) tag checked) = Refl
firedOwner (Fired nameEq keyEq (ORemove actor) tag checked) = Refl
firedOwner (Fired nameEq keyEq (LBegin actor) tag checked) = Refl
firedOwner (Fired nameEq keyEq (LAdvance actor) tag checked) = Refl
firedOwner (Fired nameEq keyEq (LDivert actor) tag checked) = Refl
firedOwner (Fired nameEq keyEq (LLeave actor) tag checked) = Refl
firedOwner (Fired nameEq keyEq (LUnload actor) tag checked) = Refl

0 iteratorStageActorAtSingleton :
  (head : Transition first last) ->
  IteratorStage name key world error value actor
    (MoreTransitions head NoTransitions) ->
  actor = transitionActor head
iteratorStageActorAtSingleton head
  (StageFromAdvance nameEq keyEq actor tag equation occurs fiber found remaining
    accumulator view lifecycle step rest suffix) =
  trans
    (sym (firedOwner (Fired nameEq keyEq (LAdvance actor) tag equation)))
    (singletonOccursActor occurs)

0 actualGeneratorActor :
  (head : Transition first last) ->
  (generator : TraceEffectGenerator name key world error value actor
    (MoreTransitions head NoTransitions)) ->
  actor = transitionActor head
actualGeneratorActor head
  (ActualForwardGenerator before afterState nameEq keyEq action tag equation occurs
    actorMatches) =
  trans (sym actorMatches)
    (trans (sym (firedOwner _)) (singletonOccursActor occurs))
actualGeneratorActor head (IteratorForwardGenerator stage) =
  iteratorStageActorAtSingleton head stage
actualGeneratorActor head (IteratorYieldedGenerator stage origin) =
  iteratorStageActorAtSingleton head stage

0 foreignTransformationIdentity :
  (head : Transition first last) ->
  Not (actor = transitionActor head) ->
  (transformation : TraceEffectTransformation name key world error value actor
    (MoreTransitions head NoTransitions)) ->
  (state : EffectState name key value world) ->
  runTraceEffectTransformation transformation state = Just state
foreignTransformationIdentity head distinct TraceIdentity state = Refl
foreignTransformationIdentity head distinct (TraceGenerator generator) state =
  void (distinct (actualGeneratorActor head generator))
foreignTransformationIdentity head distinct (TraceCompose after before) state =
  rewrite foreignTransformationIdentity head distinct before state in
    foreignTransformationIdentity head distinct after state

||| Every concrete singleton trace has a constructive Definition-60 witness:
||| all generators belong to its sole actor, so a transformation for any
||| distinct actor is identity. This is non-vacuous even when the sole action is
||| effectful and has reachable iterator/yielded generators.
public export
0 singletonTraceIndependent :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (head : Transition first last) ->
  TraceIndependent name key world error value keyEq
    (MoreTransitions head NoTransitions)
singletonTraceIndependent nameEq keyEq head = MkTraceIndependent commute stable
  where
  0 commute :
    (left, right : name) -> Not (left = right) ->
    (leftT : TraceEffectTransformation name key world error value left
      (MoreTransitions head NoTransitions)) ->
    (rightT : TraceEffectTransformation name key world error value right
      (MoreTransitions head NoTransitions)) ->
    PartialCommute (EffectStateEquivalence keyEq)
      (runTraceEffectTransformation leftT)
      (runTraceEffectTransformation rightT)
  commute left right distinct leftT rightT with
    (decEq @{nameEq} left (transitionActor head))
    commute left right distinct leftT rightT | No leftForeign =
      effectIdentityOnLeftCommutes keyEq (runTraceEffectTransformation leftT)
        (foreignTransformationIdentity head leftForeign leftT)
        (runTraceEffectTransformation rightT)
    commute left right distinct leftT rightT | Yes leftIsActor =
      let 0 rightForeign : Not (right = transitionActor head)
          rightForeign same = distinct (trans leftIsActor (sym same))
      in effectIdentityOnRightCommutes keyEq (runTraceEffectTransformation leftT)
        (runTraceEffectTransformation rightT)
        (foreignTransformationIdentity head rightForeign rightT)

  0 stable :
    (left, right : name) -> Not (left = right) ->
    (stage : IteratorStage name key world error value left
      (MoreTransitions head NoTransitions)) ->
    (foreign : TraceEffectTransformation name key world error value right
      (MoreTransitions head NoTransitions)) ->
    (origin : EffectState name key value world) ->
    IteratorYieldStableUnder keyEq stage
      (runTraceEffectTransformation foreign) origin
  stable left right distinct stage foreign origin =
    let leftIsActor = iteratorStageActorAtSingleton head stage
        0 rightForeign : Not (right = transitionActor head)
        rightForeign same = distinct (trans leftIsActor (sym same))
        0 foreignIdentity : runTraceEffectTransformation foreign origin =
          Just origin
        foreignIdentity = foreignTransformationIdentity head rightForeign foreign
          origin
    in rewrite foreignIdentity in
      iteratorYieldAgreementReflexive keyEq stage origin
