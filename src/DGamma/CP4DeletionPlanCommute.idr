module DGamma.CP4DeletionPlanCommute

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionChildlessInvariant
import DGamma.CP4DeletionCommuteCore
import DGamma.CP4DeletionControlOrchestration
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPlanRuntime
import DGamma.CP4DeletionPlanSuccess
import Data.List.Elem
import Decidable.Equality

%default total

0 unequalSymmetric : Not (left = right) -> Not (right = left)
unequalSymmetric distinct Refl = distinct Refl

0 childOfInjectiveCommute : ChildOf left = ChildOf right -> left = right
childOfInjectiveCommute Refl = Refl

0 parentOutsideNotChildOf :
  (parent : Parent name) -> (removed : name) ->
  ParentOutside parent removed -> Not (parent = ChildOf removed)
parentOutsideNotChildOf Root removed outside Refl impossible
parentOutsideNotChildOf (ChildOf parent) removed distinct same =
  distinct (childOfInjectiveCommute same)

||| Result of commuting one registry update through an indexed Inactive-leaf
||| deletion plan.  Equality is intentionally stated only for the exact ordered
||| runtime binding list.  The transformed plan may carry different erased
||| `UniqueKeys` proof terms.
public export
record InactivePlanUpdateCommute
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name)
  {oldSource, oldTarget : Registry name key value world error}
  (oldPlan : InactiveLeafDeletionPlan {name = name} {key = key}
    {value = value} {world = world} {error = error} nameEq oldSource oldTarget)
  (newSource : Registry name key value world error)
  (expectedTargetBindings :
    List (Binding name (FiberAt name key value world error))) where
  constructor MkInactivePlanUpdateCommute
  commutedPlanTarget : Registry name key value world error
  commutedInactivePlan : InactiveLeafDeletionPlan {name = name} {key = key}
    {value = value} {world = world} {error = error} nameEq newSource
    commutedPlanTarget
  0 commutedTargetBindings : bindings commutedPlanTarget =
    expectedTargetBindings
  0 commutedActorOutside : (actor : name) ->
    ActorOutsideDeletionPlan actor oldPlan ->
    ActorOutsideDeletionPlan actor commutedInactivePlan

||| A retained O-Insert commutes through every deleted leaf when both its fresh
||| owner and (for a child insertion) its parent are outside the plan.
public export
0 insertFreshThroughInactivePlan :
  (nameEq : DecEq name) ->
  (inserted : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key}
    {value = value} {world = world} {error = error} nameEq source target) ->
  OrchestrationOutsideDeletionPlan
    (the (Action name key value world error)
      (OInsert inserted parent component)) plan ->
  (0 absent : lookupFiber @{nameEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} inserted source = Nothing) ->
  InactivePlanUpdateCommute name key world error value nameEq plan
    (insertBinding @{nameEq} inserted (freshFiber component parent) source absent)
    (Bind inserted (freshFiber component parent) :: bindings target)
insertFreshThroughInactivePlan nameEq inserted parent component
  source@(MkCoeffectContext entries unique) _ NoInactiveLeafDeletion
  OrchestrationOutsideDeletionEnd absent =
    MkInactivePlanUpdateCommute
      (insertBinding @{nameEq} inserted (freshFiber component parent) source absent)
      NoInactiveLeafDeletion Refl
      (\actor, ActorOutsideDeletionEnd => ActorOutsideDeletionEnd)
insertFreshThroughInactivePlan {name} {key} {world} {error} {value}
  nameEq inserted parent component source target
  (DeleteInactiveLeaf removed removedComponent removedParent removedRetired
    removedTable removedOutcome removedFound removedNoChild rest)
  (OrchestrationOutsideDeletionStep rest ownerOutside parentOutside outsideRest)
  absent =
    let 0 removedOutside : Not (removed = inserted)
        removedOutside = unequalSymmetric ownerOutside
        0 nextRemovedFound : lookupFiber @{nameEq} {name = name} {key = key}
          {value = value} {world = world} {error = error} removed
          (insertBinding @{nameEq} inserted (freshFiber component parent) source
            absent) = Just (MkFiber removedComponent removedParent removedRetired
              removedTable (Inactive removedOutcome))
        nextRemovedFound = trans
          (lookupInsertOther removed inserted removedOutside
            (freshFiber component parent) source absent)
          removedFound
        0 nextRemovedNoChild : hasChild @{nameEq} {name = name} {key = key}
          {value = value} {world = world} {error = error} removed
          (insertBinding @{nameEq} inserted (freshFiber component parent) source
            absent) = False
        nextRemovedNoChild = hasChildInsertFalse nameEq removed inserted component
          parent source absent (parentOutsideNotChildOf parent removed parentOutside)
          removedNoChild
        oldTailSource : Registry name key value world error
        oldTailSource = deleteBinding @{nameEq} removed source
        0 tailAbsent : lookupFiber @{nameEq} {name = name} {key = key}
          {value = value} {world = world} {error = error} inserted oldTailSource =
          Nothing
        tailAbsent = trans
          (lookupDeleteOther inserted removed ownerOutside source) absent
        canonicalTailSource : Registry name key value world error
        canonicalTailSource = insertBinding @{nameEq} inserted
          (freshFiber component parent) oldTailSource tailAbsent
        actualTailSource : Registry name key value world error
        actualTailSource = deleteBinding @{nameEq} removed
          (insertBinding @{nameEq} inserted (freshFiber component parent) source
            absent)
        0 tailCommute : InactivePlanUpdateCommute name key world error value
          nameEq rest canonicalTailSource
          (Bind inserted (freshFiber component parent) :: bindings target)
        tailCommute = insertFreshThroughInactivePlan nameEq inserted parent
          component oldTailSource target rest outsideRest tailAbsent
        0 tailSourcesSame : bindings canonicalTailSource =
          bindings actualTailSource
        tailSourcesSame = trans
          (insertBindingRuntimeBindings nameEq inserted
            (freshFiber component parent) oldTailSource tailAbsent)
          (sym (deleteBindingAfterDistinctInsertBindings nameEq inserted removed
            ownerOutside (freshFiber component parent) source absent))
        0 transported : InactivePlanBindingsTransport name key world error value
          nameEq (commutedInactivePlan tailCommute) actualTailSource
        transported = transportInactivePlanAcrossBindings nameEq canonicalTailSource
          (commutedPlanTarget tailCommute) actualTailSource
          (commutedInactivePlan tailCommute) tailSourcesSame
        nextPlan : InactiveLeafDeletionPlan {name = name} {key = key}
          {value = value} {world = world} {error = error} nameEq
          (insertBinding @{nameEq} inserted (freshFiber component parent) source
            absent)
          (transportedPlanTarget transported)
        nextPlan = DeleteInactiveLeaf removed removedComponent removedParent
          removedRetired removedTable removedOutcome nextRemovedFound
          nextRemovedNoChild (transportedInactivePlan transported)
        0 targetBindings : bindings (transportedPlanTarget transported) =
          Bind inserted (freshFiber component parent) :: bindings target
        targetBindings = trans (sym (transportedPlanBindings transported))
          (commutedTargetBindings tailCommute)
        0 outsideCommute : (actor : name) ->
          ActorOutsideDeletionPlan actor
            (DeleteInactiveLeaf {fibers = source} {target = target} removed
              removedComponent removedParent removedRetired removedTable
              removedOutcome removedFound removedNoChild rest) ->
          ActorOutsideDeletionPlan actor nextPlan
        outsideCommute actor
          (ActorOutsideDeletionStep _ actorDistinct actorOutsideRest) =
            ActorOutsideDeletionStep (transportedInactivePlan transported)
              actorDistinct
              (transportedActorOutside transported actor
                (commutedActorOutside tailCommute actor actorOutsideRest))
        outsideCommute actor ActorOutsideDeletionEnd impossible
    in MkInactivePlanUpdateCommute (transportedPlanTarget transported) nextPlan
      targetBindings outsideCommute

||| A parent-preserving replacement of an actor outside the plan commutes
||| through the complete leaf deletion.  All evaluator replacement branches
||| satisfy the parent-preservation premise.
public export
0 replaceOutsideThroughInactivePlan :
  (nameEq : DecEq name) ->
  (changed : name) ->
  (old, next : Fiber name key value world error) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key}
    {value = value} {world = world} {error = error} nameEq source target) ->
  ActorOutsideDeletionPlan changed plan ->
  (0 found : lookupFiber @{nameEq} changed source = Just old) ->
  (0 sameParent : fiberParent next = fiberParent old) ->
  InactivePlanUpdateCommute name key world error value nameEq plan
    (replaceBinding @{nameEq} changed next source)
    (replaceEntries @{nameEq} changed next (bindings target))
replaceOutsideThroughInactivePlan nameEq changed old next
  source@(MkCoeffectContext entries unique) _ NoInactiveLeafDeletion
  ActorOutsideDeletionEnd found sameParent =
    MkInactivePlanUpdateCommute (replaceBinding @{nameEq} changed next source)
      NoInactiveLeafDeletion Refl
      (\actor, ActorOutsideDeletionEnd => ActorOutsideDeletionEnd)
replaceOutsideThroughInactivePlan {name} {key} {world} {error} {value}
  nameEq changed old next source target
  (DeleteInactiveLeaf removed removedComponent removedParent removedRetired
    removedTable removedOutcome removedFound removedNoChild rest)
  (ActorOutsideDeletionStep rest changedOutside outsideRest) found sameParent =
    let 0 removedOutside : Not (removed = changed)
        removedOutside = unequalSymmetric changedOutside
        0 nextRemovedFound : lookupFiber @{nameEq} removed
          (replaceBinding @{nameEq} changed next source) =
          Just (MkFiber removedComponent removedParent removedRetired removedTable
            (Inactive removedOutcome))
        nextRemovedFound = trans
          (lookupReplaceOther removed changed removedOutside next source)
          removedFound
        0 nextRemovedNoChild : hasChild @{nameEq} {name = name} {key = key}
          {value = value} {world = world} {error = error} removed
          (replaceBinding @{nameEq} changed next source) = False
        nextRemovedNoChild = hasChildReplaceFalse nameEq removed changed next old
          source found sameParent removedNoChild
        oldTailSource : Registry name key value world error
        oldTailSource = deleteBinding @{nameEq} removed source
        0 tailFound : lookupFiber @{nameEq} changed oldTailSource = Just old
        tailFound = trans (lookupDeleteOther changed removed changedOutside source)
          found
        canonicalTailSource : Registry name key value world error
        canonicalTailSource = replaceBinding @{nameEq} changed next oldTailSource
        actualTailSource : Registry name key value world error
        actualTailSource = deleteBinding @{nameEq} removed
          (replaceBinding @{nameEq} changed next source)
        0 tailCommute : InactivePlanUpdateCommute name key world error value
          nameEq rest canonicalTailSource
          (replaceEntries @{nameEq} changed next (bindings target))
        tailCommute = replaceOutsideThroughInactivePlan nameEq changed old next
          oldTailSource target rest outsideRest tailFound sameParent
        0 tailSourcesSame : bindings canonicalTailSource =
          bindings actualTailSource
        tailSourcesSame = trans
          (replaceBindingRuntimeBindings nameEq changed next oldTailSource)
          (sym (deleteBindingAfterDistinctReplaceBindings nameEq changed removed
            changedOutside next source))
        0 transported : InactivePlanBindingsTransport name key world error value
          nameEq (commutedInactivePlan tailCommute) actualTailSource
        transported = transportInactivePlanAcrossBindings nameEq canonicalTailSource
          (commutedPlanTarget tailCommute) actualTailSource
          (commutedInactivePlan tailCommute) tailSourcesSame
        nextPlan : InactiveLeafDeletionPlan {name = name} {key = key}
          {value = value} {world = world} {error = error} nameEq
          (replaceBinding @{nameEq} changed next source)
          (transportedPlanTarget transported)
        nextPlan = DeleteInactiveLeaf removed removedComponent removedParent
          removedRetired removedTable removedOutcome nextRemovedFound
          nextRemovedNoChild (transportedInactivePlan transported)
        0 targetBindings : bindings (transportedPlanTarget transported) =
          replaceEntries @{nameEq} changed next (bindings target)
        targetBindings = trans (sym (transportedPlanBindings transported))
          (commutedTargetBindings tailCommute)
        0 outsideCommute : (actor : name) ->
          ActorOutsideDeletionPlan actor
            (DeleteInactiveLeaf {fibers = source} {target = target} removed
              removedComponent removedParent removedRetired removedTable
              removedOutcome removedFound removedNoChild rest) ->
          ActorOutsideDeletionPlan actor nextPlan
        outsideCommute actor
          (ActorOutsideDeletionStep _ actorDistinct actorOutsideRest) =
            ActorOutsideDeletionStep (transportedInactivePlan transported)
              actorDistinct
              (transportedActorOutside transported actor
                (commutedActorOutside tailCommute actor actorOutsideRest))
        outsideCommute actor ActorOutsideDeletionEnd impossible
    in MkInactivePlanUpdateCommute (transportedPlanTarget transported) nextPlan
      targetBindings outsideCommute

||| Deleting an actor outside the plan commutes with deleting every plan leaf.
public export
0 deleteOutsideThroughInactivePlan :
  (nameEq : DecEq name) ->
  (changed : name) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key}
    {value = value} {world = world} {error = error} nameEq source target) ->
  ActorOutsideDeletionPlan changed plan ->
  InactivePlanUpdateCommute name key world error value nameEq plan
    (deleteBinding @{nameEq} changed source)
    (deleteEntries @{nameEq} changed (bindings target))
deleteOutsideThroughInactivePlan nameEq changed
  source@(MkCoeffectContext entries unique) _ NoInactiveLeafDeletion
  ActorOutsideDeletionEnd =
    MkInactivePlanUpdateCommute (deleteBinding @{nameEq} changed source)
      NoInactiveLeafDeletion Refl
      (\actor, ActorOutsideDeletionEnd => ActorOutsideDeletionEnd)
deleteOutsideThroughInactivePlan {name} {key} {world} {error} {value}
  nameEq changed source target
  (DeleteInactiveLeaf removed removedComponent removedParent removedRetired
    removedTable removedOutcome removedFound removedNoChild rest)
  (ActorOutsideDeletionStep rest changedOutside outsideRest) =
    let 0 removedOutside : Not (removed = changed)
        removedOutside = unequalSymmetric changedOutside
        0 nextRemovedFound : lookupFiber @{nameEq} removed
          (deleteBinding @{nameEq} changed source) =
          Just (MkFiber removedComponent removedParent removedRetired removedTable
            (Inactive removedOutcome))
        nextRemovedFound = trans
          (lookupDeleteOther removed changed removedOutside source) removedFound
        0 nextRemovedNoChild : hasChild @{nameEq} {name = name} {key = key}
          {value = value} {world = world} {error = error} removed
          (deleteBinding @{nameEq} changed source) = False
        nextRemovedNoChild = hasChildDeleteFalse nameEq removed changed source
          removedNoChild
        oldTailSource : Registry name key value world error
        oldTailSource = deleteBinding @{nameEq} removed source
        canonicalTailSource : Registry name key value world error
        canonicalTailSource = deleteBinding @{nameEq} changed oldTailSource
        actualTailSource : Registry name key value world error
        actualTailSource = deleteBinding @{nameEq} removed
          (deleteBinding @{nameEq} changed source)
        0 tailCommute : InactivePlanUpdateCommute name key world error value
          nameEq rest canonicalTailSource
          (deleteEntries @{nameEq} changed (bindings target))
        tailCommute = deleteOutsideThroughInactivePlan nameEq changed oldTailSource
          target rest outsideRest
        0 tailSourcesSame : bindings canonicalTailSource =
          bindings actualTailSource
        tailSourcesSame = deleteBindingDistinctCommuteBindings nameEq changed
          removed changedOutside source
        0 transported : InactivePlanBindingsTransport name key world error value
          nameEq (commutedInactivePlan tailCommute) actualTailSource
        transported = transportInactivePlanAcrossBindings nameEq canonicalTailSource
          (commutedPlanTarget tailCommute) actualTailSource
          (commutedInactivePlan tailCommute) tailSourcesSame
        nextPlan : InactiveLeafDeletionPlan {name = name} {key = key}
          {value = value} {world = world} {error = error} nameEq
          (deleteBinding @{nameEq} changed source)
          (transportedPlanTarget transported)
        nextPlan = DeleteInactiveLeaf removed removedComponent removedParent
          removedRetired removedTable removedOutcome nextRemovedFound
          nextRemovedNoChild (transportedInactivePlan transported)
        0 targetBindings : bindings (transportedPlanTarget transported) =
          deleteEntries @{nameEq} changed (bindings target)
        targetBindings = trans (sym (transportedPlanBindings transported))
          (commutedTargetBindings tailCommute)
        0 outsideCommute : (actor : name) ->
          ActorOutsideDeletionPlan actor
            (DeleteInactiveLeaf {fibers = source} {target = target} removed
              removedComponent removedParent removedRetired removedTable
              removedOutcome removedFound removedNoChild rest) ->
          ActorOutsideDeletionPlan actor nextPlan
        outsideCommute actor
          (ActorOutsideDeletionStep _ actorDistinct actorOutsideRest) =
            ActorOutsideDeletionStep (transportedInactivePlan transported)
              actorDistinct
              (transportedActorOutside transported actor
                (commutedActorOutside tailCommute actor actorOutsideRest))
        outsideCommute actor ActorOutsideDeletionEnd impossible
    in MkInactivePlanUpdateCommute (transportedPlanTarget transported) nextPlan
      targetBindings outsideCommute

0 memberTailWhenHeadDistinct :
  (actor, head : name) -> Not (actor = head) ->
  (rest : List name) -> Elem actor (head :: rest) -> Elem actor rest
memberTailWhenHeadDistinct actor actor distinct rest Here = void (distinct Refl)
memberTailWhenHeadDistinct actor head distinct rest (There later) = later

||| If the original action removes an actor that the plan itself deletes, erase
||| that exact plan occurrence instead of replaying the action.  The resulting
||| target is equal to the old plan target only at ordered runtime bindings;
||| proof-term equality is neither required nor claimed.
public export
0 removeExactActorFromInactivePlan :
  (nameEq : DecEq name) ->
  (removedActor : name) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key}
    {value = value} {world = world} {error = error} nameEq source target) ->
  ActorDeletedByInactivePlan {name = name} {key = key} {value = value}
    {world = world} {error = error} removedActor plan ->
  (0 actorNoChild : hasChild @{nameEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} removedActor source = False) ->
  InactivePlanUpdateCommute name key world error value nameEq plan
    (deleteBinding @{nameEq} removedActor source) (bindings target)
removeExactActorFromInactivePlan nameEq removedActor source source
  NoInactiveLeafDeletion present actorNoChild = void (elemNilVoid present)
  where
  0 elemNilVoid : Elem item [] -> Void
  elemNilVoid Here impossible
  elemNilVoid (There later) impossible
removeExactActorFromInactivePlan {name} {key} {world} {error} {value}
  nameEq removedActor source target
  (DeleteInactiveLeaf headActor headComponent headParent headRetired headTable
    headOutcome headFound headNoChild rest) present actorNoChild
  with (decEq @{nameEq} removedActor headActor)
  removeExactActorFromInactivePlan nameEq headActor source target
    (DeleteInactiveLeaf headActor headComponent headParent headRetired headTable
      headOutcome headFound headNoChild rest) present actorNoChild | Yes Refl =
      let 0 outsideCommute : (actor : name) ->
            ActorOutsideDeletionPlan actor
              (DeleteInactiveLeaf {fibers = source} {target = target} headActor
                headComponent headParent headRetired headTable headOutcome
                headFound headNoChild rest) ->
            ActorOutsideDeletionPlan actor rest
          outsideCommute actor
            (ActorOutsideDeletionStep _ actorDistinct actorOutsideRest) =
              actorOutsideRest
      in MkInactivePlanUpdateCommute target rest Refl outsideCommute
  removeExactActorFromInactivePlan {name} {key} {world} {error} {value}
    nameEq removedActor source target
    (DeleteInactiveLeaf headActor headComponent headParent headRetired headTable
      headOutcome headFound headNoChild rest) present actorNoChild |
    No actorDistinctHead =
      let 0 headDistinctActor : Not (headActor = removedActor)
          headDistinctActor = unequalSymmetric actorDistinctHead
          0 tailPresent : Elem removedActor (inactivePlanActors rest)
          tailPresent = memberTailWhenHeadDistinct removedActor headActor
            actorDistinctHead (inactivePlanActors rest) present
          0 nextHeadFound : lookupFiber @{nameEq} headActor
            (deleteBinding @{nameEq} removedActor source) =
            Just (MkFiber headComponent headParent headRetired headTable
              (Inactive headOutcome))
          nextHeadFound = trans
            (lookupDeleteOther headActor removedActor headDistinctActor source)
            headFound
          0 nextHeadNoChild : hasChild @{nameEq} {name = name} {key = key}
            {value = value} {world = world} {error = error} headActor
            (deleteBinding @{nameEq} removedActor source) = False
          nextHeadNoChild = hasChildDeleteFalse nameEq headActor removedActor source
            headNoChild
          oldTailSource : Registry name key value world error
          oldTailSource = deleteBinding @{nameEq} headActor source
          canonicalTailSource : Registry name key value world error
          canonicalTailSource = deleteBinding @{nameEq} removedActor oldTailSource
          actualTailSource : Registry name key value world error
          actualTailSource = deleteBinding @{nameEq} headActor
            (deleteBinding @{nameEq} removedActor source)
          0 tailActorNoChild : hasChild @{nameEq} {name = name} {key = key}
            {value = value} {world = world} {error = error} removedActor
            oldTailSource = False
          tailActorNoChild = hasChildDeleteFalse nameEq removedActor headActor
            source actorNoChild
          0 tailCommute : InactivePlanUpdateCommute name key world error value
            nameEq rest canonicalTailSource (bindings target)
          tailCommute = removeExactActorFromInactivePlan nameEq removedActor
            oldTailSource target rest tailPresent tailActorNoChild
          0 tailSourcesSame : bindings canonicalTailSource =
            bindings actualTailSource
          tailSourcesSame = deleteBindingDistinctCommuteBindings nameEq
            removedActor headActor actorDistinctHead source
          0 transported : InactivePlanBindingsTransport name key world error value
            nameEq (commutedInactivePlan tailCommute) actualTailSource
          transported = transportInactivePlanAcrossBindings nameEq
            canonicalTailSource (commutedPlanTarget tailCommute) actualTailSource
            (commutedInactivePlan tailCommute) tailSourcesSame
          nextPlan : InactiveLeafDeletionPlan {name = name} {key = key}
            {value = value} {world = world} {error = error} nameEq
            (deleteBinding @{nameEq} removedActor source)
            (transportedPlanTarget transported)
          nextPlan = DeleteInactiveLeaf headActor headComponent headParent
            headRetired headTable headOutcome nextHeadFound nextHeadNoChild
            (transportedInactivePlan transported)
          0 targetBindings : bindings (transportedPlanTarget transported) =
            bindings target
          targetBindings = trans (sym (transportedPlanBindings transported))
            (commutedTargetBindings tailCommute)
          0 outsideCommute : (actor : name) ->
            ActorOutsideDeletionPlan actor
              (DeleteInactiveLeaf {fibers = source} {target = target} headActor
                headComponent headParent headRetired headTable headOutcome
                headFound headNoChild rest) ->
            ActorOutsideDeletionPlan actor nextPlan
          outsideCommute actor
            (ActorOutsideDeletionStep _ actorOutsideHead actorOutsideRest) =
              ActorOutsideDeletionStep (transportedInactivePlan transported)
                actorOutsideHead
                (transportedActorOutside transported actor
                  (commutedActorOutside tailCommute actor actorOutsideRest))
      in MkInactivePlanUpdateCommute (transportedPlanTarget transported) nextPlan
        targetBindings outsideCommute

0 justInjectivePlanCommute : Just left = Just right -> left = right
justInjectivePlanCommute Refl = Refl

||| Re-retiring an exact actor already erased by the plan updates that leaf in
||| place.  The replacement is not replayed in the survivor: deleting the
||| retired replacement yields the same ordered target bindings as deleting the
||| old Inactive leaf.  This case is required because the evaluator permits
||| idempotent O-Retire on an already-retired fiber.
public export
0 retireExactActorInInactivePlan :
  (nameEq : DecEq name) ->
  (retiredActor : name) ->
  (oldFiber : Fiber name key value world error) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key}
    {value = value} {world = world} {error = error} nameEq source target) ->
  ActorDeletedByInactivePlan {name = name} {key = key} {value = value}
    {world = world} {error = error} retiredActor plan ->
  (0 found : lookupFiber @{nameEq} retiredActor source = Just oldFiber) ->
  InactivePlanUpdateCommute name key world error value nameEq plan
    (replaceBinding @{nameEq} retiredActor (retireFiber oldFiber) source)
    (bindings target)
retireExactActorInInactivePlan nameEq retiredActor oldFiber source source
  NoInactiveLeafDeletion present found = void (elemNilVoid present)
  where
  0 elemNilVoid : Elem item [] -> Void
  elemNilVoid Here impossible
  elemNilVoid (There later) impossible
retireExactActorInInactivePlan {name} {key} {world} {error} {value}
  nameEq retiredActor oldFiber source target
  (DeleteInactiveLeaf headActor headComponent headParent headRetired headTable
    headOutcome headFound headNoChild rest) present found
  with (decEq @{nameEq} retiredActor headActor)
  retireExactActorInInactivePlan nameEq headActor oldFiber source target
    (DeleteInactiveLeaf headActor headComponent headParent headRetired headTable
      headOutcome headFound headNoChild rest) present found | Yes Refl =
      let 0 sameOld :
            (the (Fiber name key value world error) oldFiber =
              MkFiber headComponent headParent headRetired headTable
                (Inactive headOutcome))
          sameOld = justInjectivePlanCommute (trans (sym found) headFound)
      in case sameOld of
        Refl =>
          let nextFiber : Fiber name key value world error
              nextFiber = MkFiber headComponent headParent True headTable
                (Inactive headOutcome)
              updatedSource : Registry name key value world error
              updatedSource = replaceBinding @{nameEq} headActor nextFiber source
              actualTailSource : Registry name key value world error
              actualTailSource = deleteBinding @{nameEq} headActor updatedSource
              oldTailSource : Registry name key value world error
              oldTailSource = deleteBinding @{nameEq} headActor source
              0 tailsSame : bindings oldTailSource = bindings actualTailSource
              tailsSame = sym (deleteBindingAfterSameReplaceBindings nameEq
                headActor nextFiber source)
              0 transported : InactivePlanBindingsTransport name key world error
                value nameEq rest actualTailSource
              transported = transportInactivePlanAcrossBindings nameEq
                oldTailSource target actualTailSource rest tailsSame
              0 nextFound : lookupFiber @{nameEq} headActor updatedSource =
                Just nextFiber
              nextFound = lookupReplacedFiber headActor
                (MkFiber headComponent headParent headRetired headTable
                  (Inactive headOutcome)) nextFiber source headFound
              0 nextNoChild : hasChild @{nameEq} {name = name} {key = key}
                {value = value} {world = world} {error = error} headActor
                updatedSource = False
              nextNoChild = hasChildReplaceFalse nameEq headActor headActor
                nextFiber
                (MkFiber headComponent headParent headRetired headTable
                  (Inactive headOutcome)) source headFound Refl headNoChild
              nextPlan : InactiveLeafDeletionPlan {name = name} {key = key}
                {value = value} {world = world} {error = error} nameEq
                updatedSource (transportedPlanTarget transported)
              nextPlan = DeleteInactiveLeaf headActor headComponent headParent
                True headTable headOutcome nextFound nextNoChild
                (transportedInactivePlan transported)
              0 targetBindings : bindings (transportedPlanTarget transported) =
                bindings target
              targetBindings = sym (transportedPlanBindings transported)
              0 outsideCommute : (actor : name) ->
                ActorOutsideDeletionPlan actor
                  (DeleteInactiveLeaf {fibers = source} {target = target}
                    headActor headComponent headParent headRetired headTable
                    headOutcome headFound headNoChild rest) ->
                ActorOutsideDeletionPlan actor nextPlan
              outsideCommute actor
                (ActorOutsideDeletionStep _ actorDistinct actorOutsideRest) =
                  ActorOutsideDeletionStep (transportedInactivePlan transported)
                    actorDistinct
                    (transportedActorOutside transported actor actorOutsideRest)
          in MkInactivePlanUpdateCommute (transportedPlanTarget transported)
            nextPlan targetBindings outsideCommute
  retireExactActorInInactivePlan {name} {key} {world} {error} {value}
    nameEq retiredActor oldFiber source target
    (DeleteInactiveLeaf headActor headComponent headParent headRetired headTable
      headOutcome headFound headNoChild rest) present found |
    No actorDistinctHead =
      let 0 headDistinctActor : Not (headActor = retiredActor)
          headDistinctActor = unequalSymmetric actorDistinctHead
          0 tailPresent : Elem retiredActor (inactivePlanActors rest)
          tailPresent = memberTailWhenHeadDistinct retiredActor headActor
            actorDistinctHead (inactivePlanActors rest) present
          0 tailFound : lookupFiber @{nameEq} retiredActor
            (deleteBinding @{nameEq} headActor source) = Just oldFiber
          tailFound = trans
            (lookupDeleteOther retiredActor headActor actorDistinctHead source)
            found
          oldTailSource : Registry name key value world error
          oldTailSource = deleteBinding @{nameEq} headActor source
          canonicalTailSource : Registry name key value world error
          canonicalTailSource = replaceBinding @{nameEq} retiredActor
            (retireFiber oldFiber) oldTailSource
          actualTailSource : Registry name key value world error
          actualTailSource = deleteBinding @{nameEq} headActor
            (replaceBinding @{nameEq} retiredActor (retireFiber oldFiber) source)
          0 tailCommute : InactivePlanUpdateCommute name key world error value
            nameEq rest canonicalTailSource (bindings target)
          tailCommute = retireExactActorInInactivePlan nameEq retiredActor
            oldFiber oldTailSource target rest tailPresent tailFound
          0 tailSourcesSame : bindings canonicalTailSource =
            bindings actualTailSource
          tailSourcesSame = trans
            (replaceBindingRuntimeBindings nameEq retiredActor
              (retireFiber oldFiber) oldTailSource)
            (sym (deleteBindingAfterDistinctReplaceBindings nameEq retiredActor
              headActor actorDistinctHead (retireFiber oldFiber) source))
          0 transported : InactivePlanBindingsTransport name key world error
            value nameEq (commutedInactivePlan tailCommute) actualTailSource
          transported = transportInactivePlanAcrossBindings nameEq
            canonicalTailSource (commutedPlanTarget tailCommute) actualTailSource
            (commutedInactivePlan tailCommute) tailSourcesSame
          0 nextHeadFound : lookupFiber @{nameEq} headActor
            (replaceBinding @{nameEq} retiredActor (retireFiber oldFiber)
              source) =
            Just (MkFiber headComponent headParent headRetired headTable
              (Inactive headOutcome))
          nextHeadFound = trans
            (lookupReplaceOther headActor retiredActor headDistinctActor
              (retireFiber oldFiber) source) headFound
          0 nextHeadNoChild : hasChild @{nameEq} {name = name} {key = key}
            {value = value} {world = world} {error = error} headActor
            (replaceBinding @{nameEq} retiredActor (retireFiber oldFiber)
              source) = False
          nextHeadNoChild = hasChildReplaceFalse nameEq headActor retiredActor
            (retireFiber oldFiber) oldFiber source found
            (fiberParentRetireHint oldFiber) headNoChild
          nextPlan : InactiveLeafDeletionPlan {name = name} {key = key}
            {value = value} {world = world} {error = error} nameEq
            (replaceBinding @{nameEq} retiredActor (retireFiber oldFiber) source)
            (transportedPlanTarget transported)
          nextPlan = DeleteInactiveLeaf headActor headComponent headParent
            headRetired headTable headOutcome nextHeadFound nextHeadNoChild
            (transportedInactivePlan transported)
          0 targetBindings : bindings (transportedPlanTarget transported) =
            bindings target
          targetBindings = trans (sym (transportedPlanBindings transported))
            (commutedTargetBindings tailCommute)
          0 outsideCommute : (actor : name) ->
            ActorOutsideDeletionPlan actor
              (DeleteInactiveLeaf {fibers = source} {target = target} headActor
                headComponent headParent headRetired headTable headOutcome
                headFound headNoChild rest) ->
            ActorOutsideDeletionPlan actor nextPlan
          outsideCommute actor
            (ActorOutsideDeletionStep _ actorOutsideHead actorOutsideRest) =
              ActorOutsideDeletionStep (transportedInactivePlan transported)
                actorOutsideHead
                (transportedActorOutside transported actor
                  (commutedActorOutside tailCommute actor actorOutsideRest))
      in MkInactivePlanUpdateCommute (transportedPlanTarget transported) nextPlan
        targetBindings outsideCommute
