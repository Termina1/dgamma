module DGamma.CP4DeletionPlanRuntime

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionPlanComplete
import Decidable.Equality

%default total

0 lookupFiberBindingsCoherent :
  (nameEq : DecEq name) -> (selected : name) ->
  (left, right : Registry name key value world error) ->
  bindings left = bindings right ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} selected left =
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} selected right
lookupFiberBindingsCoherent nameEq selected
  (MkCoeffectContext leftEntries leftUnique)
  (MkCoeffectContext rightEntries rightUnique) same =
    case same of Refl => Refl

0 hasChildBindingsCoherent :
  (nameEq : DecEq name) -> (selected : name) ->
  (left, right : Registry name key value world error) ->
  bindings left = bindings right ->
  hasChild @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} selected left =
  hasChild @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} selected right
hasChildBindingsCoherent nameEq selected
  (MkCoeffectContext leftEntries leftUnique)
  (MkCoeffectContext rightEntries rightUnique) same =
    case same of Refl => Refl

0 deleteBindingBindingsCoherent :
  (nameEq : DecEq name) -> (selected : name) ->
  (left, right : Registry name key value world error) ->
  bindings left = bindings right ->
  bindings (deleteBinding @{nameEq} selected left) =
  bindings (deleteBinding @{nameEq} selected right)
deleteBindingBindingsCoherent nameEq selected
  (MkCoeffectContext leftEntries leftUnique)
  (MkCoeffectContext rightEntries rightUnique) same =
    cong (deleteEntries @{nameEq} selected) same

||| Reindex an Inactive-leaf deletion plan across equality of the complete
||| ordered runtime binding list.  The transported target retains binding-list
||| equality with the original target; no equality of `UniqueKeys` proofs is
||| required or claimed.
public export
record InactivePlanBindingsTransport
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name)
  {leftSource, leftTarget : Registry name key value world error}
  (leftPlan : InactiveLeafDeletionPlan {name = name} {key = key}
    {value = value} {world = world} {error = error} nameEq leftSource
    leftTarget)
  (rightSource : Registry name key value world error) where
  constructor MkInactivePlanBindingsTransport
  transportedPlanTarget : Registry name key value world error
  transportedInactivePlan : InactiveLeafDeletionPlan {name = name} {key = key}
    {value = value} {world = world} {error = error} nameEq rightSource
    transportedPlanTarget
  0 transportedPlanBindings : bindings leftTarget =
    bindings transportedPlanTarget
  0 transportedPlanActors : inactivePlanActors transportedInactivePlan =
    inactivePlanActors leftPlan
  0 transportedActorOutside : (actor : name) ->
    ActorOutsideDeletionPlan actor leftPlan ->
    ActorOutsideDeletionPlan actor transportedInactivePlan

||| Total plan transport through exact ordered bindings.  This is the plan-side
||| companion of evaluator runtime-snapshot transport.
public export
0 transportInactivePlanAcrossBindings :
  (nameEq : DecEq name) ->
  (leftSource, leftTarget, rightSource :
    Registry name key value world error) ->
  (leftPlan : InactiveLeafDeletionPlan {name = name} {key = key}
    {value = value} {world = world} {error = error} nameEq leftSource
    leftTarget) ->
  bindings leftSource = bindings rightSource ->
  InactivePlanBindingsTransport name key world error value nameEq leftPlan
    rightSource
transportInactivePlanAcrossBindings nameEq leftSource leftSource rightSource
  NoInactiveLeafDeletion same =
    MkInactivePlanBindingsTransport rightSource NoInactiveLeafDeletion same Refl
      (\actor, ActorOutsideDeletionEnd => ActorOutsideDeletionEnd)
transportInactivePlanAcrossBindings nameEq leftSource leftTarget rightSource
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest) same =
      let 0 rightFound : (lookupFiber @{nameEq} {name = name} {key = key}
            {value = value} {world = world} {error = error} removed rightSource =
            Just (MkFiber component parent retiredFlag table (Inactive outcome)))
          rightFound = trans (sym (lookupFiberBindingsCoherent
            {name = name} {key = key} {value = value} {world = world}
            {error = error} nameEq removed leftSource rightSource same)) found
          0 rightNoChild : (hasChild @{nameEq} {name = name} {key = key}
            {value = value} {world = world} {error = error} removed
            rightSource = False)
          rightNoChild = trans (sym (hasChildBindingsCoherent {name = name}
            {key = key} {value = value} {world = world} {error = error} nameEq
            removed leftSource rightSource same)) noChild
          leftTailSource : Registry name key value world error
          leftTailSource = deleteBinding @{nameEq} removed leftSource
          rightTailSource : Registry name key value world error
          rightTailSource = deleteBinding @{nameEq} removed rightSource
          0 tailsSame : bindings leftTailSource = bindings rightTailSource
          tailsSame = deleteBindingBindingsCoherent {name = name} {key = key}
            {value = value} {world = world} {error = error} nameEq removed
            leftSource rightSource same
          0 tailTransport : InactivePlanBindingsTransport name key world error
            value nameEq rest rightTailSource
          tailTransport = transportInactivePlanAcrossBindings nameEq
            leftTailSource leftTarget rightTailSource rest tailsSame
      in let transportedPlan : InactiveLeafDeletionPlan {name = name}
               {key = key} {value = value} {world = world} {error = error}
               nameEq rightSource (transportedPlanTarget tailTransport)
             transportedPlan = DeleteInactiveLeaf removed component parent
               retiredFlag table outcome rightFound rightNoChild
               (transportedInactivePlan tailTransport)
             0 outsideTransport : (actor : name) ->
               ActorOutsideDeletionPlan actor
                 (DeleteInactiveLeaf {fibers = leftSource}
                   {target = leftTarget} removed component parent retiredFlag
                   table outcome found noChild rest) ->
               ActorOutsideDeletionPlan actor transportedPlan
             outsideTransport actor
               (ActorOutsideDeletionStep _ oldDistinct outsideRest) =
                 ActorOutsideDeletionStep (transportedInactivePlan tailTransport)
                   oldDistinct
                   (transportedActorOutside tailTransport actor outsideRest)
         in MkInactivePlanBindingsTransport
           (transportedPlanTarget tailTransport) transportedPlan
           (transportedPlanBindings tailTransport)
           (cong (removed ::) (transportedPlanActors tailTransport))
           outsideTransport
