module DGamma.CP5O19RootInputSeparationSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O19AttachedPairsSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Native occurrence elimination: no action-word or raw-name relabelling.
export
0 o19NoRootOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {first, last, before, afterState : SystemState name key value world error} ->
  {trace : Transitions first last} -> {step : Transition before afterState} ->
  NoRootOrchestration nameEq trace -> OccursIn step trace ->
  Not (RootOrchestrationStep nameEq step)
o19NoRootOccurrence (NoRootOrchestrationStep step rest excluded tail) OccursHere = excluded
o19NoRootOccurrence (NoRootOrchestrationStep step rest excluded tail) (OccursLater there) =
  o19NoRootOccurrence tail there

||| Candidate structural restriction for expanded whole-block producers.
||| It is NOT asserted to follow from AdjacentActorSwapSafety. At least one
||| selected native body has no external input; the other may have a nonempty
||| forced-root bundle including Retire/Remove controls. No swapped result,
||| diamond, or replay conclusion is stored in this premise.
public export
0 O19AtMostOneExternalBlock :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {leftFirst, leftLast, rightFirst, rightLast : SystemState name key value world error} ->
  (leftBody : Transitions leftFirst leftLast) ->
  (rightBody : Transitions rightFirst rightLast) -> Type
O19AtMostOneExternalBlock nameEq leftBody rightBody =
  Either (NoRootOrchestration nameEq leftBody) (NoRootOrchestration nameEq rightBody)

||| All nine root/root products are excluded by the NAMED premise, not by a
||| claim that two independent actors cannot carry external bundles.
export
0 o19SeparateRootInputOccurrences :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {leftFirst, leftLast, rightFirst, rightLast, leftBefore, leftAfter,
   rightBefore, rightAfter : SystemState name key value world error} ->
  {leftBody : Transitions leftFirst leftLast} ->
  {rightBody : Transitions rightFirst rightLast} ->
  {left : Transition leftBefore leftAfter} ->
  {right : Transition rightBefore rightAfter} ->
  O19AtMostOneExternalBlock nameEq leftBody rightBody ->
  OccursIn left leftBody -> OccursIn right rightBody ->
  RootOrchestrationStep nameEq left -> RootOrchestrationStep nameEq right -> Void
o19SeparateRootInputOccurrences (Left absent) leftIn rightIn leftRoot rightRoot =
  o19NoRootOccurrence absent leftIn leftRoot
o19SeparateRootInputOccurrences (Right absent) leftIn rightIn leftRoot rightRoot =
  o19NoRootOccurrence absent rightIn rightRoot

||| Every expanded core (including child Retire/Remove) is root-input free.
||| The control branches compare lookups at the SAME native source state.
export
0 o19ExpandedCoreNoRoot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {actor : name} ->
  {first, last : SystemState name key value world error} ->
  {core : Transitions first last} -> ActorLifecycleCore nameEq actor core ->
  NoRootOrchestration nameEq core
o19ExpandedCoreNoRoot CoreLifecycleEnd = NoRootOrchestrationEnd
o19ExpandedCoreNoRoot (CoreLifecycleStep step rest lifecycle owned tail) =
  NoRootOrchestrationStep step rest
    (\root => void (uninhabited (trans (sym lifecycle) (o19AttachedRootNonLifecycle root))))
    (o19ExpandedCoreNoRoot tail)
o19ExpandedCoreNoRoot (CoreYieldedRegistrationStep step rest inserted tail) =
  NoRootOrchestrationStep step rest (\root => case root of
    RootInsertStep exact => case trans (sym inserted) exact of Refl impossible
    RootRetireStep fiber found parent exact => case trans (sym inserted) exact of Refl impossible
    RootRemoveStep fiber found parent exact => case trans (sym inserted) exact of Refl impossible)
    (o19ExpandedCoreNoRoot tail)
o19ExpandedCoreNoRoot (CoreChildRetireStep step rest child fiber found parent controlled tail) =
  NoRootOrchestrationStep step rest (\root => case root of
    RootInsertStep exact => case trans (sym controlled) exact of Refl impossible
    RootRetireStep rootFiber rootFound rootParent exact =>
      case cong actionOwner (trans (sym controlled) exact) of
        Refl => case justInjective (trans (sym found) rootFound) of
          Refl => case trans (sym parent) rootParent of Refl impossible
    RootRemoveStep rootFiber rootFound rootParent exact => case trans (sym controlled) exact of Refl impossible)
    (o19ExpandedCoreNoRoot tail)
o19ExpandedCoreNoRoot (CoreChildRemoveStep step rest child fiber found parent controlled tail) =
  NoRootOrchestrationStep step rest (\root => case root of
    RootInsertStep exact => case trans (sym controlled) exact of Refl impossible
    RootRetireStep rootFiber rootFound rootParent exact => case trans (sym controlled) exact of Refl impossible
    RootRemoveStep rootFiber rootFound rootParent exact =>
      case cong actionOwner (trans (sym controlled) exact) of
        Refl => case justInjective (trans (sym found) rootFound) of
          Refl => case trans (sym parent) rootParent of Refl impossible)
    (o19ExpandedCoreNoRoot tail)
