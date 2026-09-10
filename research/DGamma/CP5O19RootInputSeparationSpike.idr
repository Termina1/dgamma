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

||| The three diagonal root-input products. There is deliberately NO
||| constructor for the six mixed Insert/Retire/Remove products, nor for
||| distinct owners in a diagonal product.
public export
data O19RootHeadAgreement :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  Action name key value world error -> Action name key value world error -> Type where
  RootInsertAgreement :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {root : name} -> {component : Component key value world error} ->
    O19RootHeadAgreement (OInsert root Root component) (OInsert root Root component)
  RootRetireAgreement :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {root : name} -> O19RootHeadAgreement {name} {key} {world} {error} {value}
      (ORetire root) (ORetire root)
  RootRemoveAgreement :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {root : name} -> O19RootHeadAgreement {name} {key} {world} {error} {value}
      (ORemove root) (ORemove root)

||| SameExternalOrchestration determines the root/root product WITHOUT a
||| block-separation assumption: only the three exact diagonal products can
||| be related. Thus all six mixed products are excluded even for one owner;
||| each diagonal also forces identical root names (and Insert components).
export
0 o19RootInputProductAgreement :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {leftFirst, leftMiddle, leftLast, rightFirst, rightMiddle, rightLast : SystemState name key value world error} ->
  (left : Transition leftFirst leftMiddle) -> (right : Transition rightFirst rightMiddle) ->
  (leftRest : Transitions leftMiddle leftLast) -> (rightRest : Transitions rightMiddle rightLast) ->
  RootOrchestrationStep nameEq left -> RootOrchestrationStep nameEq right ->
  SameExternalOrchestration nameEq (MoreTransitions left leftRest) (MoreTransitions right rightRest) ->
  O19RootHeadAgreement (transitionAction left) (transitionAction right)
o19RootInputProductAgreement left right leftRest rightRest leftRoot rightRoot same =
  rewrite sym (o19AttachedRootHeadsSame left right leftRest rightRest leftRoot rightRoot same) in
    case leftRoot of
      RootInsertStep exact => rewrite exact in RootInsertAgreement
      RootRetireStep fiber found parent exact => rewrite exact in RootRetireAgreement
      RootRemoveStep fiber found parent exact => rewrite exact in RootRemoveAgreement

||| Each of the three admissible products names the identical root owner.
export
0 o19RootHeadOwnerEqual :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {left, right : Action name key value world error} ->
  O19RootHeadAgreement left right -> actionOwner left = actionOwner right
o19RootHeadOwnerEqual RootInsertAgreement = Refl
o19RootHeadOwnerEqual RootRetireAgreement = Refl
o19RootHeadOwnerEqual RootRemoveAgreement = Refl

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
