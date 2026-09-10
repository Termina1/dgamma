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
