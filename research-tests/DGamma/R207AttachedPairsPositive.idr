module DGamma.R207AttachedPairsPositive

import DGamma.Core
import DGamma.Effects
import DGamma.Unified
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.Section3Example
import DGamma.CP5O19AttachedPairsSpike
import DGamma.R206AttachedGrammarPositive
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Apply the total 49-product observer to ANY two ACTUAL edges of the native
||| R206 release/forced-insert/root-retire/root-remove body. This is source
||| classification, not an assumption that this body is a sanctioned block.
export
0 r207ObserveEveryAttachedPair :
  {leftBefore, leftAfter, rightBefore, rightAfter : SystemState Nat ToyKey ToyValue ToyRuntime String} ->
  (left : Transition leftBefore leftAfter) -> (right : Transition rightBefore rightAfter) ->
  OccursIn left (MoreTransitions r206ReleaseEdge (MoreTransitions r206RootInsertEdge
    (MoreTransitions r206RootRetireEdge (MoreTransitions r206RootRemoveEdge NoTransitions)))) ->
  OccursIn right (MoreTransitions r206ReleaseEdge (MoreTransitions r206RootInsertEdge
    (MoreTransitions r206RootRetireEdge (MoreTransitions r206RootRemoveEdge NoTransitions)))) ->
  O19AttachedSourcePair Nat ToyKey ToyRuntime String ToyValue (the (DecEq Nat) %search) 0 0
    (MoreTransitions r206ReleaseEdge (MoreTransitions r206RootInsertEdge
      (MoreTransitions r206RootRetireEdge (MoreTransitions r206RootRemoveEdge NoTransitions))))
    (MoreTransitions r206ReleaseEdge (MoreTransitions r206RootInsertEdge
      (MoreTransitions r206RootRetireEdge (MoreTransitions r206RootRemoveEdge NoTransitions)))) left right
r207ObserveEveryAttachedPair = o19ObserveAttachedPair (the (DecEq Nat) %search) 0 0
  (MoreTransitions r206ReleaseEdge (MoreTransitions r206RootInsertEdge
    (MoreTransitions r206RootRetireEdge (MoreTransitions r206RootRemoveEdge NoTransitions))))
  (MoreTransitions r206ReleaseEdge (MoreTransitions r206RootInsertEdge
    (MoreTransitions r206RootRetireEdge (MoreTransitions r206RootRemoveEdge NoTransitions))))
  r206AttachedControlsShape r206AttachedControlsShape

||| Two concrete non-legacy products: child Remove/forced Root Insert and
||| same-bundle Root Retire/Root Remove. All four source edges are selected.
export
0 r207ConcreteAttachedPairs :
  (O19AttachedSourcePair Nat ToyKey ToyRuntime String ToyValue (the (DecEq Nat) %search) 0 0
    (MoreTransitions r206ReleaseEdge (MoreTransitions r206RootInsertEdge
      (MoreTransitions r206RootRetireEdge (MoreTransitions r206RootRemoveEdge NoTransitions))))
    (MoreTransitions r206ReleaseEdge (MoreTransitions r206RootInsertEdge
      (MoreTransitions r206RootRetireEdge (MoreTransitions r206RootRemoveEdge NoTransitions)))) r206ReleaseEdge r206RootInsertEdge,
   O19AttachedSourcePair Nat ToyKey ToyRuntime String ToyValue (the (DecEq Nat) %search) 0 0
    (MoreTransitions r206ReleaseEdge (MoreTransitions r206RootInsertEdge
      (MoreTransitions r206RootRetireEdge (MoreTransitions r206RootRemoveEdge NoTransitions))))
    (MoreTransitions r206ReleaseEdge (MoreTransitions r206RootInsertEdge
      (MoreTransitions r206RootRetireEdge (MoreTransitions r206RootRemoveEdge NoTransitions)))) r206RootRetireEdge r206RootRemoveEdge)
r207ConcreteAttachedPairs =
  (r207ObserveEveryAttachedPair r206ReleaseEdge r206RootInsertEdge OccursHere (OccursLater OccursHere),
   r207ObserveEveryAttachedPair r206RootRetireEdge r206RootRemoveEdge
     (OccursLater (OccursLater OccursHere)) (OccursLater (OccursLater (OccursLater OccursHere))))

||| The root control's early applicability is NOT a consequence of its source
||| class: before its own insertion neither retirement nor removal can fire.
export
0 r207RootControlsNotEnabledBeforeBirth :
  (checkedApplyAction @{the (DecEq Nat) %search} @{the (DecEq ToyKey) %search}
    (ORetire 2) r206Released = Nothing,
   checkedApplyAction @{the (DecEq Nat) %search} @{the (DecEq ToyKey) %search}
    (ORemove 2) r206Released = Nothing)
r207RootControlsNotEnabledBeforeBirth = (Refl, Refl)
