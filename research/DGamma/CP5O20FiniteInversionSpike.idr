module DGamma.CP5O20FiniteInversionSpike

import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O20LinearExtensionSpike
import Data.List
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Pure finite inversion availability capital. It owns the precise adjacent
||| swap and reverse goal order, but does NOT assert actual block safety.
public export
record O20FiniteInversion (name : Type) (sourceOrder, goalOrder : List name) where
  constructor MkO20FiniteInversion
  0 invertedOrder : List name
  0 invertedSwap : AdjacentActorOrderSwap name sourceOrder invertedOrder
  0 invertedGoalBefore : BeforeIn (actorRight invertedSwap) (actorLeft invertedSwap) goalOrder

||| A later inversion remains the SAME selected pair under a source head.
export
0 o20InversionUnderSourceHead :
  {name : Type} -> {sourceOrder, goalOrder : List name} -> (head : name) ->
  O20FiniteInversion name sourceOrder goalOrder -> O20FiniteInversion name (head :: sourceOrder) goalOrder
o20InversionUnderSourceHead head
  (MkO20FiniteInversion target (MkAdjacentActorOrderSwap leading left right trailing beforeExact afterExact distinct) reverseOrder) =
    MkO20FiniteInversion (head :: target)
      (MkAdjacentActorOrderSwap (head :: leading) left right trailing
        (cong (head ::) beforeExact) (cong (head ::) afterExact) distinct) reverseOrder
