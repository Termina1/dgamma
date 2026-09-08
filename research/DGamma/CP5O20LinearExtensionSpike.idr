module DGamma.CP5O20LinearExtensionSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5O20SafeBlockSelectionSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Both exact finite-list members are produced by actual order evidence.
export
0 o20BeforeMembers :
  {name : Type} -> {left, right : name} -> {order : List name} ->
  BeforeIn left right order -> (Elem left order, Elem right order)
o20BeforeMembers (BeforeHere later) = (Here, There later)
o20BeforeMembers (BeforeThere later) =
  (There (fst (o20BeforeMembers later)), There (snd (o20BeforeMembers later)))
