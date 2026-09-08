module DGamma.CP5O20LinearExtensionSpike

import DGamma.Core
import DGamma.Coeffects
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

||| Strict finite order is asymmetric on the ACTUAL unique enumeration.
||| The proof inspects only list/order constructors, not a swap/effect builder.
export
0 o20BeforeAsymmetric :
  {name : Type} -> {left, right : name} -> {order : List name} ->
  UniqueKeys order -> BeforeIn left right order -> Not (BeforeIn right left order)
o20BeforeAsymmetric (UniqueCons absent unique) (BeforeHere later) (BeforeHere earlier) = absent later
o20BeforeAsymmetric (UniqueCons absent unique) (BeforeHere later) (BeforeThere earlier) =
  absent (snd (o20BeforeMembers earlier))
o20BeforeAsymmetric (UniqueCons absent unique) (BeforeThere later) (BeforeHere earlier) =
  absent (snd (o20BeforeMembers later))
o20BeforeAsymmetric (UniqueCons absent unique) (BeforeThere later) (BeforeThere earlier) =
  o20BeforeAsymmetric unique later earlier
