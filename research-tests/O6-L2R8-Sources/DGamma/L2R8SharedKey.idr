module DGamma.L2R8SharedKey

import DGamma.L2R7ObservedAny
import DGamma.L2R7ReleaseDecode
import Data.List
import Data.List.Elem
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| New observed statement, NOT elemDecConsObserved. Eliminate the actual
||| library isElem RESULT with its call-site equation; never re-case isElem.
||| Over the isElem release scan; agreement with scanReleaseOrdinals open.
public export
0 sharedKeyDecision : {key : Type} -> (keyEq : DecEq key) ->
  (left, right : List key) -> (item : key) -> (0 member : Elem item left) ->
  (decision : Dec (Elem item right)) ->
  (0 equation : isElem @{keyEq} item right = decision) ->
  (0 accepted : isYes decision = True) -> SharedKey left right
sharedKeyDecision keyEq left right item member (Yes present) equation accepted =
  MkSharedKey item member present
sharedKeyDecision keyEq left right item member (No absent) equation accepted = absurd accepted
