module DGamma.L2R10ReleaseAgreement

import Prelude.Types
import Prelude.Interfaces
import DGamma.Calculus
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Equality.Core
import Decidable.Decidable

%default total
%unbound_implicits off

||| NEW absence consumer, not the exhausted elemDecConsObserved equation.
||| The library decision is supplied as its actual observed value/equation.
||| Eliminate only that Dec; the recursive absence equation is structural.
export
0 releaseAbsentAtDecision : {key : Type} -> (keyEq : DecEq key) ->
  (wanted, head : key) -> (tail : List key) ->
  (decision : Dec (wanted = head)) ->
  (0 equation : decEq @{keyEq} wanted head = decision) ->
  (0 absent : Not (Elem wanted (head :: tail))) ->
  (0 tailFalse : elemDec @{keyEq} wanted tail = False) ->
  elemDec @{keyEq} wanted (head :: tail) = False
releaseAbsentAtDecision keyEq wanted head tail (Yes same) equation absent tailFalse =
  absurd (absent (replace {p = \item => Elem item (head :: tail)} (sym same) Here))
releaseAbsentAtDecision keyEq wanted head tail (No different) equation absent tailFalse =
  rewrite equation in tailFalse

||| Structural absence fold. Observe the LIBRARY decEq at its own call site;
||| no inferred local view or re-cased library call appears in the consumer.
export
0 releaseAbsentFalse : {key : Type} -> (keyEq : DecEq key) ->
  (wanted : key) -> (keys : List key) -> (0 absent : Not (Elem wanted keys)) ->
  elemDec @{keyEq} wanted keys = False
releaseAbsentFalse keyEq wanted [] absent = Refl
releaseAbsentFalse keyEq wanted (head :: tail) absent =
  releaseAbsentAtDecision keyEq wanted head tail (decEq @{keyEq} wanted head) Refl absent
    (releaseAbsentFalse keyEq wanted tail (\member => absent (There member)))

||| Eliminate the explicitly observed Calculus.elemDec BOOL, not a projected
||| guard. The native library's false-soundness gives the impossible branch.
export
0 releasePresentAtBool : {key : Type} -> (keyEq : DecEq key) ->
  (wanted : key) -> (keys : List key) -> (seen : Bool) ->
  (0 equation : elemDec @{keyEq} wanted keys = seen) ->
  (0 present : Elem wanted keys) -> seen = True
releasePresentAtBool keyEq wanted keys False equation present =
  absurd (elemDecFalseNotElem @{keyEq} wanted keys equation present)
releasePresentAtBool keyEq wanted keys True equation present = Refl

||| Own both library observations. A single Dec elimination connects native
||| isElem truth to the observed old Bool; no old/new equality is assumed.
export
0 releaseAgreementAtDec : {key : Type} -> (keyEq : DecEq key) ->
  (wanted : key) -> (keys : List key) -> (seen : Bool) ->
  (0 oldEquation : elemDec @{keyEq} wanted keys = seen) ->
  (decision : Dec (Elem wanted keys)) ->
  (0 equation : isElem @{keyEq} wanted keys = decision) ->
  isYes (isElem @{keyEq} wanted keys) = seen
releaseAgreementAtDec keyEq wanted keys seen oldEquation (Yes present) equation =
  rewrite equation in sym (releasePresentAtBool keyEq wanted keys seen oldEquation present)
releaseAgreementAtDec keyEq wanted keys seen oldEquation (No absent) equation =
  rewrite equation in trans (sym (releaseAbsentFalse keyEq wanted keys absent)) oldEquation

||| GENERAL SINGLE-KEY agreement. Both library values are observed HERE
||| with their own native equations. This is not yet the bounded whole-trail
||| release-list theorem: overlap folding, offsets and filtering remain.
export
0 releaseScanAgrees : {key : Type} -> (keyEq : DecEq key) ->
  (wanted : key) -> (keys : List key) ->
  isYes (isElem @{keyEq} wanted keys) = elemDec @{keyEq} wanted keys
releaseScanAgrees keyEq wanted keys =
  releaseAgreementAtDec keyEq wanted keys (elemDec @{keyEq} wanted keys) Refl
    (isElem @{keyEq} wanted keys) Refl
