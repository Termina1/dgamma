module DGamma.L2R14PhaseRelease

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3Attached
import DGamma.L2R8ReleaseScan
import DGamma.L2R9OrdinalScan
import DGamma.L2R9OrdinalLink
import DGamma.L2R10ReleaseAgreement
import DGamma.L2R12PhaseAccepted
import DGamma.L2R14PhaseSeed
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Reflect the old elemDec Bool through the CHECKED library agreement.
||| The actual isElem decision is observed once by the consuming caller.
export
0 phaseMemberAtDecision : {a : Type} -> (dictionary : DecEq a) ->
  (item : a) -> (items : List a) -> (decision : Dec (Elem item items)) ->
  (0 equation : isElem @{dictionary} item items = decision) ->
  (0 accepted : elemDec @{dictionary} item items = True) -> Elem item items
phaseMemberAtDecision dictionary item items (Yes present) equation accepted = present
phaseMemberAtDecision dictionary item items (No absent) equation accepted =
  absurd (trans (sym (cong isYes equation))
    (trans (releaseScanAgrees dictionary item items) accepted))

||| Membership transport under a shared head. Only membership is eliminated;
||| this supplies the true branch of the native filter decoder.
export
0 phaseConsInclusion : {a : Type} -> (head, item : a) -> (left, right : List a) ->
  (0 inclusion : Elem item left -> Elem item right) ->
  (0 member : Elem item (head :: left)) -> Elem item (head :: right)
phaseConsInclusion _ item left right inclusion Here = Here
phaseConsInclusion head item left right inclusion (There later) = There (inclusion later)

||| Remove one observed filter guard, preserving genuine source membership.
||| The tail continuation is structural recursion, not a membership oracle.
export
0 phaseFilterAtBool : {a : Type} -> (predicate : a -> Bool) ->
  (head, item : a) -> (rest : List a) -> (seen : Bool) ->
  (0 equation : predicate head = seen) ->
  (0 inclusion : Elem item (filter predicate rest) -> Elem item rest) ->
  (0 member : Elem item (filter predicate (head :: rest))) -> Elem item (head :: rest)
phaseFilterAtBool predicate head item rest True equation inclusion =
  rewrite equation in phaseConsInclusion head item (filter predicate rest) rest inclusion
phaseFilterAtBool predicate head item rest False equation inclusion =
  rewrite equation in \member => There (inclusion member)

||| Genuine unfiltered membership from native filter membership. Every
||| predicate Bool is observed at this structural call site.
export
0 phaseFilterMember : {a : Type} -> (predicate : a -> Bool) ->
  (item : a) -> (items : List a) ->
  (0 member : Elem item (filter predicate items)) -> Elem item items
phaseFilterMember predicate item [] member = absurd member
phaseFilterMember predicate item (head :: rest) member =
  phaseFilterAtBool predicate head item rest (predicate head) Refl
    (\later => phaseFilterMember predicate item rest later) member
