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
