module DGamma.L2R9OrdinalScan

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3Attached
import DGamma.L2R8SharedKey
import DGamma.L2R8ReleaseScan
import Data.List
import Data.List.Elem
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Runtime head ordinal observation over the SAME isElem overlap as L2R8.
||| The Bool is eliminated before any consumer constructs guard-indexed data.
public export
overlapOrdinals : {key : Type} -> (keyEq : DecEq key) ->
  (left, right : List key) -> (seen : Bool) ->
  (0 equation : any (\item => isYes (isElem @{keyEq} item right)) left = seen) -> List Nat
overlapOrdinals keyEq left right True equation = [0]
overlapOrdinals keyEq left right False equation = []
