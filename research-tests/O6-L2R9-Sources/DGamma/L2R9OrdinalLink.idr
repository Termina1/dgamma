module DGamma.L2R9OrdinalLink

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3Attached
import DGamma.L2R7ReleaseDecode
import DGamma.L2R8SharedKey
import DGamma.L2R8ReleaseScan
import DGamma.L2R9OrdinalScan
import Data.List
import Data.List.Elem
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Erased head linkage at the actual observed isElem overlap. Each
||| successful shared-key packet corresponds to exactly one head ordinal.
export
0 overlapOrdinalLink : {key : Type} -> (keyEq : DecEq key) ->
  (left, right : List key) -> (seen : Bool) ->
  (0 equation : any (\item => isYes (isElem @{keyEq} item right)) left = seen) ->
  map (\shared => Z) (sharedKeysObserved keyEq left right seen equation) =
    overlapOrdinals keyEq left right seen equation
overlapOrdinalLink keyEq left right True equation = Refl
overlapOrdinalLink keyEq left right False equation = Refl
