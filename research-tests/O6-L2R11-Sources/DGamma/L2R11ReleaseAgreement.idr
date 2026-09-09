module DGamma.L2R11ReleaseAgreement

import Prelude.Types
import Prelude.Interfaces
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3Attached
import DGamma.L2R6ForcedScan
import DGamma.L2R8ReleaseScan
import DGamma.L2R9OrdinalScan
import DGamma.L2R9OrdinalLink
import DGamma.L2R10ReleaseAgreement
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core
import Decidable.Decidable

%default total
%unbound_implicits off

||| Whole declaration-list overlap agreement with the library's actual
||| foldl accumulator. Native decisions remain owned by releaseScanAgrees.
||| any is foldl, NOT the right-recursive Boolean fold.
export
0 releaseOverlapAgrees : {key : Type} -> (keyEq : DecEq key) ->
  (left, right : List key) -> (accumulator : Bool) ->
  foldl (\acc, item => acc || isYes (isElem @{keyEq} item right)) accumulator left =
  foldl (\acc, item => acc || elemDec @{keyEq} item right) accumulator left
releaseOverlapAgrees keyEq [] right accumulator = Refl
releaseOverlapAgrees keyEq (head :: tail) right accumulator =
  rewrite releaseScanAgrees keyEq head right in
  releaseOverlapAgrees keyEq tail right (accumulator || elemDec @{keyEq} head right)
