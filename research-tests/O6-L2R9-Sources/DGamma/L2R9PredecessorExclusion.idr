module DGamma.L2R9PredecessorExclusion

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R6FrontNormal
import DGamma.L2R6Phase
import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Maybe
import Data.Nat
import Data.Rel
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| LOCAL head algebra for the EXACT two FrontNormal/NeverRetired guards.
||| Once both actual head conjuncts are decoded, a root control after life
||| is impossible whether its origin is forced or not. General whole-scan
||| acceptance -> located-head extraction remains OPEN, not an assumed law.
||| In attachedC the forced-control alternative must instead be authenticated
||| as belonging to an earlier placed bundle; that placement lift is OPEN.
export
0 rootControlHeadExcluded : (seen, rootInput, control, forced : Bool) ->
  (0 seenAccepted : seen = True) -> (0 rootAccepted : rootInput = True) ->
  (0 controlAccepted : control = True) ->
  (0 front : not (seen && rootInput && not forced) = True) ->
  (0 never : not (control && rootInput && forced) = True) -> Void
rootControlHeadExcluded seen rootInput control False seenAccepted rootAccepted controlAccepted front never =
  absurd (replace {p = \r => not (True && r && True) = True} rootAccepted
    (replace {p = \s => not (s && rootInput && True) = True} seenAccepted front))
rootControlHeadExcluded seen rootInput control True seenAccepted rootAccepted controlAccepted front never =
  absurd (replace {p = \r => not (True && r && True) = True} rootAccepted
    (replace {p = \c => not (c && rootInput && True) = True} controlAccepted never))

||| Exact observed-guard arithmetic: a positive conditional Nat distance
||| cannot have its source ordinal at/below the external-order floor. The
||| native guard is passed with its OWN equation, never re-cased implicitly.
export
0 positiveFloorAtGuard : (ordinal, target : Nat) ->
  (condition, seen : Bool) -> (0 equation : condition = seen) ->
  (0 positive : LT 0 (if condition then minus ordinal target else 0)) ->
  (0 floor : LTE ordinal target) -> Void
positiveFloorAtGuard ordinal target False seen equation positive floor = absurd positive
positiveFloorAtGuard ordinal target True seen equation positive floor =
  absurd (transitive positive
    (replace {p = \n => LTE (minus ordinal target) n} (sym (minusZeroN target))
      (minusLteMonotone {m = ordinal} {n = target} {p = target} floor)))

||| FULL native root-BIRTH forbidden case UNDER the stated external-order
||| floor: an adjacent earlier native root cannot precede a positive-distance
||| selected catalog birth when its ending cut is at/below the actual target.
||| Front/never/phase premises retain the authorized domain; arithmetic is
||| stronger and does not need to inspect them. Deriving this floor from the
||| catalog maximum/rank remains separate, as does global control-head
||| extraction. attachedC forced controls need the earlier-placed-bundle lift.
||| Pass the ACTUAL isJust(anchorOf ...) value and Refl at the call site.
export
0 rootBirthPredecessorExcluded :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace) ->
  (entry : RootCatalogEntry name key world error value) ->
  (0 member : Elem entry (scanRootCatalog 0 trail)) ->
  (previousRoot : name) -> (previousComponent : Component key value world error) ->
  (previousBirth : LocatedActionOccurrence (OInsert previousRoot Root previousComponent) trace) ->
  (0 adjacent : catalogOrdinal entry = S (locatedActionOrdinal previousBirth)) ->
  (0 front : FrontNormal name key world error value nameEq keyEq trail) ->
  (0 never : ForcedRootNeverRetired name key world error value nameEq keyEq trail) ->
  (0 phase : ForcedRootPhase name key world error value nameEq keyEq trail entry) ->
  (0 externalFloor : LTE (S (locatedActionOrdinal previousBirth)) (targetPosition nameEq keyEq trail (catalogOrdinal entry))) ->
  (seen : Bool) -> (0 equation : isJust (anchorOf nameEq keyEq trail (catalogOrdinal entry)) = seen) ->
  (0 positive : LT 0 (rootDistance nameEq keyEq trail (catalogOrdinal entry))) -> Void
rootBirthPredecessorExcluded nameEq keyEq trail entry member previousRoot previousComponent previousBirth
  adjacent front never phase externalFloor False equation positive =
  absurd (replace {p = \n => LT 0 n}
    (the (rootDistance nameEq keyEq trail (catalogOrdinal entry) = 0) (rewrite equation in Refl)) positive)
rootBirthPredecessorExcluded nameEq keyEq trail entry member previousRoot previousComponent previousBirth
  adjacent front never phase externalFloor True equation positive =
  positiveFloorAtGuard (catalogOrdinal entry) (targetPosition nameEq keyEq trail (catalogOrdinal entry)) True True Refl
    (replace {p = \n => LT 0 n}
      (the (rootDistance nameEq keyEq trail (catalogOrdinal entry) =
        minus (catalogOrdinal entry) (targetPosition nameEq keyEq trail (catalogOrdinal entry)))
        (rewrite equation in Refl)) positive)
    (replace {p = \n => LTE n (targetPosition nameEq keyEq trail (catalogOrdinal entry))}
      (sym adjacent) externalFloor)
