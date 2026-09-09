module DGamma.L2R6FrontNormal

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3Attached
import DGamma.L2R3AttachedGap
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Latest matching birth occurrence at/before the action cut. None denotes
||| an initially installed root. Raw-name reuse does not select the first
||| birth. General agreement with the accepted generation scanner is OPEN.
public export
rootOriginAt : {name, key, world, error : Type} -> {value : key -> Type} ->
  DecEq name -> name -> Nat -> List (RootCatalogEntry name key world error value) -> Maybe Nat
rootOriginAt nameEq actor cut catalog = map pred (lastReleaseCut
  (map catalogOrdinal (filter (\entry => catalogOrdinal entry <= cut &&
    isYes (decEq @{nameEq} actor (catalogRoot entry))) catalog)))

||| Test whether the observed birth origin has an assigned release anchor.
||| Initially installed roots have no in-trace forced origin. Equivalence
||| with the independent inductive ForcedOnTrace classifier remains owed.
public export
originForced : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  DecEq name -> DecEq key -> AvailabilityTrace name key world error value trace -> Maybe Nat -> Bool
originForced nameEq keyEq trail Nothing = False
originForced nameEq keyEq trail (Just ordinal) = isJust (anchorOf nameEq keyEq trail ordinal)

||| Retire/Remove tag observation; root status still requires the ACTUAL
||| source-state rootInputAtSource test. This does not classify children roots.
public export
rootControlAction : {name, key, world, error : Type} -> {value : key -> Type} ->
  Action name key value world error -> Bool
rootControlAction (ORetire actor) = True
rootControlAction (ORemove actor) = True
rootControlAction (OInsert actor parent component) = False
rootControlAction (LBegin actor) = False
rootControlAction (LAdvance actor) = False
rootControlAction (LDivert actor) = False
rootControlAction (LUnload actor) = False
rootControlAction (LLeave actor) = False

||| Combine two head conditions with one observed tail result. Single tuple
||| elimination avoids duplicating the recursive native scan.
public export
frontControlHead : Bool -> Bool -> (Bool, Bool) -> (Bool, Bool)
frontControlHead frontOK controlOK (tailFront, tailControl) =
  (frontOK && tailFront, controlOK && tailControl)

||| Total actual-trace scan: (all non-forced root orchestration is before the
||| first lifecycle, no forced root Retire/Remove). Retire/Remove root status
||| uses the native source; birth generation uses the latest catalog ordinal.
||| Whole/traversed traces are separate solely to retain the original catalog.
public export
scanFrontDisposition : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 initial, finalState, first, lastState : SystemState name key value world error} ->
  {0 global : Transitions initial finalState} -> {0 trace : Transitions first lastState} ->
  DecEq name -> DecEq key -> AvailabilityTrace name key world error value global ->
  Nat -> Bool -> AvailabilityTrace name key world error value trace -> (Bool, Bool)
scanFrontDisposition nameEq keyEq whole ordinal seen (AvailabilityEnd state) = (True, True)
scanFrontDisposition {name} {key} {world} {error} {value} nameEq keyEq whole ordinal seen
  (AvailabilityStep source (Fired ne ke action tag checked) rest later) = frontControlHead
    (not (seen && rootInputAtSource name key world error value nameEq action source &&
      not (originForced nameEq keyEq whole (rootOriginAt nameEq (actionOwner action) ordinal (scanRootCatalog 0 whole)))))
    (not (rootControlAction action && rootInputAtSource name key world error value nameEq action source &&
      originForced nameEq keyEq whole (rootOriginAt nameEq (actionOwner action) ordinal (scanRootCatalog 0 whole))))
    (scanFrontDisposition nameEq keyEq whole (S ordinal) (seen || isLifecycleAction action) later)

||| Accepted front-normal scan with explicit observed Bool and producer-owned
||| equation. General correspondence to ForcedOnTrace/generation-origin
||| proofs is NOT implied merely by accepting this executable predicate.
public export
record FrontNormal
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {0 first, finalState : SystemState name key value world error}
  {0 trace : Transitions first finalState}
  (trail : AvailabilityTrace name key world error value trace) where
  constructor MkFrontNormal
  frontObserved : Bool
  0 frontEquation : fst (scanFrontDisposition nameEq keyEq trail 0 False trail) = frontObserved
  0 frontAccepted : frontObserved = True

||| The no-forced-control option, explicitly checked by the total native
||| scan. It is not imposed on all quiescent traces by fiat; the paper's
||| open-set/lifecycle argument still owes this disposition when applicable.
public export
record ForcedRootNeverRetired
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {0 first, finalState : SystemState name key value world error}
  {0 trace : Transitions first finalState}
  (trail : AvailabilityTrace name key world error value trace) where
  constructor MkForcedRootNeverRetired
  neverRetiredObserved : Bool
  0 neverRetiredEquation : snd (scanFrontDisposition nameEq keyEq trail 0 False trail) = neverRetiredObserved
  0 neverRetiredAccepted : neverRetiredObserved = True
