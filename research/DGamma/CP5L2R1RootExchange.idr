module DGamma.CP5L2R1RootExchange

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| An AUTHENTICATED adjacent root-insert exchange, not an applicability oracle
||| or a proof that all distinct actions commute. The R178 crossed interval
||| checks source AND destination declaration availability and no root input.
||| Producers still discharge both alternate native checked equations.
public export
record AvailabilityRootExchange
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (root : name) (component : Component key value world error)
  {first, middle, finalState : SystemState name key value world error}
  (left : Transition first middle) (right : Transition middle finalState) where
  constructor MkAvailabilityRootExchange
  0 rootSwapDistinct : Not (root = transitionActor left)
  0 rootSwapAction : transitionAction right = OInsert root Root component
  0 rootSwapCutCompatible : DGamma.CP5AvailabilityAwarePlacement.rootCutCompatible name key world error value
    nameEq keyEq component 0
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep first left NoTransitions (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd middle)) = True
  rootSwapMiddle : SystemState name key value world error
  0 rootSwapEarlyChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert root Root component) first = Just (OInsertTag, rootSwapMiddle)
  0 rootSwapLaterChecked : checkedApplyAction @{nameEq} @{keyEq}
    (transitionAction left) rootSwapMiddle = Just (transitionTag left, finalState)

||| Execute a produced root square between unchanged physical prefix/suffix.
||| The literal source endpoint is preserved; there is no suffix replay oracle.
public export
rootExchangeInContext :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {root : name} -> {component : Component key value world error} ->
  {initial, first, middle, cut, finalState : SystemState name key value world error} ->
  (earlier : Transitions initial first) ->
  (left : Transition first middle) -> (right : Transition middle cut) ->
  (later : Transitions cut finalState) ->
  AvailabilityRootExchange name key world error value nameEq keyEq root component left right ->
  Transitions initial finalState
rootExchangeInContext {nameEq} {keyEq} {root} {component} earlier left right later
  (MkAvailabilityRootExchange distinct rootAction compatible moved earlyChecked laterChecked) =
  appendTransitions earlier
    (MoreTransitions (Fired nameEq keyEq (OInsert root Root component) OInsertTag earlyChecked)
      (MoreTransitions (Fired nameEq keyEq (transitionAction left) (transitionTag left) laterChecked) later))

||| Executable lifecycle-before-root-BIRTH inversion count on an actual-state
||| trace. `prior` is the count of earlier lifecycle edges. Blocked inversions
||| may remain in a normal form: zero is NOT claimed by R178 availability.
public export
rootBirthInversions :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  Nat -> DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace -> Nat
rootBirthInversions prior (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd state) = 0
rootBirthInversions prior (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep first (Fired _ _ (OInsert root Root component) _ _) rest later) =
  prior + rootBirthInversions prior later
rootBirthInversions prior (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep first (Fired _ _ action _ _) rest later) =
  rootBirthInversions (if isLifecycleAction action then S prior else prior) later

||| Every admitted Begin/root-insert square decreases this physical inversion
||| count by EXACTLY one, with arbitrary prior lifecycle count and arbitrary
||| authentic suffix. Applicability is carried by the produced native square,
||| not inferred from a rank list. No global root-placement producer is claimed.
export
0 beginRootExchangeDecreases :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor, root : name) ->
  (component : Component key value world error) ->
  (first, middle, cut, finalState : SystemState name key value world error) ->
  (0 beforeBegin : checkedApplyAction @{nameEq} @{keyEq} (LBegin actor) first = Just (LBeginTag, middle)) ->
  (0 beforeRoot : checkedApplyAction @{nameEq} @{keyEq} (OInsert root Root component) middle = Just (OInsertTag, cut)) ->
  (exchange : AvailabilityRootExchange name key world error value nameEq keyEq root component
    (Fired {before = first} {afterState = middle} nameEq keyEq (LBegin actor) LBeginTag beforeBegin) (Fired {before = middle} {afterState = cut} nameEq keyEq (OInsert root Root component) OInsertTag beforeRoot)) ->
  {0 rest : Transitions cut finalState} ->
  (later : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value rest) -> (prior : Nat) ->
  rootBirthInversions prior
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep first (Fired {before = first} {afterState = middle} nameEq keyEq (LBegin actor) LBeginTag beforeBegin) (MoreTransitions (Fired {before = middle} {afterState = cut} nameEq keyEq (OInsert root Root component) OInsertTag beforeRoot) rest)
      (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep middle (Fired {before = middle} {afterState = cut} nameEq keyEq (OInsert root Root component) OInsertTag beforeRoot) rest later)) =
  S (rootBirthInversions prior
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep first (Fired {before = first} {afterState = rootSwapMiddle exchange} nameEq keyEq (OInsert root Root component) OInsertTag (rootSwapEarlyChecked exchange)) (MoreTransitions (Fired {before = rootSwapMiddle exchange} {afterState = cut} nameEq keyEq (LBegin actor) LBeginTag (rootSwapLaterChecked exchange)) rest)
      (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (rootSwapMiddle exchange) (Fired {before = rootSwapMiddle exchange} {afterState = cut} nameEq keyEq (LBegin actor) LBeginTag (rootSwapLaterChecked exchange)) rest later)))
beginRootExchangeDecreases nameEq keyEq actor root component first middle cut finalState
  beforeBegin beforeRoot exchange later prior = Refl
