module DGamma.CP5O19CartesianSitePlanSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5O19OrdinalPlanSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19ReplayObservationSpike
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| The actual adjacent transposition SITES, in execution order, extracted
||| structurally from the real finite chain. No action word approximation.
public export
0 o19CrossingSites :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} -> {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> {target : Transitions initial targetFinal} ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq source target -> List Nat
o19CrossingSites FiniteAdjacentSwapDone = []
o19CrossingSites (FiniteAdjacentSwapStep current earlier left right later orientation diamond result target rest) =
  transitionCount earlier :: o19CrossingSites rest

||| Actual finite-chain append concatenates its actual site words. This
||| structural law is the row/column splice bridge, not a node-count bound.
export
0 o19AppendFiniteSites :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} -> {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, sourceFinal, middleFinal, targetFinal : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> {middle : Transitions initial middleFinal} -> {target : Transitions initial targetFinal} ->
  (first : FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq source middle) ->
  (second : FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq middle target) ->
  (o19CrossingSites (o19AppendFinite first second) = o19CrossingSites first ++ o19CrossingSites second)
o19AppendFiniteSites FiniteAdjacentSwapDone second = Refl
o19AppendFiniteSites (FiniteAdjacentSwapStep current earlier left right later orientation diamond result target rest) second =
  cong ((transitionCount earlier) ::) (o19AppendFiniteSites rest second)

||| Execute an explicit site word numerically, retaining both true source
||| coordinates at each crossing and updating the ordinal map by that exact
||| adjacent transposition. The actual-plan connection is proved below.
public export
o19OriginsAtSites : (Nat -> Nat) -> List Nat -> List (Nat, Nat)
o19OriginsAtSites originalMap [] = []
o19OriginsAtSites originalMap (point :: rest) =
  (originalMap point, originalMap (S point)) ::
    o19OriginsAtSites (\position => originalMap (fst (adjacentSwapOrdinalExhaustive point position))) rest

||| The actual GLOBAL plan's coordinate list equals numerical execution of
||| its ACTUAL site word. Structural induction uses the producer-owned D4
||| equation on the explicit recursively produced tail, never a Refl claim
||| about a nested Cartesian builder. Equal labels play no role.
export
0 o19GlobalPlanSites :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} -> {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, sourceFinal, currentFinal, targetFinal : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> {current : Transitions initial currentFinal} -> {target : Transitions initial targetFinal} ->
  (correspondence : ActionRegistrationReplayCorrespondence name key world error value source current) ->
  (currentMap : O19OrdinalActionMap name key world error value source current correspondence) ->
  (derivation : FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq current target) ->
  (globalCrossingPositions (o19BuildGlobalOriginPlan correspondence currentMap derivation) =
    o19OriginsAtSites (ordinalOrigin currentMap) (o19CrossingSites derivation))
o19GlobalPlanSites correspondence currentMap FiniteAdjacentSwapDone = Refl
o19GlobalPlanSites correspondence currentMap
  (FiniteAdjacentSwapStep current earlier left right later orientation diamond result target rest) =
    trans (o19GlobalPlanPrependPositions current earlier left right later orientation diamond result target rest correspondence currentMap
      (o19BuildGlobalOriginPlan
        (composeActionRegistrationReplayCorrespondence correspondence (swappedOccurrenceCorrespondence result))
        (o19OrdinalMapAfterNode correspondence currentMap earlier left right later diamond result) rest))
      (cong ((ordinalOrigin currentMap (transitionCount earlier), ordinalOrigin currentMap (S (transitionCount earlier))) ::)
        (o19GlobalPlanSites
          (composeActionRegistrationReplayCorrespondence correspondence (swappedOccurrenceCorrespondence result))
          (o19OrdinalMapAfterNode correspondence currentMap earlier left right later diamond result) rest))

||| Expected sites for bubbling the last right transition across an explicit
||| left spine. The rightmost left node crosses first, so the sites descend.
||| The actual row connection is proved in the row producer's owning module.
public export
o19RowSites : Nat -> Nat -> List Nat
o19RowSites start Z = []
o19RowSites start (S width) = o19RowSites (S start) width ++ [start]
