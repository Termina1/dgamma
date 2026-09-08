module DGamma.CP5O19CartesianSitePlanSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceRankObservationSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19MixedRowDispatcherSpike
import DGamma.CP5O19CartesianLengthSpike
import DGamma.CP5O19PairObservationSpike
import DGamma.CP5O19CartesianWordRowSpike
import DGamma.CP5O19ActualCartesianSpike
import DGamma.CP5O19OrdinalPlanSpike
import DGamma.CP5O19PaperBranchCompletenessSpike
import DGamma.CP5O19CartesianColumnsSpike
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| The actual adjacent transposition SITES, in execution order, extracted
||| structurally from the real finite chain. No action word approximation.
export
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
