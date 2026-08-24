module DGamma.R11GenericRawPlanRepackagerPositive

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Metatheory
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

||| Historical copy of the revision-11 open result boundary.  The live
||| `AdjacentSwapResult` constructor is intentionally not used anywhere in this
||| module: after revision 19 it becomes producer-private.  Keeping a local copy
||| preserves the exact accepted historical claim—that fully supplied semantic
||| fields can be repackaged mechanically—without granting current O6 authority.
public export
record RetiredOpenAdjacentSwapResult
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
    SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (tracePrefix : Transitions initial pairFirst)
  (left : Transition pairFirst pairMiddle)
  (right : Transition pairMiddle pairFinal)
  (suffix : Transitions pairFinal originalFinal)
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) where
  constructor MkRetiredOpenAdjacentSwapResult
  retiredReplayedFinal : SystemState name key value world error
  retiredReplayedSuffix :
    Transitions (swappedFinal diamond) retiredReplayedFinal
  retiredSwappedTrace : Transitions initial retiredReplayedFinal
  0 retiredOriginalDecomposition : appendTransitions tracePrefix
    (MoreTransitions left (MoreTransitions right suffix)) = original
  0 retiredSwappedDecomposition : retiredSwappedTrace =
    appendTransitions tracePrefix
      (MoreTransitions (movedRight diamond)
        (MoreTransitions (movedLeft diamond) retiredReplayedSuffix))
  retiredSameExternalInputs :
    SameExternalOrchestration nameEq original retiredSwappedTrace
  retiredReplayCorrespondence : RelationalReplayCorrespondence name key world
    error value original retiredSwappedTrace
  retiredEndpoint : RelationalReplayEndpoint name key world error value nameEq
    keyEq originalFinal retiredReplayedFinal
  retiredPremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq retiredSwappedTrace

||| The revision-11 result materializer was intentionally only a raw
||| repackager.  This historical theorem keeps that claim exact: every output
||| field is supplied by the caller and placed in a local retired-open record.
||| It cannot construct the live `AdjacentSwapResult` and cannot enter O17/O19.
public export
0 materializeRetiredOpenAdjacentSwapResult :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
    SystemState name key value world error} ->
  {original : Transitions initial originalFinal} ->
  {tracePrefix : Transitions initial pairFirst} ->
  {left : Transition pairFirst pairMiddle} ->
  {right : Transition pairMiddle pairFinal} ->
  {suffix : Transitions pairFinal originalFinal} ->
  {diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right} ->
  (replayedFinal : SystemState name key value world error) ->
  (replayedSuffix : Transitions (swappedFinal diamond) replayedFinal) ->
  (swappedTrace : Transitions initial replayedFinal) ->
  appendTransitions tracePrefix
    (MoreTransitions left (MoreTransitions right suffix)) = original ->
  swappedTrace = appendTransitions tracePrefix
    (MoreTransitions (movedRight diamond)
      (MoreTransitions (movedLeft diamond) replayedSuffix)) ->
  SameExternalOrchestration nameEq original swappedTrace ->
  RelationalReplayCorrespondence name key world error value original
    swappedTrace ->
  RelationalReplayEndpoint name key world error value nameEq keyEq originalFinal
    replayedFinal ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq
    swappedTrace ->
  RetiredOpenAdjacentSwapResult name key world error value protocol nameEq keyEq
    original tracePrefix left right suffix diamond
materializeRetiredOpenAdjacentSwapResult replayedFinal replayedSuffix swappedTrace
  originalExact swappedExact external replay endpoint premises =
    MkRetiredOpenAdjacentSwapResult replayedFinal replayedSuffix swappedTrace
      originalExact swappedExact external replay endpoint premises
