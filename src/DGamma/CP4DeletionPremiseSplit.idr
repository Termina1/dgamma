module DGamma.CP4DeletionPremiseSplit

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionGenerationScan
import Data.Maybe
import Decidable.Equality

%default total

||| Split generation-indexed no-episode evidence at an exact scanner boundary.
||| The scanner fixes the ordinal/environment at the cut, preventing either
||| side from silently restarting generation numbering.
public export
0 noRegisteredEpisodeAppendSplit :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  (middleOrdinal : Nat) ->
  (middleLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq ordinal live left middleOrdinal middleLive ->
  NoRegisteredEpisode nameEq registered ordinal live
    (appendTransitions left right) ->
  (NoRegisteredEpisode nameEq registered ordinal live left,
   NoRegisteredEpisode nameEq registered middleOrdinal middleLive right)
noRegisteredEpisodeAppendSplit nameEq registered ordinal live NoTransitions right
  ordinal live GenerationTraceScanEnd noEpisodes =
    (NoRegisteredEpisodeEnd, noEpisodes)
noRegisteredEpisodeAppendSplit nameEq registered ordinal live
  (MoreTransitions (Fired stepNameEq stepKeyEq action tag checked) leftRest)
  right middleOrdinal middleLive
  (GenerationTraceScanStep
    (Fired stepNameEq stepKeyEq action tag checked) leftRest scanTail)
  (NoRegisteredEpisodeStep
    (Fired stepNameEq stepKeyEq action tag checked)
    (appendTransitions leftRest right) noBegin noTail) =
    case noRegisteredEpisodeAppendSplit nameEq registered (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal action live)
      leftRest right middleOrdinal middleLive scanTail noTail of
      (leftEvidence, rightEvidence) =>
        (NoRegisteredEpisodeStep
          (Fired stepNameEq stepKeyEq action tag checked)
          leftRest noBegin leftEvidence,
         rightEvidence)

||| Definition-69 evidence is pointwise at checked boundaries, so unlike
||| registration-retirement provenance it splits over append without any extra
||| semantic premise.
public export
0 totalAppendSplit :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  TraceComponentsTotal nameEq keyEq (appendTransitions left right) ->
  (TraceComponentsTotal nameEq keyEq left,
   TraceComponentsTotal nameEq keyEq right)
totalAppendSplit NoTransitions right evidence =
  (TraceComponentsTotalEnd, evidence)
totalAppendSplit
  (MoreTransitions (Fired stepNameEq stepKeyEq action tag checked)
    leftRest) right
  (TraceComponentsTotalStep
    (Fired stepNameEq stepKeyEq action tag checked)
    (appendTransitions leftRest right) boundary tailTotal) =
    case totalAppendSplit leftRest right tailTotal of
      (leftTotal, rightTotal) =>
        (TraceComponentsTotalStep
          (Fired stepNameEq stepKeyEq action tag checked)
          leftRest boundary leftTotal,
         rightTotal)

||| Package the exact three-way located-episode split needed by Lemma 72. It
||| derives both missing generation scans and transports the global no-R-episode
||| premise to the selected segment and suffix.
public export
record LocatedNoRegisteredSegments
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState)
  (selected : name)
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global)
  (registered : List (RegistrationGeneration name))
  (episodeStartOrdinal : Nat)
  (episodeStartLive : GenerationEnvironment name) where
  constructor MkLocatedNoRegisteredSegments
  episodeEndOrdinal : Nat
  episodeEndLive : GenerationEnvironment name
  0 episodeScan : GenerationTraceScan nameEq episodeStartOrdinal
    episodeStartLive
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode)))
    episodeEndOrdinal episodeEndLive
  0 episodeNoRegistered : NoRegisteredEpisode nameEq registered
    episodeStartOrdinal episodeStartLive
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode)))
  originalFinalOrdinal : Nat
  originalFinalLive : GenerationEnvironment name
  0 suffixScan : GenerationTraceScan nameEq episodeEndOrdinal episodeEndLive
    (traceAfterClosing episode) originalFinalOrdinal originalFinalLive
  0 suffixNoRegistered : NoRegisteredEpisode nameEq registered
    episodeEndOrdinal episodeEndLive (traceAfterClosing episode)

public export
0 splitLocatedNoRegisteredSegments :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (global : Transitions initial finalState) ->
  (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  (registered : List (RegistrationGeneration name)) ->
  (episodeStartOrdinal : Nat) ->
  (episodeStartLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq 0 [] (traceBeforeOpening episode)
    episodeStartOrdinal episodeStartLive ->
  NoRegisteredEpisode nameEq registered 0 [] global ->
  LocatedNoRegisteredSegments name key world error value nameEq keyEq global
    selected episode registered episodeStartOrdinal episodeStartLive
splitLocatedNoRegisteredSegments nameEq keyEq global selected episode registered
  episodeStartOrdinal episodeStartLive beforeScan globalNoRegistered =
    let decomposedNoRegistered : NoRegisteredEpisode nameEq registered 0 []
          (appendTransitions (traceBeforeOpening episode)
            (MoreTransitions
              (beginTransition (closedOpening (locatedEpisode episode)))
              (appendTransitions (closedTransitions (locatedEpisode episode))
                (traceAfterClosing episode))))
        decomposedNoRegistered =
          replace
            {p = \trace => NoRegisteredEpisode nameEq registered 0 [] trace}
            (sym (locatedDecomposition episode)) globalNoRegistered
    in case noRegisteredEpisodeAppendSplit nameEq registered 0 []
      (traceBeforeOpening episode)
      (MoreTransitions
        (beginTransition (closedOpening (locatedEpisode episode)))
        (appendTransitions (closedTransitions (locatedEpisode episode))
          (traceAfterClosing episode)))
      episodeStartOrdinal episodeStartLive beforeScan decomposedNoRegistered of
      (beforeNoRegistered, centerAndSuffixNoRegistered) =>
        case scanGenerations nameEq episodeStartOrdinal episodeStartLive
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode episode)))
            (closedTransitions (locatedEpisode episode))) of
          MkGenerationScanResult episodeEndOrdinal episodeEndLive episodeScan =>
            case noRegisteredEpisodeAppendSplit nameEq registered
              episodeStartOrdinal episodeStartLive
              (MoreTransitions
                (beginTransition (closedOpening (locatedEpisode episode)))
                (closedTransitions (locatedEpisode episode)))
              (traceAfterClosing episode) episodeEndOrdinal episodeEndLive
              episodeScan centerAndSuffixNoRegistered of
              (episodeNoRegistered, suffixNoRegistered) =>
                case scanGenerations nameEq episodeEndOrdinal episodeEndLive
                  (traceAfterClosing episode) of
                  MkGenerationScanResult finalOrdinal finalLive suffixScan =>
                    MkLocatedNoRegisteredSegments episodeEndOrdinal
                      episodeEndLive episodeScan episodeNoRegistered finalOrdinal
                      finalLive suffixScan suffixNoRegistered

||| The same located decomposition for repaired Definition 69. This gives the
||| selected segment/suffix totality evidence without changing the public alias.
public export
0 traceComponentsTotalLocatedSplit :
  (global : Transitions initial finalState) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  TraceComponentsTotal nameEq keyEq global ->
  (TraceComponentsTotal nameEq keyEq (traceBeforeOpening episode),
   TraceComponentsTotal nameEq keyEq
     (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
       (closedTransitions (locatedEpisode episode))),
   TraceComponentsTotal nameEq keyEq (traceAfterClosing episode))
traceComponentsTotalLocatedSplit global episode totality =
  let decomposedTotal : TraceComponentsTotal nameEq keyEq
        (appendTransitions (traceBeforeOpening episode)
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode episode)))
            (appendTransitions (closedTransitions (locatedEpisode episode))
              (traceAfterClosing episode))))
      decomposedTotal = replace
        {p = \trace => TraceComponentsTotal nameEq keyEq trace}
        (sym (locatedDecomposition episode)) totality
  in case totalAppendSplit (traceBeforeOpening episode)
    (MoreTransitions
      (beginTransition (closedOpening (locatedEpisode episode)))
      (appendTransitions (closedTransitions (locatedEpisode episode))
        (traceAfterClosing episode)))
    decomposedTotal of
    (beforeTotal, centerSuffixTotal) =>
      case totalAppendSplit
        (MoreTransitions
          (beginTransition (closedOpening (locatedEpisode episode)))
          (closedTransitions (locatedEpisode episode)))
        (traceAfterClosing episode) centerSuffixTotal of
        (episodeTotal, suffixTotal) =>
          (beforeTotal, episodeTotal, suffixTotal)
