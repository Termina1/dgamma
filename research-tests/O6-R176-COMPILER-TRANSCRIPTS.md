# R176 complete compiler transcripts

93 serialized compiler invocations: 61 positives, 26 intentional diagnostic negatives, 6 charged proof rejections. No engineering interrupt. See machine ledger for timing/RSS and the initial-batch clock limitation.

## A1-1 — positive

```text
START A1-1 2026-09-07T01:01:34.129632+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5UniqueRawNameCanonicalCapital.idr
END {"unit": "A1-1", "start": "2026-09-07T01:01:34.129632+00:00", "end": "2026-09-07T01:01:46.352501+00:00", "exit": 0, "maxSampleRSSKiB": 820960, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5UniqueRawNameCanonicalCapital.idr", "diagnosticErrors": false}
 8/11: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
 9/11: Building DGamma.CP5ConfluenceCrossTraceSpike (research/DGamma/CP5ConfluenceCrossTraceSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:39:3--39:68
 35 | 
 36 | public export
 37 | data CertifiedActorPermutation :
 38 |   (name : Type) -> List name -> List name -> Type where
 39 |   ActorPermutationDone : CertifiedActorPermutation name order order
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:40:3--43:48
 40 |   ActorPermutationStep :
 41 |     AdjacentActorOrderSwap name before middle ->
 42 |     CertifiedActorPermutation name middle after ->
 43 |     CertifiedActorPermutation name before after

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:273:1--276:77
 273 | transitionPrefixLength : (earlierTrace : Transitions initial before) ->
 274 |   (step : Transition before after) ->
 275 |   transitionCount (appendTransitions earlierTrace
 276 |     (MoreTransitions step NoTransitions)) = S (transitionCount earlierTrace)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:734:3--740:55
 734 |   OperationalActorDone :
 735 |     (blocks : ActorBlockDecomposition name key world error value nameEq keyEq
 736 |       order trace) ->
 737 |     (premises : ReplayInvariantBundle name key world error value protocol nameEq
 738 |       keyEq trace) ->
 739 |     OperationalActorPermutation name key world error value protocol nameEq keyEq

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:741:3--757:35
 741 |   OperationalActorStep :
 742 |     (orderSwap : AdjacentActorOrderSwap name before middle) ->
 743 |     (restCertificate : CertifiedActorPermutation name middle after) ->
 744 |     (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
 745 |       before sourceTrace) ->
 746 |     (sourcePremises : ReplayInvariantBundle name key world error value protocol

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1213:3--1221:41
 1213 | 0 permutationReplayCorrespondence :
 1214 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1215 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1216 |       rightCapital matching} ->
 1217 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1218 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1227:3--1235:41
 1227 | 0 permutationOccurrenceCorrespondence :
 1228 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1229 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1230 |       rightCapital matching} ->
 1231 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1232 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->

10/11: Building DGamma.CP5UniqueRawNameDeletion (research/DGamma/CP5UniqueRawNameDeletion.idr)
11/11: Building DGamma.CP5UniqueRawNameCanonicalCapital (research/DGamma/CP5UniqueRawNameCanonicalCapital.idr)


```

## A2-1 — positive

```text
START A2-1 2026-09-07T01:02:06.216934+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5UniqueRawNameCanonicalCapital.idr
END {"unit": "A2-1", "start": "2026-09-07T01:02:06.216934+00:00", "end": "2026-09-07T01:02:10.290391+00:00", "exit": 0, "maxSampleRSSKiB": 4546592, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5UniqueRawNameCanonicalCapital.idr", "diagnosticErrors": false}
11/11: Building DGamma.CP5UniqueRawNameCanonicalCapital (research/DGamma/CP5UniqueRawNameCanonicalCapital.idr)


```

## A3-1 — positive

```text
START A3-1 2026-09-07T01:02:30.060603+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5UniqueRawNameCanonicalCapital.idr
END {"unit": "A3-1", "start": "2026-09-07T01:02:30.060603+00:00", "end": "2026-09-07T01:02:34.135457+00:00", "exit": 0, "maxSampleRSSKiB": 4457904, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5UniqueRawNameCanonicalCapital.idr", "diagnosticErrors": false}
11/11: Building DGamma.CP5UniqueRawNameCanonicalCapital (research/DGamma/CP5UniqueRawNameCanonicalCapital.idr)


```

## A4-1 — positive

```text
START A4-1 2026-09-07T01:03:01.246756+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5UniqueRawNameCanonicalCapital.idr
END {"unit": "A4-1", "start": "2026-09-07T01:03:01.246756+00:00", "end": "2026-09-07T01:03:05.331786+00:00", "exit": 0, "maxSampleRSSKiB": 4164896, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5UniqueRawNameCanonicalCapital.idr", "diagnosticErrors": false}
11/11: Building DGamma.CP5UniqueRawNameCanonicalCapital (research/DGamma/CP5UniqueRawNameCanonicalCapital.idr)


```

## A-baseline-pollution — expected-negative

```text
START A-baseline-pollution 2026-09-07T01:03:37.520896+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R6OldPollutionNegative.idr
END {"unit": "A-baseline-pollution", "start": "2026-09-07T01:03:37.520896+00:00", "end": "2026-09-07T01:03:39.558058+00:00", "exit": 1, "maxSampleRSSKiB": 0, "cmd": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R6OldPollutionNegative.idr", "diagnosticErrors": true}
1/1: Building DGamma.R6OldPollutionNegative (research-tests/DGamma/R6OldPollutionNegative.idr)
Error: While processing right hand side of oldPollutionReachesO20. When unifying:
    CertifiedActorPermutation name (supportOrder (canonicalSchedule leftCapital)) (map (renameBackward (currentNameBijection (endpointRenaming sameInputs))) (supportOrder (canonicalSchedule rightCapital)))
and:
    CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital ?matching
Mismatch between: CertifiedActorPermutation name (supportOrder (canonicalSchedule leftCapital)) (map (renameBackward (currentNameBijection (endpointRenaming sameInputs))) (supportOrder (canonicalSchedule rightCapital))) and CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital ?matching.

DGamma.R6OldPollutionNegative:42:54--42:62
 38 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational)
 39 | oldPollutionReachesO20 {nameEq} {keyEq} {protocol} {leftTrace} {rightTrace}
 40 |   {sameInputs} {leftCapital} {rightCapital} matching polluted =
 41 |     (polluted ** canonicalSchedulesConvergeSpike nameEq keyEq protocol leftTrace
 42 |       rightTrace sameInputs leftCapital rightCapital polluted)
                                                           ^^^^^^^^



```

## A-baseline-mixed — expected-negative

```text
START A-baseline-mixed 2026-09-07T01:03:46.834527+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R6MixedScheduleNegative.idr
END {"unit": "A-baseline-mixed", "start": "2026-09-07T01:03:46.834527+00:00", "end": "2026-09-07T01:03:48.893225+00:00", "exit": 1, "maxSampleRSSKiB": 0, "cmd": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R6MixedScheduleNegative.idr", "diagnosticErrors": true}
1/1: Building DGamma.R6MixedScheduleNegative (research-tests/DGamma/R6MixedScheduleNegative.idr)
Error: While processing right hand side of mixedLeftSchedule. When unifying:
    CanonicalConvergenceResult name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital operational
and:
    CanonicalConvergenceResult name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs otherLeft rightCapital operational
Mismatch between: leftCapital and otherLeft.

DGamma.R6MixedScheduleNegative:34:41--34:52
 30 |     (currentNameBijection (endpointRenaming sameInputs))
 31 | mixedLeftSchedule {nameEq} {keyEq} {protocol} {leftTrace} {rightTrace} {sameInputs}
 32 |   leftCapital otherLeft rightCapital convergence =
 33 |     originalEndpointsConvergeSpike nameEq keyEq protocol leftTrace rightTrace
 34 |       sameInputs otherLeft rightCapital convergence
                                              ^^^^^^^^^^^



```

## A5-1 — positive

```text
START A5-1 2026-09-07T01:04:09.291762+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCrossTraceSpike.idr
END {"unit": "A5-1", "start": "2026-09-07T01:04:09.291762+00:00", "end": "2026-09-07T01:04:15.414965+00:00", "exit": 0, "maxSampleRSSKiB": 2780928, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCrossTraceSpike.idr", "diagnosticErrors": false}
9/9: Building DGamma.CP5ConfluenceCrossTraceSpike (research/DGamma/CP5ConfluenceCrossTraceSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:40:3--40:68
 36 | 
 37 | public export
 38 | data CertifiedActorPermutation :
 39 |   (name : Type) -> List name -> List name -> Type where
 40 |   ActorPermutationDone : CertifiedActorPermutation name order order
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:41:3--44:48
 41 |   ActorPermutationStep :
 42 |     AdjacentActorOrderSwap name before middle ->
 43 |     CertifiedActorPermutation name middle after ->
 44 |     CertifiedActorPermutation name before after

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:274:1--277:77
 274 | transitionPrefixLength : (earlierTrace : Transitions initial before) ->
 275 |   (step : Transition before after) ->
 276 |   transitionCount (appendTransitions earlierTrace
 277 |     (MoreTransitions step NoTransitions)) = S (transitionCount earlierTrace)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:735:3--741:55
 735 |   OperationalActorDone :
 736 |     (blocks : ActorBlockDecomposition name key world error value nameEq keyEq
 737 |       order trace) ->
 738 |     (premises : ReplayInvariantBundle name key world error value protocol nameEq
 739 |       keyEq trace) ->
 740 |     OperationalActorPermutation name key world error value protocol nameEq keyEq

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:742:3--758:35
 742 |   OperationalActorStep :
 743 |     (orderSwap : AdjacentActorOrderSwap name before middle) ->
 744 |     (restCertificate : CertifiedActorPermutation name middle after) ->
 745 |     (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
 746 |       before sourceTrace) ->
 747 |     (sourcePremises : ReplayInvariantBundle name key world error value protocol

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1216:3--1224:41
 1216 | 0 permutationReplayCorrespondence :
 1217 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1218 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1219 |       rightCapital matching} ->
 1220 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1221 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1230:3--1238:41
 1230 | 0 permutationOccurrenceCorrespondence :
 1231 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1232 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1233 |       rightCapital matching} ->
 1234 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1235 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->



```

## A6-1 — positive

```text
START A6-1 2026-09-07T01:04:37.601497+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCrossTraceSpike.idr
END {"unit": "A6-1", "start": "2026-09-07T01:04:37.601497+00:00", "end": "2026-09-07T01:04:43.719452+00:00", "exit": 0, "maxSampleRSSKiB": 2460240, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCrossTraceSpike.idr", "diagnosticErrors": false}
9/9: Building DGamma.CP5ConfluenceCrossTraceSpike (research/DGamma/CP5ConfluenceCrossTraceSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:40:3--40:68
 36 | 
 37 | public export
 38 | data CertifiedActorPermutation :
 39 |   (name : Type) -> List name -> List name -> Type where
 40 |   ActorPermutationDone : CertifiedActorPermutation name order order
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:41:3--44:48
 41 |   ActorPermutationStep :
 42 |     AdjacentActorOrderSwap name before middle ->
 43 |     CertifiedActorPermutation name middle after ->
 44 |     CertifiedActorPermutation name before after

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:274:1--277:77
 274 | transitionPrefixLength : (earlierTrace : Transitions initial before) ->
 275 |   (step : Transition before after) ->
 276 |   transitionCount (appendTransitions earlierTrace
 277 |     (MoreTransitions step NoTransitions)) = S (transitionCount earlierTrace)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:735:3--741:55
 735 |   OperationalActorDone :
 736 |     (blocks : ActorBlockDecomposition name key world error value nameEq keyEq
 737 |       order trace) ->
 738 |     (premises : ReplayInvariantBundle name key world error value protocol nameEq
 739 |       keyEq trace) ->
 740 |     OperationalActorPermutation name key world error value protocol nameEq keyEq

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:742:3--758:35
 742 |   OperationalActorStep :
 743 |     (orderSwap : AdjacentActorOrderSwap name before middle) ->
 744 |     (restCertificate : CertifiedActorPermutation name middle after) ->
 745 |     (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
 746 |       before sourceTrace) ->
 747 |     (sourcePremises : ReplayInvariantBundle name key world error value protocol

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1218:3--1226:41
 1218 | 0 permutationReplayCorrespondence :
 1219 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1220 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1221 |       rightCapital matching} ->
 1222 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1223 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1232:3--1240:41
 1232 | 0 permutationOccurrenceCorrespondence :
 1233 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1234 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1235 |       rightCapital matching} ->
 1236 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1237 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->



```

## A7-1 — positive

```text
START A7-1 2026-09-07T01:04:56.608001+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCrossTraceSpike.idr
END {"unit": "A7-1", "start": "2026-09-07T01:04:56.608001+00:00", "end": "2026-09-07T01:05:02.719894+00:00", "exit": 0, "maxSampleRSSKiB": 2346144, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCrossTraceSpike.idr", "diagnosticErrors": false}
9/9: Building DGamma.CP5ConfluenceCrossTraceSpike (research/DGamma/CP5ConfluenceCrossTraceSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:40:3--40:68
 36 | 
 37 | public export
 38 | data CertifiedActorPermutation :
 39 |   (name : Type) -> List name -> List name -> Type where
 40 |   ActorPermutationDone : CertifiedActorPermutation name order order
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:41:3--44:48
 41 |   ActorPermutationStep :
 42 |     AdjacentActorOrderSwap name before middle ->
 43 |     CertifiedActorPermutation name middle after ->
 44 |     CertifiedActorPermutation name before after

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:274:1--277:77
 274 | transitionPrefixLength : (earlierTrace : Transitions initial before) ->
 275 |   (step : Transition before after) ->
 276 |   transitionCount (appendTransitions earlierTrace
 277 |     (MoreTransitions step NoTransitions)) = S (transitionCount earlierTrace)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:736:3--742:55
 736 |   OperationalActorDone :
 737 |     (blocks : ActorBlockDecomposition name key world error value nameEq keyEq
 738 |       order trace) ->
 739 |     (premises : ReplayInvariantBundle name key world error value protocol nameEq
 740 |       keyEq trace) ->
 741 |     OperationalActorPermutation name key world error value protocol nameEq keyEq

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:743:3--759:35
 743 |   OperationalActorStep :
 744 |     (orderSwap : AdjacentActorOrderSwap name before middle) ->
 745 |     (restCertificate : CertifiedActorPermutation name middle after) ->
 746 |     (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
 747 |       before sourceTrace) ->
 748 |     (sourcePremises : ReplayInvariantBundle name key world error value protocol

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1219:3--1227:41
 1219 | 0 permutationReplayCorrespondence :
 1220 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1221 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1222 |       rightCapital matching} ->
 1223 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1224 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1233:3--1241:41
 1233 | 0 permutationOccurrenceCorrespondence :
 1234 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1235 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1236 |       rightCapital matching} ->
 1237 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1238 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->



```

## A8-1 — positive

```text
START A8-1 2026-09-07T01:05:20.916423+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCrossTraceSpike.idr
END {"unit": "A8-1", "start": "2026-09-07T01:05:20.916423+00:00", "end": "2026-09-07T01:05:27.049290+00:00", "exit": 0, "maxSampleRSSKiB": 2467712, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCrossTraceSpike.idr", "diagnosticErrors": false}
9/9: Building DGamma.CP5ConfluenceCrossTraceSpike (research/DGamma/CP5ConfluenceCrossTraceSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:40:3--40:68
 36 | 
 37 | public export
 38 | data CertifiedActorPermutation :
 39 |   (name : Type) -> List name -> List name -> Type where
 40 |   ActorPermutationDone : CertifiedActorPermutation name order order
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:41:3--44:48
 41 |   ActorPermutationStep :
 42 |     AdjacentActorOrderSwap name before middle ->
 43 |     CertifiedActorPermutation name middle after ->
 44 |     CertifiedActorPermutation name before after

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:274:1--277:77
 274 | transitionPrefixLength : (earlierTrace : Transitions initial before) ->
 275 |   (step : Transition before after) ->
 276 |   transitionCount (appendTransitions earlierTrace
 277 |     (MoreTransitions step NoTransitions)) = S (transitionCount earlierTrace)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:736:3--742:55
 736 |   OperationalActorDone :
 737 |     (blocks : ActorBlockDecomposition name key world error value nameEq keyEq
 738 |       order trace) ->
 739 |     (premises : ReplayInvariantBundle name key world error value protocol nameEq
 740 |       keyEq trace) ->
 741 |     OperationalActorPermutation name key world error value protocol nameEq keyEq

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:743:3--759:35
 743 |   OperationalActorStep :
 744 |     (orderSwap : AdjacentActorOrderSwap name before middle) ->
 745 |     (restCertificate : CertifiedActorPermutation name middle after) ->
 746 |     (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
 747 |       before sourceTrace) ->
 748 |     (sourcePremises : ReplayInvariantBundle name key world error value protocol

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1219:3--1227:41
 1219 | 0 permutationReplayCorrespondence :
 1220 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1221 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1222 |       rightCapital matching} ->
 1223 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1224 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1233:3--1241:41
 1233 | 0 permutationOccurrenceCorrespondence :
 1234 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1235 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1236 |       rightCapital matching} ->
 1237 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1238 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->



```

## A8n-1 — expected-negative

```text
START A8n-1 2026-09-07T01:05:44.143637+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R6OldPollutionNegative.idr
END {"unit": "A8n-1", "start": "2026-09-07T01:05:44.143637+00:00", "end": "2026-09-07T01:05:46.200932+00:00", "exit": 1, "maxSampleRSSKiB": 0, "cmd": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R6OldPollutionNegative.idr", "diagnosticErrors": true}
1/1: Building DGamma.R6OldPollutionNegative (research-tests/DGamma/R6OldPollutionNegative.idr)
Error: While processing right hand side of oldPollutionReachesO20. When unifying:
    CertifiedActorPermutation name (supportOrder (canonicalSchedule leftCapital)) (map (renameBackward (currentNameBijection (endpointRenaming sameInputs))) (supportOrder (canonicalSchedule rightCapital)))
and:
    CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital ?matching
Mismatch between: CertifiedActorPermutation name (supportOrder (canonicalSchedule leftCapital)) (map (renameBackward (currentNameBijection (endpointRenaming sameInputs))) (supportOrder (canonicalSchedule rightCapital))) and CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital ?matching.

DGamma.R6OldPollutionNegative:45:77--45:85
 41 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational)
 42 | oldPollutionReachesO20 {nameEq} {keyEq} {protocol} {leftTrace} {rightTrace}
 43 |   {sameInputs} {leftCapital} {rightCapital} leftUnique rightUnique matching polluted =
 44 |     (polluted ** canonicalSchedulesConvergeSpike nameEq keyEq protocol leftTrace
 45 |       rightTrace sameInputs leftCapital rightCapital leftUnique rightUnique polluted)
                                                                                  ^^^^^^^^



```

## A9-1 — positive

```text
START A9-1 2026-09-07T01:06:06.382438+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCrossTraceSpike.idr
END {"unit": "A9-1", "start": "2026-09-07T01:06:06.382438+00:00", "end": "2026-09-07T01:06:12.494799+00:00", "exit": 0, "maxSampleRSSKiB": 2215104, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCrossTraceSpike.idr", "diagnosticErrors": false}
9/9: Building DGamma.CP5ConfluenceCrossTraceSpike (research/DGamma/CP5ConfluenceCrossTraceSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:40:3--40:68
 36 | 
 37 | public export
 38 | data CertifiedActorPermutation :
 39 |   (name : Type) -> List name -> List name -> Type where
 40 |   ActorPermutationDone : CertifiedActorPermutation name order order
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:41:3--44:48
 41 |   ActorPermutationStep :
 42 |     AdjacentActorOrderSwap name before middle ->
 43 |     CertifiedActorPermutation name middle after ->
 44 |     CertifiedActorPermutation name before after

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:274:1--277:77
 274 | transitionPrefixLength : (earlierTrace : Transitions initial before) ->
 275 |   (step : Transition before after) ->
 276 |   transitionCount (appendTransitions earlierTrace
 277 |     (MoreTransitions step NoTransitions)) = S (transitionCount earlierTrace)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:736:3--742:55
 736 |   OperationalActorDone :
 737 |     (blocks : ActorBlockDecomposition name key world error value nameEq keyEq
 738 |       order trace) ->
 739 |     (premises : ReplayInvariantBundle name key world error value protocol nameEq
 740 |       keyEq trace) ->
 741 |     OperationalActorPermutation name key world error value protocol nameEq keyEq

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:743:3--759:35
 743 |   OperationalActorStep :
 744 |     (orderSwap : AdjacentActorOrderSwap name before middle) ->
 745 |     (restCertificate : CertifiedActorPermutation name middle after) ->
 746 |     (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
 747 |       before sourceTrace) ->
 748 |     (sourcePremises : ReplayInvariantBundle name key world error value protocol

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1219:3--1227:41
 1219 | 0 permutationReplayCorrespondence :
 1220 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1221 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1222 |       rightCapital matching} ->
 1223 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1224 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1233:3--1241:41
 1233 | 0 permutationOccurrenceCorrespondence :
 1234 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1235 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1236 |       rightCapital matching} ->
 1237 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1238 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->



```

## A9n-1 — expected-negative

```text
START A9n-1 2026-09-07T01:06:28.164339+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R6MixedScheduleNegative.idr
END {"unit": "A9n-1", "start": "2026-09-07T01:06:28.164339+00:00", "end": "2026-09-07T01:06:30.224504+00:00", "exit": 1, "maxSampleRSSKiB": 0, "cmd": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R6MixedScheduleNegative.idr", "diagnosticErrors": true}
1/1: Building DGamma.R6MixedScheduleNegative (research-tests/DGamma/R6MixedScheduleNegative.idr)
Error: While processing right hand side of mixedLeftSchedule. When unifying:
    CanonicalConvergenceResult name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital operational
and:
    CanonicalConvergenceResult name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs otherLeft rightCapital operational
Mismatch between: leftCapital and otherLeft.

DGamma.R6MixedScheduleNegative:37:64--37:75
 33 |     (currentNameBijection (endpointRenaming sameInputs))
 34 | mixedLeftSchedule {nameEq} {keyEq} {protocol} {leftTrace} {rightTrace} {sameInputs}
 35 |   leftCapital otherLeft rightCapital leftUnique rightUnique convergence =
 36 |     originalEndpointsConvergeSpike nameEq keyEq protocol leftTrace rightTrace
 37 |       sameInputs otherLeft rightCapital leftUnique rightUnique convergence
                                                                     ^^^^^^^^^^^



```

## A10-1 — positive

```text
START A10-1 2026-09-07T01:06:51.163133+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
END {"unit": "A10-1", "start": "2026-09-07T01:06:51.163133+00:00", "end": "2026-09-07T01:06:59.320032+00:00", "exit": 0, "maxSampleRSSKiB": 814976, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr", "diagnosticErrors": false}
8/8: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)


```

## A10-forward-check — positive

```text
START A10-forward-check 2026-09-07T01:07:10.612944+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCrossTraceSpike.idr
END {"unit": "A10-forward-check", "start": "2026-09-07T01:07:10.612944+00:00", "end": "2026-09-07T01:07:16.733734+00:00", "exit": 0, "maxSampleRSSKiB": 2963024, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCrossTraceSpike.idr", "diagnosticErrors": false}
9/9: Building DGamma.CP5ConfluenceCrossTraceSpike (research/DGamma/CP5ConfluenceCrossTraceSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:40:3--40:68
 36 | 
 37 | public export
 38 | data CertifiedActorPermutation :
 39 |   (name : Type) -> List name -> List name -> Type where
 40 |   ActorPermutationDone : CertifiedActorPermutation name order order
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:41:3--44:48
 41 |   ActorPermutationStep :
 42 |     AdjacentActorOrderSwap name before middle ->
 43 |     CertifiedActorPermutation name middle after ->
 44 |     CertifiedActorPermutation name before after

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:274:1--277:77
 274 | transitionPrefixLength : (earlierTrace : Transitions initial before) ->
 275 |   (step : Transition before after) ->
 276 |   transitionCount (appendTransitions earlierTrace
 277 |     (MoreTransitions step NoTransitions)) = S (transitionCount earlierTrace)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:736:3--742:55
 736 |   OperationalActorDone :
 737 |     (blocks : ActorBlockDecomposition name key world error value nameEq keyEq
 738 |       order trace) ->
 739 |     (premises : ReplayInvariantBundle name key world error value protocol nameEq
 740 |       keyEq trace) ->
 741 |     OperationalActorPermutation name key world error value protocol nameEq keyEq

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:743:3--759:35
 743 |   OperationalActorStep :
 744 |     (orderSwap : AdjacentActorOrderSwap name before middle) ->
 745 |     (restCertificate : CertifiedActorPermutation name middle after) ->
 746 |     (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
 747 |       before sourceTrace) ->
 748 |     (sourcePremises : ReplayInvariantBundle name key world error value protocol

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1219:3--1227:41
 1219 | 0 permutationReplayCorrespondence :
 1220 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1221 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1222 |       rightCapital matching} ->
 1223 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1224 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1233:3--1241:41
 1233 | 0 permutationOccurrenceCorrespondence :
 1234 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1235 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1236 |       rightCapital matching} ->
 1237 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1238 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->



```

## A-thread-R8 — positive

```text
START A-thread-R8 2026-09-07T01:07:45.267907+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R8FullPipeline.idr
END {"unit": "A-thread-R8", "start": "2026-09-07T01:07:45.267907+00:00", "end": "2026-09-07T01:09:27.063661+00:00", "exit": 0, "maxSampleRSSKiB": 38819680, "cmd": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R8FullPipeline.idr", "diagnosticErrors": false}
1/1: Building DGamma.R8FullPipeline (research-tests/DGamma/R8FullPipeline.idr)


```

## A-thread-R16 — positive

```text
START A-thread-R16 2026-09-07T01:09:52.783397+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R16ConfluenceTheoremAssemblyPositive.idr
END {"unit": "A-thread-R16", "start": "2026-09-07T01:09:52.783397+00:00", "end": "2026-09-07T01:09:54.823332+00:00", "exit": 0, "maxSampleRSSKiB": 0, "cmd": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R16ConfluenceTheoremAssemblyPositive.idr", "diagnosticErrors": false}
2/2: Building DGamma.R16ConfluenceTheoremAssemblyPositive (research-tests/DGamma/R16ConfluenceTheoremAssemblyPositive.idr)


```

## A11-1 — expected-negative

```text
START A11-1 2026-09-07T01:10:16.989307+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176BareCapitalFreshnessNegative.idr
END {"unit": "A11-1", "start": "2026-09-07T01:10:16.989307+00:00", "end": "2026-09-07T01:10:19.050361+00:00", "exit": 1, "maxSampleRSSKiB": 0, "cmd": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176BareCapitalFreshnessNegative.idr", "diagnosticErrors": true}
1/1: Building DGamma.R176BareCapitalFreshnessNegative (research-tests/DGamma/R176BareCapitalFreshnessNegative.idr)
Error: While processing right hand side of bareCapitalCannotSupplyFreshness. When unifying:
    TraceIndependent name key world error value keyEq initial originalFinal original
and:
    UniqueRawNameInsertions name key world error value nameEq keyEq original
Mismatch between: TraceIndependent name key world error value keyEq initial originalFinal original and UniqueRawNameInsertions name key world error value nameEq keyEq original.

DGamma.R176BareCapitalFreshnessNegative:26:6--26:38
 22 |   (UniqueRawNameInsertions name key world error value nameEq keyEq
 23 |     (canonicalTrace (canonicalSchedule capital)))
 24 | bareCapitalCannotSupplyFreshness name key world error value protocol nameEq keyEq capital =
 25 |   capitalCanonicalUniqueInsertions name key world error value protocol nameEq keyEq capital
 26 |     (originalTraceIndependent capital)
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^



```

## A12-1 — expected-negative

```text
START A12-1 2026-09-07T01:10:43.823087+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176WrongOriginalTraceUniqueNegative.idr
END {"unit": "A12-1", "start": "2026-09-07T01:10:43.823087+00:00", "end": "2026-09-07T01:10:45.879093+00:00", "exit": 1, "maxSampleRSSKiB": 0, "cmd": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176WrongOriginalTraceUniqueNegative.idr", "diagnosticErrors": true}
1/1: Building DGamma.R176WrongOriginalTraceUniqueNegative (research-tests/DGamma/R176WrongOriginalTraceUniqueNegative.idr)
Error: While processing right hand side of wrongOriginalTraceFreshness. When unifying:
    UniqueRawNameInsertions name key world error value nameEq keyEq otherTrace
and:
    UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace
Mismatch between: otherTrace and leftTrace.

DGamma.R176WrongOriginalTraceUniqueNegative:37:43--37:54
 33 |     (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)
 34 | wrongOriginalTraceFreshness name key world error value nameEq keyEq protocol leftTrace rightTrace
 35 |   otherTrace sameInputs leftCapital rightCapital otherUnique rightUnique =
 36 |     canonicalSupportOrdersMatchSpike nameEq keyEq protocol leftTrace rightTrace
 37 |       sameInputs leftCapital rightCapital otherUnique rightUnique
                                                ^^^^^^^^^^^



```

## A13-1 — expected-negative

```text
START A13-1 2026-09-07T01:11:14.352280+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176UnsealedOriginUniqueNegative.idr
END {"unit": "A13-1", "start": "2026-09-07T01:11:14.352280+00:00", "end": "2026-09-07T01:11:16.400419+00:00", "exit": 1, "maxSampleRSSKiB": 0, "cmd": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176UnsealedOriginUniqueNegative.idr", "diagnosticErrors": true}
1/1: Building DGamma.R176UnsealedOriginUniqueNegative (research-tests/DGamma/R176UnsealedOriginUniqueNegative.idr)
Error: While processing right hand side of unsealedOriginCannotTransportUnique. When unifying:
    ActionRegistrationReplayCorrespondence name key world error value source target
and:
    FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq ?source ?target
Mismatch between: ActionRegistrationReplayCorrespondence name key world error value source target and FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq ?source ?target.

DGamma.R176UnsealedOriginUniqueNegative:24:90--24:96
 20 |   (origin : ActionRegistrationReplayCorrespondence name key world error value source target) ->
 21 |   (UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
 22 |   (UniqueRawNameInsertions name key world error value nameEq keyEq target)
 23 | unsealedOriginCannotTransportUnique name key world error value protocol nameEq keyEq origin unique =
 24 |   uniqueInsertionsAfterFiniteDerivation name key world error value protocol nameEq keyEq origin unique
                                                                                               ^^^^^^



```

## A14-1 — expected-negative

```text
START A14-1 2026-09-07T01:11:44.482514+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176ReductionUniqueDirectionNegative.idr
END {"unit": "A14-1", "start": "2026-09-07T01:11:44.482514+00:00", "end": "2026-09-07T01:11:46.514400+00:00", "exit": 1, "maxSampleRSSKiB": 0, "cmd": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176ReductionUniqueDirectionNegative.idr", "diagnosticErrors": true}
1/1: Building DGamma.R176ReductionUniqueDirectionNegative (research-tests/DGamma/R176ReductionUniqueDirectionNegative.idr)
Error: While processing right hand side of reductionUniqueCannotRunBackward. Can't solve constraint between: reduction .reducedFinal and originalFinal.

DGamma.R176ReductionUniqueDirectionNegative:25:93--25:106
 21 |   (reduction : ClosingFreeReduction name key world error value protocol nameEq keyEq original) ->
 22 |   (UniqueRawNameInsertions name key world error value nameEq keyEq (reducedTrace reduction)) ->
 23 |   (UniqueRawNameInsertions name key world error value nameEq keyEq (reducedTrace reduction))
 24 | reductionUniqueCannotRunBackward name key world error value protocol nameEq keyEq reduction reducedUnique =
 25 |   uniqueInsertionsAfterReduction name key world error value nameEq keyEq protocol reduction reducedUnique
                                                                                                  ^^^^^^^^^^^^^



```

## A15-1 — positive

```text
START A15-1 2026-09-07T01:12:13.538260+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176CanonicalPermutationUniquePositive.idr
END {"unit": "A15-1", "start": "2026-09-07T01:12:13.538260+00:00", "end": "2026-09-07T01:12:15.594473+00:00", "exit": 0, "maxSampleRSSKiB": 0, "cmd": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176CanonicalPermutationUniquePositive.idr", "diagnosticErrors": false}
1/1: Building DGamma.R176CanonicalPermutationUniquePositive (research-tests/DGamma/R176CanonicalPermutationUniquePositive.idr)


```

## A-reuse-positive — positive

```text
START A-reuse-positive 2026-09-07T01:12:26.341132+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R173UniqueRawNameInsertionsFixtures.idr
END {"unit": "A-reuse-positive", "start": "2026-09-07T01:12:26.341132+00:00", "end": "2026-09-07T01:13:15.159696+00:00", "exit": 0, "maxSampleRSSKiB": 2446576, "cmd": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R173UniqueRawNameInsertionsFixtures.idr", "diagnosticErrors": false}
2/3: Building DGamma.R172O17OpenParentRootReuseCandidate (research-tests/DGamma/R172O17OpenParentRootReuseCandidate.idr)
3/3: Building DGamma.R173UniqueRawNameInsertionsFixtures (research-tests/DGamma/R173UniqueRawNameInsertionsFixtures.idr)


```

## A-provision-positive — positive

```text
START A-provision-positive 2026-09-07T01:13:22.736136+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R174O17ProvisionCollisionUnique.idr
END {"unit": "A-provision-positive", "start": "2026-09-07T01:13:22.736136+00:00", "end": "2026-09-07T01:13:24.787788+00:00", "exit": 0, "maxSampleRSSKiB": 0, "cmd": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R174O17ProvisionCollisionUnique.idr", "diagnosticErrors": false}
2/2: Building DGamma.R174O17ProvisionCollisionUnique (research-tests/DGamma/R174O17ProvisionCollisionUnique.idr)


```

## B1-1 — positive

```text
START B1-1 2026-09-07T01:18:41.429349+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr
END {"unit": "B1-1", "start": "2026-09-07T01:18:41.429349+00:00", "end": "2026-09-07T01:20:00.764754+00:00", "exit": 0, "maxSampleRSSKiB": 4897568, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr", "diagnosticErrors": false}
4/4: Building DGamma.CP5ConfluenceDeletionChainSpike (research/DGamma/CP5ConfluenceDeletionChainSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  surviving is shadowing DGamma.CP4DeletionGenerationFilter.GenerationFilterResult.surviving

DGamma.CP5ConfluenceDeletionChainSpike:3012:1--3014:19
 3012 | generationSubsequenceSourceOrdinal :
 3013 |   GenerationActionSubsequence nameEq deletable ordinal live original surviving ->
 3014 |   Nat -> Maybe Nat



```

## B2-1 — positive

```text
START B2-1 2026-09-07T01:20:33.421907+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr
END {"unit": "B2-1", "start": "2026-09-07T01:20:33.421907+00:00", "end": "2026-09-07T01:21:52.816331+00:00", "exit": 0, "maxSampleRSSKiB": 5020960, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr", "diagnosticErrors": false}
4/4: Building DGamma.CP5ConfluenceDeletionChainSpike (research/DGamma/CP5ConfluenceDeletionChainSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  surviving is shadowing DGamma.CP4DeletionGenerationFilter.GenerationFilterResult.surviving

DGamma.CP5ConfluenceDeletionChainSpike:3012:1--3014:19
 3012 | generationSubsequenceSourceOrdinal :
 3013 |   GenerationActionSubsequence nameEq deletable ordinal live original surviving ->
 3014 |   Nat -> Maybe Nat



```

## B3-1 — positive

```text
START B3-1 2026-09-07T01:22:14.792727+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr
END {"unit": "B3-1", "start": "2026-09-07T01:22:14.792727+00:00", "end": "2026-09-07T01:23:34.135113+00:00", "exit": 0, "maxSampleRSSKiB": 4742192, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr", "diagnosticErrors": false}
4/4: Building DGamma.CP5ConfluenceDeletionChainSpike (research/DGamma/CP5ConfluenceDeletionChainSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  surviving is shadowing DGamma.CP4DeletionGenerationFilter.GenerationFilterResult.surviving

DGamma.CP5ConfluenceDeletionChainSpike:3012:1--3014:19
 3012 | generationSubsequenceSourceOrdinal :
 3013 |   GenerationActionSubsequence nameEq deletable ordinal live original surviving ->
 3014 |   Nat -> Maybe Nat



```

## B4-1 — positive

```text
START B4-1 2026-09-07T01:24:00.894467+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr
END {"unit": "B4-1", "start": "2026-09-07T01:24:00.894467+00:00", "end": "2026-09-07T01:25:20.281990+00:00", "exit": 0, "maxSampleRSSKiB": 4888256, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr", "diagnosticErrors": false}
4/4: Building DGamma.CP5ConfluenceDeletionChainSpike (research/DGamma/CP5ConfluenceDeletionChainSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  surviving is shadowing DGamma.CP4DeletionGenerationFilter.GenerationFilterResult.surviving

DGamma.CP5ConfluenceDeletionChainSpike:3012:1--3014:19
 3012 | generationSubsequenceSourceOrdinal :
 3013 |   GenerationActionSubsequence nameEq deletable ordinal live original surviving ->
 3014 |   Nat -> Maybe Nat



```

## B5-1 — positive

```text
START B5-1 2026-09-07T01:25:39.480577+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr
END {"unit": "B5-1", "start": "2026-09-07T01:25:39.480577+00:00", "end": "2026-09-07T01:26:58.873050+00:00", "exit": 0, "maxSampleRSSKiB": 4815504, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr", "diagnosticErrors": false}
4/4: Building DGamma.CP5ConfluenceDeletionChainSpike (research/DGamma/CP5ConfluenceDeletionChainSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  surviving is shadowing DGamma.CP4DeletionGenerationFilter.GenerationFilterResult.surviving

DGamma.CP5ConfluenceDeletionChainSpike:3012:1--3014:19
 3012 | generationSubsequenceSourceOrdinal :
 3013 |   GenerationActionSubsequence nameEq deletable ordinal live original surviving ->
 3014 |   Nat -> Maybe Nat



```

## B6-1 — charged-proof-rejection

```text
START B6-1 2026-09-07T01:27:45.222395+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr
END {"unit": "B6-1", "start": "2026-09-07T01:27:45.222395+00:00", "end": "2026-09-07T01:29:00.529052+00:00", "exit": 1, "maxSampleRSSKiB": 3648528, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr", "diagnosticErrors": true}
4/4: Building DGamma.CP5ConfluenceDeletionChainSpike (research/DGamma/CP5ConfluenceDeletionChainSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  surviving is shadowing DGamma.CP4DeletionGenerationFilter.GenerationFilterResult.surviving

DGamma.CP5ConfluenceDeletionChainSpike:3012:1--3014:19
 3012 | generationSubsequenceSourceOrdinal :
 3013 |   GenerationActionSubsequence nameEq deletable ordinal live original surviving ->
 3014 |   Nat -> Maybe Nat

Error: While processing type of rawClosingRanksSameActor. Undefined name UniqueRawNameInsertions. 

DGamma.CP5ConfluenceDeletionChainSpike:30619:4--30619:27
 30615 |   (protocol : RegistrationProtocol key value world error) ->
 30616 |   {initial, finalState : SystemState name key value world error} ->
 30617 |   (global : Transitions initial finalState) ->
 30618 |   (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq global) ->
 30619 |   (UniqueRawNameInsertions name key world error value nameEq keyEq global) ->
            ^^^^^^^^^^^^^^^^^^^^^^^

Error: No type declaration for DGamma.CP5ConfluenceDeletionChainSpike.rawClosingRanksSameActor.

DGamma.CP5ConfluenceDeletionChainSpike:30628:1--30644:119
 30628 | rawClosingRanksSameActor name key world error value nameEq keyEq protocol global premises unique
 30629 |   leftActor _ left right Refl =
 30630 |     uniqueRawRanksAcrossPrefixes name key world error value protocol nameEq keyEq global
 30631 |       (replayAligned premises) (replayInitialEmpty premises) unique
 30632 |       (prefixThroughOpening left)
 30633 |       (appendTransitions (closedTransitions (locatedEpisode left)) (traceAfterClosing left))



```

## B6-2 — positive

```text
START B6-2 2026-09-07T01:29:17.484952+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr
END {"unit": "B6-2", "start": "2026-09-07T01:29:17.484952+00:00", "end": "2026-09-07T01:30:36.876489+00:00", "exit": 0, "maxSampleRSSKiB": 4843072, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr", "diagnosticErrors": false}
4/4: Building DGamma.CP5ConfluenceDeletionChainSpike (research/DGamma/CP5ConfluenceDeletionChainSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  surviving is shadowing DGamma.CP4DeletionGenerationFilter.GenerationFilterResult.surviving

DGamma.CP5ConfluenceDeletionChainSpike:3013:1--3015:19
 3013 | generationSubsequenceSourceOrdinal :
 3014 |   GenerationActionSubsequence nameEq deletable ordinal live original surviving ->
 3015 |   Nat -> Maybe Nat



```

## B7-1 — positive

```text
START B7-1 2026-09-07T01:31:02.739335+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr
END {"unit": "B7-1", "start": "2026-09-07T01:31:02.739335+00:00", "end": "2026-09-07T01:32:22.076154+00:00", "exit": 0, "maxSampleRSSKiB": 4783168, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr", "diagnosticErrors": false}
4/4: Building DGamma.CP5ConfluenceDeletionChainSpike (research/DGamma/CP5ConfluenceDeletionChainSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  surviving is shadowing DGamma.CP4DeletionGenerationFilter.GenerationFilterResult.surviving

DGamma.CP5ConfluenceDeletionChainSpike:3013:1--3015:19
 3013 | generationSubsequenceSourceOrdinal :
 3014 |   GenerationActionSubsequence nameEq deletable ordinal live original surviving ->
 3015 |   Nat -> Maybe Nat



```

## B8-1 — positive

```text
START B8-1 2026-09-07T01:32:50.588373+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr
END {"unit": "B8-1", "start": "2026-09-07T01:32:50.588373+00:00", "end": "2026-09-07T01:34:09.995229+00:00", "exit": 0, "maxSampleRSSKiB": 4798400, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr", "diagnosticErrors": false}
4/4: Building DGamma.CP5ConfluenceDeletionChainSpike (research/DGamma/CP5ConfluenceDeletionChainSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  surviving is shadowing DGamma.CP4DeletionGenerationFilter.GenerationFilterResult.surviving

DGamma.CP5ConfluenceDeletionChainSpike:3013:1--3015:19
 3013 | generationSubsequenceSourceOrdinal :
 3014 |   GenerationActionSubsequence nameEq deletable ordinal live original surviving ->
 3015 |   Nat -> Maybe Nat



```

## B9-1 — positive

```text
START B9-1 2026-09-07T01:34:49.653117+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr
END {"unit": "B9-1", "start": "2026-09-07T01:34:49.653117+00:00", "end": "2026-09-07T01:36:09.065663+00:00", "exit": 0, "maxSampleRSSKiB": 4783376, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr", "diagnosticErrors": false}
4/4: Building DGamma.CP5ConfluenceDeletionChainSpike (research/DGamma/CP5ConfluenceDeletionChainSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  surviving is shadowing DGamma.CP4DeletionGenerationFilter.GenerationFilterResult.surviving

DGamma.CP5ConfluenceDeletionChainSpike:3013:1--3015:19
 3013 | generationSubsequenceSourceOrdinal :
 3014 |   GenerationActionSubsequence nameEq deletable ordinal live original surviving ->
 3015 |   Nat -> Maybe Nat



```

## B10-1 — positive

```text
START B10-1 2026-09-07T01:36:55.101136+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr
END {"unit": "B10-1", "start": "2026-09-07T01:36:55.101136+00:00", "end": "2026-09-07T01:38:14.483105+00:00", "exit": 0, "maxSampleRSSKiB": 4778048, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr", "diagnosticErrors": false}
4/4: Building DGamma.CP5ConfluenceDeletionChainSpike (research/DGamma/CP5ConfluenceDeletionChainSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  surviving is shadowing DGamma.CP4DeletionGenerationFilter.GenerationFilterResult.surviving

DGamma.CP5ConfluenceDeletionChainSpike:3013:1--3015:19
 3013 | generationSubsequenceSourceOrdinal :
 3014 |   GenerationActionSubsequence nameEq deletable ordinal live original surviving ->
 3015 |   Nat -> Maybe Nat



```

## B11-1 — positive

```text
START B11-1 2026-09-07T01:38:44.170042+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr
END {"unit": "B11-1", "start": "2026-09-07T01:38:44.170042+00:00", "end": "2026-09-07T01:40:03.582757+00:00", "exit": 0, "maxSampleRSSKiB": 4895584, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr", "diagnosticErrors": false}
4/4: Building DGamma.CP5ConfluenceDeletionChainSpike (research/DGamma/CP5ConfluenceDeletionChainSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  surviving is shadowing DGamma.CP4DeletionGenerationFilter.GenerationFilterResult.surviving

DGamma.CP5ConfluenceDeletionChainSpike:3013:1--3015:19
 3013 | generationSubsequenceSourceOrdinal :
 3014 |   GenerationActionSubsequence nameEq deletable ordinal live original surviving ->
 3015 |   Nat -> Maybe Nat



```

## B12-1 — positive

```text
START B12-1 2026-09-07T01:42:16.210309+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr
END {"unit": "B12-1", "start": "2026-09-07T01:42:16.210309+00:00", "end": "2026-09-07T01:43:35.635459+00:00", "exit": 0, "maxSampleRSSKiB": 4877280, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr", "diagnosticErrors": false}
4/4: Building DGamma.CP5ConfluenceDeletionChainSpike (research/DGamma/CP5ConfluenceDeletionChainSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  surviving is shadowing DGamma.CP4DeletionGenerationFilter.GenerationFilterResult.surviving

DGamma.CP5ConfluenceDeletionChainSpike:3013:1--3015:19
 3013 | generationSubsequenceSourceOrdinal :
 3014 |   GenerationActionSubsequence nameEq deletable ordinal live original surviving ->
 3015 |   Nat -> Maybe Nat



```

## C1-1 — positive

```text
START C1-1 2026-09-07T01:47:32.818307+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRankObservationSpike.idr
END {"unit": "C1-1", "start": "2026-09-07T01:47:32.818307+00:00", "end": "2026-09-07T01:47:34.873634+00:00", "exit": 0, "maxSampleRSSKiB": 0, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRankObservationSpike.idr", "diagnosticErrors": false}
1/1: Building DGamma.CP5ConfluenceRankObservationSpike (research/DGamma/CP5ConfluenceRankObservationSpike.idr)


```

## C2-1 — positive

```text
START C2-1 2026-09-07T01:48:03.502154+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceLocalDiamondSpike.idr
END {"unit": "C2-1", "start": "2026-09-07T01:48:03.502154+00:00", "end": "2026-09-07T01:56:24.268138+00:00", "exit": 0, "maxSampleRSSKiB": 48736704, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceLocalDiamondSpike.idr", "diagnosticErrors": false}
2/2: Building DGamma.CP5ConfluenceLocalDiamondSpike (research/DGamma/CP5ConfluenceLocalDiamondSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  tail is shadowing Prelude.Types.tail

DGamma.CP5ConfluenceLocalDiamondSpike:992:3--996:64
 992 |   ConsStageOccursLater :
 993 |     (head : Transition first middle) ->
 994 |     (later : OccursIn selected tail) ->
 995 |     ConsStageOccurrenceView {head} {tail}
 996 |       (DGamma.Metatheory.OccursLater {transition = head} later)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  head is shadowing Prelude.Types.head
  tail is shadowing Prelude.Types.tail

DGamma.CP5ConfluenceLocalDiamondSpike:998:3--1000:33
 0998 | 0 viewConsStageOccurrence :
 0999 |   (occurs : OccursIn selected (MoreTransitions head tail)) ->
 1000 |   ConsStageOccurrenceView occurs

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  tail is shadowing Prelude.Types.tail

DGamma.CP5ConfluenceLocalDiamondSpike:1818:3--1821:77
 1818 | 0 prependIteratorStage :
 1819 |   (head : Transition sourceFirst sourceMiddle) ->
 1820 |   IteratorStage name key world error value actor tail ->
 1821 |   IteratorStage name key world error value actor (MoreTransitions head tail)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  tail is shadowing Prelude.Types.tail

DGamma.CP5ConfluenceLocalDiamondSpike:1846:3--1850:32
 1846 | 0 prependGenerator :
 1847 |   (head : Transition sourceFirst sourceMiddle) ->
 1848 |   TraceEffectGenerator name key world error value actor tail ->
 1849 |   TraceEffectGenerator name key world error value actor
 1850 |     (MoreTransitions head tail)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  tail is shadowing Prelude.Types.tail

DGamma.CP5ConfluenceLocalDiamondSpike:1878:3--1883:38
 1878 | 0 prependGeneratorMapExact :
 1879 |   (head : Transition sourceFirst sourceMiddle) ->
 1880 |   (generator : TraceEffectGenerator name key world error value actor tail) ->
 1881 |   (state : EffectState name key value world) ->
 1882 |   traceGeneratorMap (prependGenerator head generator) state =
 1883 |     traceGeneratorMap generator state

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  tail is shadowing Prelude.Types.tail

DGamma.CP5ConfluenceLocalDiamondSpike:2107:3--2112:37
 2107 | 0 prependIteratorOutcomeExact :
 2108 |   (head : Transition sourceFirst sourceMiddle) ->
 2109 |   (stage : IteratorStage name key world error value actor tail) ->
 2110 |   (state : EffectState name key value world) ->
 2111 |   iteratorStageOutcome (prependIteratorStage head stage) state =
 2112 |     iteratorStageOutcome stage state

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sourceAccumulator is shadowing DGamma.CP3.ParentRegistrationYield.sourceAccumulator
  view is shadowing Data.Nat.LT.view

DGamma.CP5ConfluenceLocalDiamondSpike:6690:5--6702:53
 6690 |   0 emptyByMatch :
 6691 |     (matches : Bool) ->
 6692 |     targetMatches @{nameEq}
 6693 |       (targetFiber @{nameEq} @{keyEq}
 6694 |         (MkFiber component sourceParent retiredFlag sourceTable
 6695 |           (Reloading [] sourceAccumulator view)) sourceRegistry) view = matches ->

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:14303:11--14305:84
 14303 |         0 leftMovedSame : (state : EffectState name key value world) ->
 14304 |           partialEffectMapFor nameEq keyEq leftAction leftTag first state =
 14305 |           partialEffectMapFor nameEq keyEq leftAction leftTag earlyRightFinal state

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:16726:21--16727:69
 16726 |                   0 effectOutput : ActivationPairEffectOutput nameEq keyEq
 16727 |                     leftAction leftTag earlyRightFinal originalFinal

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:16732:21--16733:36
 16732 |                   0 rawMove : RawActivationMove nameEq keyEq leftAction leftTag
 16733 |                     earlyRightFinal

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:16741:21--16742:58
 16741 |                   0 endpoint : CheckedActivationEndpoint nameEq keyEq leftAction
 16742 |                     leftTag earlyRightFinal originalFinal

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:16792:21--16794:75
 16792 |                   0 earlyActivation : PaperActivationStep
 16793 |                     (Fired {before = first} {afterState = earlyRightFinal}
 16794 |                       nameEq keyEq rightAction rightTag earlyCheckedRight)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:16803:21--16804:43
 16803 |                   0 earlyWellFormed : registryWellFormed @{nameEq} @{keyEq}
 16804 |                     earlyRightFinal = True

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:16883:21--16886:74
 16883 |                   0 rawEarlyFrame : PartialRelated
 16884 |                     (EffectState name key value world) (EffectStateRelated keyEq)
 16885 |                     (earlyRightMap (projectEffectState @{nameEq} first))
 16886 |                     (Just (projectEffectState @{nameEq} earlyRightFinal))

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:16889:21--16892:74
 16889 |                   0 earlyFrame : PartialRelated
 16890 |                     (EffectState name key value world) (EffectStateRelated keyEq)
 16891 |                     (rightMap (projectEffectState @{nameEq} first))
 16892 |                     (Just (projectEffectState @{nameEq} earlyRightFinal))

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:16904:21--16908:74
 16904 |                   0 rightGeneratorFrame : PartialRelated
 16905 |                     (EffectState name key value world) (EffectStateRelated keyEq)
 16906 |                     (traceGeneratorMap rightGenerator
 16907 |                       (projectEffectState @{nameEq} first))
 16908 |                     (Just (projectEffectState @{nameEq} earlyRightFinal))

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:16912:21--16913:69
 16912 |                   0 effectOutput : ActivationPairEffectOutput nameEq keyEq
 16913 |                     leftAction leftTag earlyRightFinal originalFinal

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:16918:21--16919:36
 16918 |                   0 rawMove : RawActivationMove nameEq keyEq leftAction leftTag
 16919 |                     earlyRightFinal

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:16925:21--16926:58
 16925 |                   0 endpoint : CheckedActivationEndpoint nameEq keyEq leftAction
 16926 |                     leftTag earlyRightFinal originalFinal

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:16932:21--16933:78
 16932 |                   0 movedCheckedLeft : checkedApplyAction @{nameEq} @{keyEq}
 16933 |                     leftAction earlyRightFinal = Just (leftTag, swappedFinal)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:16935:21--16937:75
 16935 |                   0 movedRightActivation : PaperActivationStep
 16936 |                     (Fired {before = first} {afterState = earlyRightFinal}
 16937 |                       nameEq keyEq rightAction rightTag earlyCheckedRight)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:16939:21--16941:72
 16939 |                   0 movedLeftActivation : PaperActivationStep
 16940 |                     (Fired {before = earlyRightFinal} {afterState = swappedFinal}
 16941 |                       nameEq keyEq leftAction leftTag movedCheckedLeft)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:16951:21--16957:65
 16951 |                   0 leftLookup : (lookupFiber @{nameEq} {name = name}
 16952 |                     {key = key} {value = value} {world = world}
 16953 |                     {error = error} (actionOwner leftAction)
 16954 |                     (registry earlyRightFinal) = lookupFiber @{nameEq}
 16955 |                       {name = name} {key = key} {value = value}
 16956 |                       {world = world} {error = error}

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:16969:21--16976:61
 16969 |                   0 leftTargets : (fiber : Fiber name key value world error) ->
 16970 |                     (view : View name (dependencies
 16971 |                       (componentDependencies
 16972 |                         (fiberComponent fiber)))) ->
 16973 |                     targetFiber @{nameEq} @{keyEq} fiber
 16974 |                       (registry first) = Just view ->

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:16994:21--17002:62
 16994 |                   0 leftOutcomes : (stage : IteratorStage name key
 16995 |                     world error value (actionOwner leftAction)
 16996 |                     pairTrace) -> IteratorOutcomeAgreement name key
 16997 |                       value world error keyEq
 16998 |                       (iteratorStageOutcome stage
 16999 |                         (projectEffectState @{nameEq}

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:17027:21--17029:49
 17027 |                   0 leftComparison : ActivationReplacementComparison
 17028 |                     nameEq (actionOwner leftAction) first middle
 17029 |                     earlyRightFinal swappedFinal

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:17038:21--17040:57
 17038 |                   0 rightComparison : ActivationReplacementComparison
 17039 |                     nameEq (actionOwner rightAction) first
 17040 |                     earlyRightFinal middle originalFinal

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:17392:21--17394:75
 17392 |                   0 earlyActivation : PaperActivationStep
 17393 |                     (Fired {before = first} {afterState = earlyRightFinal}
 17394 |                       nameEq keyEq rightAction rightTag earlyCheckedRight)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:17397:21--17398:43
 17397 |                   0 earlyWellFormed : registryWellFormed @{nameEq} @{keyEq}
 17398 |                     earlyRightFinal = True

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:17490:21--17492:36
 17490 |                   0 comparison : ActivationReplacementComparison nameEq
 17491 |                     (actionOwner rightAction) middle originalFinal first
 17492 |                     earlyRightFinal

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:17499:21--17500:69
 17499 |                   0 effectOutput : ActivationPairEffectOutput nameEq keyEq
 17500 |                     leftAction leftTag earlyRightFinal originalFinal

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:17505:21--17506:36
 17505 |                   0 rawMove : RawActivationMove nameEq keyEq leftAction leftTag
 17506 |                     earlyRightFinal

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:17511:21--17512:58
 17511 |                   0 endpoint : CheckedActivationEndpoint nameEq keyEq leftAction
 17512 |                     leftTag earlyRightFinal originalFinal

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:17518:21--17519:78
 17518 |                   0 movedCheckedLeft : checkedApplyAction @{nameEq} @{keyEq}
 17519 |                     leftAction earlyRightFinal = Just (leftTag, swappedFinal)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:17521:21--17523:72
 17521 |                   0 movedLeftOrchestration : PaperOrchestrationStep
 17522 |                     (Fired {before = earlyRightFinal} {afterState = swappedFinal}
 17523 |                       nameEq keyEq leftAction leftTag movedCheckedLeft)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  swappedFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.LocalRelationalDiamond.swappedFinal

DGamma.CP5ConfluenceLocalDiamondSpike:17590:5--17592:151
 17590 |   0 leftOwnerRelated : FiberControlMaybeRelated
 17591 |     (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner leftAction) (registry originalFinal))
 17592 |     (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner leftAction) (registry swappedFinal))

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:17594:11--17597:40
 17594 |     let 0 sourceSame : Equal
 17595 |           (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner leftAction) (registry first))
 17596 |           (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner leftAction)
 17597 |             (registry earlyRightFinal))

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  swappedFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.LocalRelationalDiamond.swappedFinal

DGamma.CP5ConfluenceLocalDiamondSpike:17601:11--17607:39
 17601 |         0 ownerRelated : FiberControlMaybeRelated
 17602 |           (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
 17603 |             {world = world} {error = error} (actionOwner leftAction)
 17604 |               (registry middle))
 17605 |           (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
 17606 |             {world = world} {error = error} (actionOwner leftAction)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  swappedFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.LocalRelationalDiamond.swappedFinal

DGamma.CP5ConfluenceLocalDiamondSpike:17623:5--17625:152
 17623 |   0 rightOwnerRelated : FiberControlMaybeRelated
 17624 |     (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner rightAction) (registry originalFinal))
 17625 |     (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner rightAction) (registry swappedFinal))

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:17632:11--17638:42
 17632 |         0 ownerRelated : FiberControlMaybeRelated
 17633 |           (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
 17634 |             {world = world} {error = error} (actionOwner rightAction)
 17635 |               (registry originalFinal))
 17636 |           (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
 17637 |             {world = world} {error = error} (actionOwner rightAction)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  swappedFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.LocalRelationalDiamond.swappedFinal
  earlyRightFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.OrchestrationSwapSafety.earlyRightFinal

DGamma.CP5ConfluenceLocalDiamondSpike:17641:11--17645:40
 17641 |         0 swappedFrame : Equal
 17642 |           (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner rightAction)
 17643 |             (registry swappedFinal))
 17644 |           (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner rightAction)
 17645 |             (registry earlyRightFinal))

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  swappedFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.LocalRelationalDiamond.swappedFinal

DGamma.CP5ConfluenceLocalDiamondSpike:17655:5--17660:137
 17655 |   0 outsideRelated : (selected : name) ->
 17656 |     Not (selected = actionOwner leftAction) ->
 17657 |     Not (selected = actionOwner rightAction) ->
 17658 |     FiberControlMaybeRelated
 17659 |       (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected (registry originalFinal))
 17660 |       (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected (registry swappedFinal))

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  swappedFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.LocalRelationalDiamond.swappedFinal

DGamma.CP5ConfluenceLocalDiamondSpike:17670:11--17672:141
 17670 |         0 sameLookup : Equal
 17671 |           (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected (registry originalFinal))
 17672 |           (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected (registry swappedFinal))

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  swappedFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.LocalRelationalDiamond.swappedFinal

DGamma.CP5ConfluenceLocalDiamondSpike:17678:5--17682:72
 17678 |   0 pointwise : (selected : name) -> FiberControlMaybeRelated
 17679 |     (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
 17680 |       {world = world} {error = error} selected (registry originalFinal))
 17681 |     (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
 17682 |       {world = world} {error = error} selected (registry swappedFinal))

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  replayedFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.AdjacentSwapResult.replayedFinal

DGamma.CP5ConfluenceLocalDiamondSpike:21177:3--21184:45
 21177 | 0 replayPointwiseSuffixTraceComponentsTotal :
 21178 |   (nameEq : DecEq name) -> (keyEq : DecEq key) ->
 21179 |   (source : Transitions sourceFirst sourceFinal) ->
 21180 |   (replayed : Transitions replayedFirst replayedFinal) ->
 21181 |   SealedSuffixReplaySpine name key world error value nameEq keyEq source
 21182 |     replayed ->

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  replayedFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.AdjacentSwapResult.replayedFinal

DGamma.CP5ConfluenceLocalDiamondSpike:21202:3--21224:63
 21202 | 0 adjacentTargetTraceComponentsTotal :
 21203 |   (nameEq : DecEq name) -> (keyEq : DecEq key) ->
 21204 |   (tracePrefix : Transitions initial pairFirst) ->
 21205 |   (left : Transition pairFirst pairMiddle) ->
 21206 |   (right : Transition pairMiddle pairFinal) ->
 21207 |   (suffix : Transitions pairFinal originalFinal) ->

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  replayedFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.AdjacentSwapResult.replayedFinal

DGamma.CP5ConfluenceLocalDiamondSpike:22098:3--22120:63
 22098 | 0 r97Field9WholeAppendCorrespondence :
 22099 |   (original : Transitions initial originalFinal) ->
 22100 |   (tracePrefix : Transitions initial pairFirst) ->
 22101 |   (left : Transition pairFirst pairMiddle) ->
 22102 |   (right : Transition pairMiddle pairFinal) ->
 22103 |   (suffix : Transitions pairFinal originalFinal) ->

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  replayedFinal is shadowing DGamma.CP5ConfluenceLocalDiamondSpike.AdjacentSwapResult.replayedFinal

DGamma.CP5ConfluenceLocalDiamondSpike:22143:3--22163:63
 22143 | 0 r97Field9ConcreteCapitalConsumer :
 22144 |   (original : Transitions initial originalFinal) ->
 22145 |   (tracePrefix : Transitions initial pairFirst) ->
 22146 |   (left : Transition pairFirst pairMiddle) ->
 22147 |   (right : Transition pairMiddle pairFinal) ->
 22148 |   (suffix : Transitions pairFinal originalFinal) ->



```

## C3-1 — positive

```text
START C3-1 2026-09-07T01:57:03.342397+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
END {"unit": "C3-1", "start": "2026-09-07T01:57:03.342397+00:00", "end": "2026-09-07T02:04:12.816616+00:00", "exit": 0, "maxSampleRSSKiB": 44731088, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr", "diagnosticErrors": false}
5/8: Building DGamma.CP5ConfluenceDeletionChainSpike (research/DGamma/CP5ConfluenceDeletionChainSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  surviving is shadowing DGamma.CP4DeletionGenerationFilter.GenerationFilterResult.surviving

DGamma.CP5ConfluenceDeletionChainSpike:3013:1--3015:19
 3013 | generationSubsequenceSourceOrdinal :
 3014 |   GenerationActionSubsequence nameEq deletable ordinal live original surviving ->
 3015 |   Nat -> Maybe Nat

6/8: Building DGamma.CP5UniqueRawNameOrdinalCapital (research/DGamma/CP5UniqueRawNameOrdinalCapital.idr)
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted



```

## C4-1 — charged-proof-rejection

```text
START C4-1 2026-09-07T02:05:37.272847+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
END {"unit": "C4-1", "start": "2026-09-07T02:05:37.272847+00:00", "end": "2026-09-07T02:06:30.220891+00:00", "exit": 1, "maxSampleRSSKiB": 17970880, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr", "diagnosticErrors": true}
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted

Error: While processing right hand side of canonicalWorkRankSegmentsFold. Can't solve constraint between: case the (Maybe name) (case transitionAction step of { OInsert child (ChildOf parent) component => Just parent ; LBegin actor => Just actor ; LAdvance actor => Just actor ; LDivert actor => Just actor ; LLeave actor => Just actor ; LUnload actor => Just actor ; action => Nothing }) of
  { Nothing => [] :: canonicalWorkRankSegments name key world error value nameEq fixedOrder rest
  ; Just owner => case canonicalWorkRankSegments name key world error value nameEq fixedOrder rest of
    { [] => [[length (takeWhile (\candidate => let 0 segments = [] in case decEq candidate owner of { Yes same => False ; No distinct => True }) fixedOrder)]]
    ; segment :: later => (length (takeWhile (\candidate => let 0 segments = segment :: later in case decEq candidate owner of { Yes same => False ; No distinct => True }) fixedOrder) :: segment) :: later
    }
  } and case the (Maybe name) (case transitionAction step of { OInsert child (ChildOf parent) component => Just parent ; LBegin actor => Just actor ; LAdvance actor => Just actor ; LDivert actor => Just actor ; LLeave actor => Just actor ; LUnload actor => Just actor ; _ => Nothing }) of
  { Nothing => [] :: canonicalWorkRankSegments name key world error value nameEq fixedOrder rest
  ; Just owner => case canonicalWorkRankSegments name key world error value nameEq fixedOrder rest of
    { [] => [[length (takeWhile (\candidate => case decEq candidate owner of { Yes same => False ; No distinct => True }) fixedOrder)]]
    ; segment :: later => (length (takeWhile (\candidate => case decEq candidate owner of { Yes same => False ; No distinct => True }) fixedOrder) :: segment) :: later
    }
  }.

DGamma.CP5ConfluenceCanonicalSortSpike:5036:3--5037:86
 5036 |   cong (canonicalWorkRankStep name key world error value nameEq fixedOrder (transitionAction step))
 5037 |     (canonicalWorkRankSegmentsFold name key world error value nameEq fixedOrder rest)



```

## C4-2 — positive

```text
START C4-2 2026-09-07T02:08:40.058222+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
END {"unit": "C4-2", "start": "2026-09-07T02:08:40.058222+00:00", "end": "2026-09-07T02:09:35.055542+00:00", "exit": 0, "maxSampleRSSKiB": 18185536, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr", "diagnosticErrors": false}
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted



```

## C5-1 — positive

```text
START C5-1 2026-09-07T02:09:56.834646+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
END {"unit": "C5-1", "start": "2026-09-07T02:09:56.834646+00:00", "end": "2026-09-07T02:10:53.822144+00:00", "exit": 0, "maxSampleRSSKiB": 18071952, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr", "diagnosticErrors": false}
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted



```

## C6-1 — positive

```text
START C6-1 2026-09-07T02:11:17.798279+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
END {"unit": "C6-1", "start": "2026-09-07T02:11:17.798279+00:00", "end": "2026-09-07T02:12:12.784737+00:00", "exit": 0, "maxSampleRSSKiB": 18090784, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr", "diagnosticErrors": false}
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted



```

## C7-1 — positive

```text
START C7-1 2026-09-07T02:13:11.351675+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
END {"unit": "C7-1", "start": "2026-09-07T02:13:11.351675+00:00", "end": "2026-09-07T02:14:08.398305+00:00", "exit": 0, "maxSampleRSSKiB": 20116064, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr", "diagnosticErrors": false}
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted



```

## C8-1 — charged-proof-rejection

```text
START C8-1 2026-09-07T02:15:00.951098+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
END {"unit": "C8-1", "start": "2026-09-07T02:15:00.951098+00:00", "end": "2026-09-07T02:15:55.990107+00:00", "exit": 1, "maxSampleRSSKiB": 17955968, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr", "diagnosticErrors": true}
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  rankInversions is shadowing DGamma.CP5ConfluenceWorkMeasureSpike.rankInversions

DGamma.CP5ConfluenceCanonicalSortSpike:5170:3--5196:125
 5170 | 0 canonicalWorkAcceptedResultInversionMeasure :
 5171 |   (name, key, world, error : Type) -> (value : key -> Type) ->
 5172 |   (nameEq : DecEq name) -> (keyEq : DecEq key) ->
 5173 |   (protocol : RegistrationProtocol key value world error) ->
 5174 |   {initial, originalFinal : SystemState name key value world error} ->
 5175 |   (original : Transitions initial originalFinal) ->

Error: While processing right hand side of canonicalWorkAcceptedResultInversionMeasure. Can't solve constraint between: rankInversions and rankInversions.

DGamma.CP5ConfluenceCanonicalSortSpike:5199:5--5202:54
 5199 |     cong (\segments => foldr (+) Z (map rankInversions segments))
 5200 |       (canonicalWorkAdjacentTargetRankFold name key world error value nameEq keyEq protocol
 5201 |         (orderedSupportNames ordering) (sortingCurrentTrace (workReachedReplay current))
 5202 |         prefixTrace left right suffix diamond result)



```

## C8-2 — positive

```text
START C8-2 2026-09-07T02:16:34.473427+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
END {"unit": "C8-2", "start": "2026-09-07T02:16:34.473427+00:00", "end": "2026-09-07T02:17:31.488230+00:00", "exit": 0, "maxSampleRSSKiB": 20151984, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr", "diagnosticErrors": false}
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted



```

## C9-1 — positive

```text
START C9-1 2026-09-07T02:17:52.862479+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceWorkMeasureSpike.idr
END {"unit": "C9-1", "start": "2026-09-07T02:17:52.862479+00:00", "end": "2026-09-07T02:17:54.898647+00:00", "exit": 0, "maxSampleRSSKiB": 0, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceWorkMeasureSpike.idr", "diagnosticErrors": false}
1/1: Building DGamma.CP5ConfluenceWorkMeasureSpike (research/DGamma/CP5ConfluenceWorkMeasureSpike.idr)


```

## C10-1 — positive

```text
START C10-1 2026-09-07T02:18:19.682817+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceWorkMeasureSpike.idr
END {"unit": "C10-1", "start": "2026-09-07T02:18:19.682817+00:00", "end": "2026-09-07T02:18:21.745388+00:00", "exit": 0, "maxSampleRSSKiB": 0, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceWorkMeasureSpike.idr", "diagnosticErrors": false}
1/1: Building DGamma.CP5ConfluenceWorkMeasureSpike (research/DGamma/CP5ConfluenceWorkMeasureSpike.idr)


```

## C11-1 — charged-proof-rejection

```text
START C11-1 2026-09-07T02:19:00.377386+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
END {"unit": "C11-1", "start": "2026-09-07T02:19:00.377386+00:00", "end": "2026-09-07T02:19:55.364363+00:00", "exit": 1, "maxSampleRSSKiB": 17970416, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr", "diagnosticErrors": true}
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted

Error: While processing right hand side of canonicalWorkRankStepProgress. Can't solve constraint between: rankedPrefix (rankLiftProgress (length (takeWhile (\candidate => case decEq candidate parent of { Yes same => False ; No distinct => True }) fixedOrder)) sourceHead progress) ++ (rankedRight (rankLiftProgress (length (takeWhile (\candidate => case decEq candidate parent of { Yes same => False ; No distinct => True }) fixedOrder)) sourceHead progress) :: (rankedLeft (rankLiftProgress (length (takeWhile (\candidate => case decEq candidate parent of { Yes same => False ; No distinct => True }) fixedOrder)) sourceHead progress) :: rankedSuffix (rankLiftProgress (length (takeWhile (\candidate => case decEq candidate parent of { Yes same => False ; No distinct => True }) fixedOrder)) sourceHead progress))) and length (takeWhile (\candidate => case decEq candidate parent of { Yes same => False ; No distinct => True }) fixedOrder) :: (rankedPrefix progress ++ (rankedRight progress :: (rankedLeft progress :: rankedSuffix progress))).

DGamma.CP5ConfluenceCanonicalSortSpike:5224:5--5226:61
 5224 |     FirstRankSegment later (rankLiftProgress (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
 5225 |       Yes same => False
 5226 |       No distinct => True) fixedOrder)) sourceHead progress)



```

## C11-2 — charged-proof-rejection

```text
START C11-2 2026-09-07T02:20:50.758772+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
END {"unit": "C11-2", "start": "2026-09-07T02:20:50.758772+00:00", "end": "2026-09-07T02:21:45.751546+00:00", "exit": 1, "maxSampleRSSKiB": 17952400, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr", "diagnosticErrors": true}
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted

Error: While processing right hand side of canonicalWorkRankStepProgress. Rewriting by foldr (+) 0 (map (rankCrossing ?pivot) sourceHead) = foldr (+) 0 (map (rankCrossing ?pivot) (prior ++ (upper :: (lower :: suffix)))) did not change type rankInversions (length (takeWhile (\candidate => let 0 target = (rankedPrefix (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) ++ (rankedRight (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) :: (rankedLeft (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) :: rankedSuffix (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased)))) :: later in let 0 source = sourceHead :: later in case decEq candidate parent of { Yes same => False ; No distinct => True }) fixedOrder) :: sourceHead) = S (rankInversions ((length (takeWhile (\candidate => let 0 target = (rankedPrefix (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) ++ (rankedRight (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) :: (rankedLeft (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) :: rankedSuffix (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased)))) :: later in let 0 source = sourceHead :: later in case decEq candidate parent of { Yes same => False ; No distinct => True }) fixedOrder) :: prior) ++ (upper :: (lower :: suffix)))).

DGamma.CP5ConfluenceCanonicalSortSpike:5233:8--5241:65
 5233 |       (rewrite weights (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
 5234 |         Yes same => False
 5235 |         No distinct => True) fixedOrder)) in
 5236 |        rewrite decreased in
 5237 |          sym (plusSuccRightSucc
 5238 |            (foldr (+) Z (map (rankCrossing (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of



```

## C11-3 — charged-proof-rejection

```text
START C11-3 2026-09-07T02:22:37.745629+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
END {"unit": "C11-3", "start": "2026-09-07T02:22:37.745629+00:00", "end": "2026-09-07T02:23:32.738640+00:00", "exit": 1, "maxSampleRSSKiB": 17951024, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr", "diagnosticErrors": true}
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted

Error: While processing right hand side of canonicalWorkRankStepProgress. Rewriting by foldr (+) 0 (map (rankCrossing ?pivot) sourceHead) = foldr (+) 0 (map (rankCrossing ?pivot) (prior ++ (upper :: (lower :: suffix)))) did not change type rankInversions (length (takeWhile (\candidate => let 0 target = (rankedPrefix (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) ++ (rankedRight (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) :: (rankedLeft (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) :: rankedSuffix (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased)))) :: later in let 0 source = sourceHead :: later in case decEq candidate parent of { Yes same => False ; No distinct => True }) fixedOrder) :: sourceHead) = S (rankInversions ((length (takeWhile (\candidate => let 0 target = (rankedPrefix (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) ++ (rankedRight (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) :: (rankedLeft (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) :: rankedSuffix (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased)))) :: later in let 0 source = sourceHead :: later in case decEq candidate parent of { Yes same => False ; No distinct => True }) fixedOrder) :: prior) ++ (upper :: (lower :: suffix)))).

DGamma.CP5ConfluenceCanonicalSortSpike:5235:8--5243:65
 5235 |       (rewrite weights (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
 5236 |         Yes same => False
 5237 |         No distinct => True) fixedOrder)) in
 5238 |        rewrite decreased in
 5239 |          sym (plusSuccRightSucc
 5240 |            (foldr (+) Z (map (rankCrossing (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of



```

## gate-package — positive

```text
START gate-package 2026-09-07T02:33:13.296221+00:00 idris2 --build dgamma.ipkg
END {"unit": "gate-package", "start": "2026-09-07T02:33:13.296221+00:00", "end": "2026-09-07T02:33:29.570046+00:00", "exit": 0, "maxSampleRSSKiB": 219936, "cmd": "idris2 --build dgamma.ipkg", "diagnosticErrors": false}


```

## Initial Unit A boundary batch

```text
START idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
7/7: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4657:3--4661:39
 4657 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4658 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4659 |     nameEq keyEq original reduction ordering sorted) ->
 4660 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4661 |     original reduction ordering sorted


RESULT {"path": "research/DGamma/CP5ConfluenceCanonicalSortSpike.idr", "command": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr", "exit": 0, "seconds": 54.72510313987732, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
8/8: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)

RESULT {"path": "research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr", "command": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr", "exit": 0, "seconds": 7.500378847122192, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCrossTraceSpike.idr
9/9: Building DGamma.CP5ConfluenceCrossTraceSpike (research/DGamma/CP5ConfluenceCrossTraceSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:40:3--40:68
 36 | 
 37 | public export
 38 | data CertifiedActorPermutation :
 39 |   (name : Type) -> List name -> List name -> Type where
 40 |   ActorPermutationDone : CertifiedActorPermutation name order order
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:41:3--44:48
 41 |   ActorPermutationStep :
 42 |     AdjacentActorOrderSwap name before middle ->
 43 |     CertifiedActorPermutation name middle after ->
 44 |     CertifiedActorPermutation name before after

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:274:1--277:77
 274 | transitionPrefixLength : (earlierTrace : Transitions initial before) ->
 275 |   (step : Transition before after) ->
 276 |   transitionCount (appendTransitions earlierTrace
 277 |     (MoreTransitions step NoTransitions)) = S (transitionCount earlierTrace)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:736:3--742:55
 736 |   OperationalActorDone :
 737 |     (blocks : ActorBlockDecomposition name key world error value nameEq keyEq
 738 |       order trace) ->
 739 |     (premises : ReplayInvariantBundle name key world error value protocol nameEq
 740 |       keyEq trace) ->
 741 |     OperationalActorPermutation name key world error value protocol nameEq keyEq

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:743:3--759:35
 743 |   OperationalActorStep :
 744 |     (orderSwap : AdjacentActorOrderSwap name before middle) ->
 745 |     (restCertificate : CertifiedActorPermutation name middle after) ->
 746 |     (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
 747 |       before sourceTrace) ->
 748 |     (sourcePremises : ReplayInvariantBundle name key world error value protocol

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1219:3--1227:41
 1219 | 0 permutationReplayCorrespondence :
 1220 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1221 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1222 |       rightCapital matching} ->
 1223 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1224 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1233:3--1241:41
 1233 | 0 permutationOccurrenceCorrespondence :
 1234 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1235 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1236 |       rightCapital matching} ->
 1237 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1238 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->


RESULT {"path": "research/DGamma/CP5ConfluenceCrossTraceSpike.idr", "command": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCrossTraceSpike.idr", "exit": 0, "seconds": 4.841932773590088, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --check research/DGamma/CP5UniqueRawNameCanonicalCapital.idr
11/11: Building DGamma.CP5UniqueRawNameCanonicalCapital (research/DGamma/CP5UniqueRawNameCanonicalCapital.idr)

RESULT {"path": "research/DGamma/CP5UniqueRawNameCanonicalCapital.idr", "command": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5UniqueRawNameCanonicalCapital.idr", "exit": 0, "seconds": 2.1481451988220215, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176CanonicalPermutationUniquePositive.idr
1/1: Building DGamma.R176CanonicalPermutationUniquePositive (research-tests/DGamma/R176CanonicalPermutationUniquePositive.idr)

RESULT {"path": "research-tests/DGamma/R176CanonicalPermutationUniquePositive.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176CanonicalPermutationUniquePositive.idr", "exit": 0, "seconds": 1.558007001876831, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R173UniqueRawNameInsertionsFixtures.idr
3/3: Building DGamma.R173UniqueRawNameInsertionsFixtures (research-tests/DGamma/R173UniqueRawNameInsertionsFixtures.idr)

RESULT {"path": "research-tests/DGamma/R173UniqueRawNameInsertionsFixtures.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R173UniqueRawNameInsertionsFixtures.idr", "exit": 0, "seconds": 2.0307018756866455, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R174O17ProvisionCollisionUnique.idr
2/2: Building DGamma.R174O17ProvisionCollisionUnique (research-tests/DGamma/R174O17ProvisionCollisionUnique.idr)

RESULT {"path": "research-tests/DGamma/R174O17ProvisionCollisionUnique.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R174O17ProvisionCollisionUnique.idr", "exit": 0, "seconds": 0.9714429378509521, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R8FullPipeline.idr
1/1: Building DGamma.R8FullPipeline (research-tests/DGamma/R8FullPipeline.idr)

RESULT {"path": "research-tests/DGamma/R8FullPipeline.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R8FullPipeline.idr", "exit": 0, "seconds": 100.28090405464172, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R16ConfluenceTheoremAssemblyPositive.idr
2/2: Building DGamma.R16ConfluenceTheoremAssemblyPositive (research-tests/DGamma/R16ConfluenceTheoremAssemblyPositive.idr)

RESULT {"path": "research-tests/DGamma/R16ConfluenceTheoremAssemblyPositive.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R16ConfluenceTheoremAssemblyPositive.idr", "exit": 0, "seconds": 1.8624379634857178, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R4ScannerProducerConsumers.idr
1/1: Building DGamma.R4ScannerProducerConsumers (research-tests/DGamma/R4ScannerProducerConsumers.idr)

RESULT {"path": "research-tests/DGamma/R4ScannerProducerConsumers.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R4ScannerProducerConsumers.idr", "exit": 0, "seconds": 1.4721331596374512, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176BareCapitalFreshnessNegative.idr
1/1: Building DGamma.R176BareCapitalFreshnessNegative (research-tests/DGamma/R176BareCapitalFreshnessNegative.idr)
Error: While processing right hand side of bareCapitalCannotSupplyFreshness. When unifying:
    TraceIndependent name key world error value keyEq initial originalFinal original
and:
    UniqueRawNameInsertions name key world error value nameEq keyEq original
Mismatch between: TraceIndependent name key world error value keyEq initial originalFinal original and UniqueRawNameInsertions name key world error value nameEq keyEq original.

DGamma.R176BareCapitalFreshnessNegative:26:6--26:38
 22 |   (UniqueRawNameInsertions name key world error value nameEq keyEq
 23 |     (canonicalTrace (canonicalSchedule capital)))
 24 | bareCapitalCannotSupplyFreshness name key world error value protocol nameEq keyEq capital =
 25 |   capitalCanonicalUniqueInsertions name key world error value protocol nameEq keyEq capital
 26 |     (originalTraceIndependent capital)
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


RESULT {"path": "research-tests/DGamma/R176BareCapitalFreshnessNegative.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176BareCapitalFreshnessNegative.idr", "exit": 1, "seconds": 0.29958200454711914, "fresh": true, "expectedDiagnostic": "Mismatch between: TraceIndependent", "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176WrongOriginalTraceUniqueNegative.idr
1/1: Building DGamma.R176WrongOriginalTraceUniqueNegative (research-tests/DGamma/R176WrongOriginalTraceUniqueNegative.idr)
Error: While processing right hand side of wrongOriginalTraceFreshness. When unifying:
    UniqueRawNameInsertions name key world error value nameEq keyEq otherTrace
and:
    UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace
Mismatch between: otherTrace and leftTrace.

DGamma.R176WrongOriginalTraceUniqueNegative:37:43--37:54
 33 |     (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)
 34 | wrongOriginalTraceFreshness name key world error value nameEq keyEq protocol leftTrace rightTrace
 35 |   otherTrace sameInputs leftCapital rightCapital otherUnique rightUnique =
 36 |     canonicalSupportOrdersMatchSpike nameEq keyEq protocol leftTrace rightTrace
 37 |       sameInputs leftCapital rightCapital otherUnique rightUnique
                                                ^^^^^^^^^^^


RESULT {"path": "research-tests/DGamma/R176WrongOriginalTraceUniqueNegative.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176WrongOriginalTraceUniqueNegative.idr", "exit": 1, "seconds": 0.3029007911682129, "fresh": true, "expectedDiagnostic": "Mismatch between: otherTrace and leftTrace.", "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176UnsealedOriginUniqueNegative.idr
1/1: Building DGamma.R176UnsealedOriginUniqueNegative (research-tests/DGamma/R176UnsealedOriginUniqueNegative.idr)
Error: While processing right hand side of unsealedOriginCannotTransportUnique. When unifying:
    ActionRegistrationReplayCorrespondence name key world error value source target
and:
    FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq ?source ?target
Mismatch between: ActionRegistrationReplayCorrespondence name key world error value source target and FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq ?source ?target.

DGamma.R176UnsealedOriginUniqueNegative:24:90--24:96
 20 |   (origin : ActionRegistrationReplayCorrespondence name key world error value source target) ->
 21 |   (UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
 22 |   (UniqueRawNameInsertions name key world error value nameEq keyEq target)
 23 | unsealedOriginCannotTransportUnique name key world error value protocol nameEq keyEq origin unique =
 24 |   uniqueInsertionsAfterFiniteDerivation name key world error value protocol nameEq keyEq origin unique
                                                                                               ^^^^^^


RESULT {"path": "research-tests/DGamma/R176UnsealedOriginUniqueNegative.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176UnsealedOriginUniqueNegative.idr", "exit": 1, "seconds": 0.44910478591918945, "fresh": true, "expectedDiagnostic": "Mismatch between: ActionRegistrationReplayCorrespondence", "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176ReductionUniqueDirectionNegative.idr
1/1: Building DGamma.R176ReductionUniqueDirectionNegative (research-tests/DGamma/R176ReductionUniqueDirectionNegative.idr)
Error: While processing right hand side of reductionUniqueCannotRunBackward. Can't solve constraint between: reduction .reducedFinal and originalFinal.

DGamma.R176ReductionUniqueDirectionNegative:25:93--25:106
 21 |   (reduction : ClosingFreeReduction name key world error value protocol nameEq keyEq original) ->
 22 |   (UniqueRawNameInsertions name key world error value nameEq keyEq (reducedTrace reduction)) ->
 23 |   (UniqueRawNameInsertions name key world error value nameEq keyEq (reducedTrace reduction))
 24 | reductionUniqueCannotRunBackward name key world error value protocol nameEq keyEq reduction reducedUnique =
 25 |   uniqueInsertionsAfterReduction name key world error value nameEq keyEq protocol reduction reducedUnique
                                                                                                  ^^^^^^^^^^^^^


RESULT {"path": "research-tests/DGamma/R176ReductionUniqueDirectionNegative.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176ReductionUniqueDirectionNegative.idr", "exit": 1, "seconds": 0.37903714179992676, "fresh": true, "expectedDiagnostic": "reduction .reducedFinal and originalFinal", "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R6OldPollutionNegative.idr
1/1: Building DGamma.R6OldPollutionNegative (research-tests/DGamma/R6OldPollutionNegative.idr)
Error: While processing right hand side of oldPollutionReachesO20. When unifying:
    CertifiedActorPermutation name (supportOrder (canonicalSchedule leftCapital)) (map (renameBackward (currentNameBijection (endpointRenaming sameInputs))) (supportOrder (canonicalSchedule rightCapital)))
and:
    CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital ?matching
Mismatch between: CertifiedActorPermutation name (supportOrder (canonicalSchedule leftCapital)) (map (renameBackward (currentNameBijection (endpointRenaming sameInputs))) (supportOrder (canonicalSchedule rightCapital))) and CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital ?matching.

DGamma.R6OldPollutionNegative:45:77--45:85
 41 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational)
 42 | oldPollutionReachesO20 {nameEq} {keyEq} {protocol} {leftTrace} {rightTrace}
 43 |   {sameInputs} {leftCapital} {rightCapital} leftUnique rightUnique matching polluted =
 44 |     (polluted ** canonicalSchedulesConvergeSpike nameEq keyEq protocol leftTrace
 45 |       rightTrace sameInputs leftCapital rightCapital leftUnique rightUnique polluted)
                                                                                  ^^^^^^^^


RESULT {"path": "research-tests/DGamma/R6OldPollutionNegative.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R6OldPollutionNegative.idr", "exit": 1, "seconds": 0.3643321990966797, "fresh": true, "expectedDiagnostic": "Mismatch between: CertifiedActorPermutation", "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R6MixedScheduleNegative.idr
1/1: Building DGamma.R6MixedScheduleNegative (research-tests/DGamma/R6MixedScheduleNegative.idr)
Error: While processing right hand side of mixedLeftSchedule. When unifying:
    CanonicalConvergenceResult name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital operational
and:
    CanonicalConvergenceResult name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs otherLeft rightCapital operational
Mismatch between: leftCapital and otherLeft.

DGamma.R6MixedScheduleNegative:37:64--37:75
 33 |     (currentNameBijection (endpointRenaming sameInputs))
 34 | mixedLeftSchedule {nameEq} {keyEq} {protocol} {leftTrace} {rightTrace} {sameInputs}
 35 |   leftCapital otherLeft rightCapital leftUnique rightUnique convergence =
 36 |     originalEndpointsConvergeSpike nameEq keyEq protocol leftTrace rightTrace
 37 |       sameInputs otherLeft rightCapital leftUnique rightUnique convergence
                                                                     ^^^^^^^^^^^


RESULT {"path": "research-tests/DGamma/R6MixedScheduleNegative.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R6MixedScheduleNegative.idr", "exit": 1, "seconds": 0.3156266212463379, "fresh": true, "expectedDiagnostic": "Mismatch between: leftCapital and otherLeft.", "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R8WrongTraceBridgeNegative.idr
1/1: Building DGamma.R8WrongTraceBridgeNegative (research-tests/DGamma/R8WrongTraceBridgeNegative.idr)
Error: While processing right hand side of wrongTraceBridge. Can't solve constraint between: operational .operationalTargetFinal and otherFinal.

DGamma.R8WrongTraceBridgeNegative:36:60--36:89
 32 |     (canonicalTrace (canonicalSchedule leftCapital)) otherTrace) ->
 33 |   ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
 34 |     leftTrace rightTrace sameInputs leftCapital otherTrace otherOccurrences
 35 |     rightCapital
 36 | wrongTraceBridge convergence otherTrace otherOccurrences = convergenceBridge convergence
                                                                 ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


RESULT {"path": "research-tests/DGamma/R8WrongTraceBridgeNegative.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R8WrongTraceBridgeNegative.idr", "exit": 1, "seconds": 0.4860978126525879, "fresh": true, "expectedDiagnostic": "operationalTargetFinal and otherFinal", "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R8WrongOccurrenceBridgeNegative.idr
1/1: Building DGamma.R8WrongOccurrenceBridgeNegative (research-tests/DGamma/R8WrongOccurrenceBridgeNegative.idr)
Error: While processing right hand side of detachBridgeOccurrenceRelation. When unifying:
    ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital replayed first rightCapital
and:
    ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital replayed second rightCapital
Mismatch between: first and second.

DGamma.R8WrongOccurrenceBridgeNegative:32:54--32:60
 28 |   ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
 29 |     leftTrace rightTrace sameInputs leftCapital replayed first rightCapital ->
 30 |   ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
 31 |     leftTrace rightTrace sameInputs leftCapital replayed second rightCapital
 32 | detachBridgeOccurrenceRelation first second bridge = bridge
                                                           ^^^^^^


RESULT {"path": "research-tests/DGamma/R8WrongOccurrenceBridgeNegative.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R8WrongOccurrenceBridgeNegative.idr", "exit": 1, "seconds": 0.47641825675964355, "fresh": true, "expectedDiagnostic": "first and second", "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R11BridgeWrongGenerationNegative.idr
1/1: Building DGamma.R11BridgeWrongGenerationNegative (research-tests/DGamma/R11BridgeWrongGenerationNegative.idr)
Error: While processing right hand side of arbitraryRightBirthCannotSatisfyBridgeGeneration. Can't solve constraint between: MkRegistrationGeneration (renameForward (currentNameBijection (endpointRenaming sameInputs)) child) (registrationOrdinal (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence rightCapital) rightBirth)) and (generatedGenerationBijection sameInputs) .generationForward (registrationGeneration (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence leftCapital) leftBirth)).

DGamma.R11BridgeWrongGenerationNegative:42:26--42:30
 38 |       (canonicalOccurrenceCorrespondence leftCapital) leftBirth)) =
 39 |   registrationGeneration (replayGeneratedRegistrationOrigin
 40 |     (canonicalOccurrenceCorrespondence rightCapital) rightBirth)
 41 | arbitraryRightBirthCannotSatisfyBridgeGeneration sameInputs leftCapital rightCapital
 42 |   leftBirth rightBirth = Refl
                               ^^^^


RESULT {"path": "research-tests/DGamma/R11BridgeWrongGenerationNegative.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R11BridgeWrongGenerationNegative.idr", "exit": 1, "seconds": 0.5066351890563965, "fresh": true, "expectedDiagnostic": "generatedGenerationBijection sameInputs", "passed": true}
PASS: 10 positive fresh checks; 9 exact diagnostic-negative fresh checks

```

## Final boundary batch after ratified C11 stop

```text
START idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceWorkMeasureSpike.idr
1/1: Building DGamma.CP5ConfluenceWorkMeasureSpike (research/DGamma/CP5ConfluenceWorkMeasureSpike.idr)

RESULT {"path": "research/DGamma/CP5ConfluenceWorkMeasureSpike.idr", "command": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceWorkMeasureSpike.idr", "exit": 0, "seconds": 1.0530941486358643, "start": "2026-09-07T02:27:39.255935+00:00", "end": "2026-09-07T02:27:40.309030+00:00", "maxSampleRSSKiB": 0, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr
5/5: Building DGamma.CP5ConfluenceDeletionChainSpike (research/DGamma/CP5ConfluenceDeletionChainSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  surviving is shadowing DGamma.CP4DeletionGenerationFilter.GenerationFilterResult.surviving

DGamma.CP5ConfluenceDeletionChainSpike:3013:1--3015:19
 3013 | generationSubsequenceSourceOrdinal :
 3014 |   GenerationActionSubsequence nameEq deletable ordinal live original surviving ->
 3015 |   Nat -> Maybe Nat


RESULT {"path": "research/DGamma/CP5ConfluenceDeletionChainSpike.idr", "command": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr", "exit": 0, "seconds": 78.69857811927795, "start": "2026-09-07T02:27:40.336993+00:00", "end": "2026-09-07T02:28:59.035571+00:00", "maxSampleRSSKiB": 4981616, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted


RESULT {"path": "research/DGamma/CP5ConfluenceCanonicalSortSpike.idr", "command": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr", "exit": 0, "seconds": 55.932796001434326, "start": "2026-09-07T02:28:59.063214+00:00", "end": "2026-09-07T02:29:54.996011+00:00", "maxSampleRSSKiB": 20150224, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
9/9: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)

RESULT {"path": "research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr", "command": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr", "exit": 0, "seconds": 8.274405241012573, "start": "2026-09-07T02:29:55.024765+00:00", "end": "2026-09-07T02:30:03.299172+00:00", "maxSampleRSSKiB": 2923424, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCrossTraceSpike.idr
10/10: Building DGamma.CP5ConfluenceCrossTraceSpike (research/DGamma/CP5ConfluenceCrossTraceSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:40:3--40:68
 36 | 
 37 | public export
 38 | data CertifiedActorPermutation :
 39 |   (name : Type) -> List name -> List name -> Type where
 40 |   ActorPermutationDone : CertifiedActorPermutation name order order
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:41:3--44:48
 41 |   ActorPermutationStep :
 42 |     AdjacentActorOrderSwap name before middle ->
 43 |     CertifiedActorPermutation name middle after ->
 44 |     CertifiedActorPermutation name before after

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:274:1--277:77
 274 | transitionPrefixLength : (earlierTrace : Transitions initial before) ->
 275 |   (step : Transition before after) ->
 276 |   transitionCount (appendTransitions earlierTrace
 277 |     (MoreTransitions step NoTransitions)) = S (transitionCount earlierTrace)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:736:3--742:55
 736 |   OperationalActorDone :
 737 |     (blocks : ActorBlockDecomposition name key world error value nameEq keyEq
 738 |       order trace) ->
 739 |     (premises : ReplayInvariantBundle name key world error value protocol nameEq
 740 |       keyEq trace) ->
 741 |     OperationalActorPermutation name key world error value protocol nameEq keyEq

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:743:3--759:35
 743 |   OperationalActorStep :
 744 |     (orderSwap : AdjacentActorOrderSwap name before middle) ->
 745 |     (restCertificate : CertifiedActorPermutation name middle after) ->
 746 |     (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
 747 |       before sourceTrace) ->
 748 |     (sourcePremises : ReplayInvariantBundle name key world error value protocol

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1219:3--1227:41
 1219 | 0 permutationReplayCorrespondence :
 1220 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1221 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1222 |       rightCapital matching} ->
 1223 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1224 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1233:3--1241:41
 1233 | 0 permutationOccurrenceCorrespondence :
 1234 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1235 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1236 |       rightCapital matching} ->
 1237 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1238 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->


RESULT {"path": "research/DGamma/CP5ConfluenceCrossTraceSpike.idr", "command": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCrossTraceSpike.idr", "exit": 0, "seconds": 5.189213991165161, "start": "2026-09-07T02:30:03.328451+00:00", "end": "2026-09-07T02:30:08.517666+00:00", "maxSampleRSSKiB": 3370128, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --check research/DGamma/CP5UniqueRawNameCanonicalCapital.idr
11/12: Building DGamma.CP5UniqueRawNameDeletion (research/DGamma/CP5UniqueRawNameDeletion.idr)
12/12: Building DGamma.CP5UniqueRawNameCanonicalCapital (research/DGamma/CP5UniqueRawNameCanonicalCapital.idr)

RESULT {"path": "research/DGamma/CP5UniqueRawNameCanonicalCapital.idr", "command": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5UniqueRawNameCanonicalCapital.idr", "exit": 0, "seconds": 3.1050379276275635, "start": "2026-09-07T02:30:08.545294+00:00", "end": "2026-09-07T02:30:11.650331+00:00", "maxSampleRSSKiB": 738736, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176CanonicalPermutationUniquePositive.idr
1/1: Building DGamma.R176CanonicalPermutationUniquePositive (research-tests/DGamma/R176CanonicalPermutationUniquePositive.idr)

RESULT {"path": "research-tests/DGamma/R176CanonicalPermutationUniquePositive.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176CanonicalPermutationUniquePositive.idr", "exit": 0, "seconds": 2.0780160427093506, "start": "2026-09-07T02:30:11.678192+00:00", "end": "2026-09-07T02:30:13.756208+00:00", "maxSampleRSSKiB": 1726944, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R173UniqueRawNameInsertionsFixtures.idr
1/3: Building DGamma.R45BareDiamondDisciplineCounterexamplePositive (research-tests/DGamma/R45BareDiamondDisciplineCounterexamplePositive.idr)
2/3: Building DGamma.R172O17OpenParentRootReuseCandidate (research-tests/DGamma/R172O17OpenParentRootReuseCandidate.idr)
3/3: Building DGamma.R173UniqueRawNameInsertionsFixtures (research-tests/DGamma/R173UniqueRawNameInsertionsFixtures.idr)

RESULT {"path": "research-tests/DGamma/R173UniqueRawNameInsertionsFixtures.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R173UniqueRawNameInsertionsFixtures.idr", "exit": 0, "seconds": 52.78791284561157, "start": "2026-09-07T02:30:13.784262+00:00", "end": "2026-09-07T02:31:06.572176+00:00", "maxSampleRSSKiB": 3072192, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R174O17ProvisionCollisionUnique.idr
1/2: Building DGamma.R174O17ProvisionCollisionCandidate (research-tests/DGamma/R174O17ProvisionCollisionCandidate.idr)
2/2: Building DGamma.R174O17ProvisionCollisionUnique (research-tests/DGamma/R174O17ProvisionCollisionUnique.idr)

RESULT {"path": "research-tests/DGamma/R174O17ProvisionCollisionUnique.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R174O17ProvisionCollisionUnique.idr", "exit": 0, "seconds": 2.085549831390381, "start": "2026-09-07T02:31:06.599529+00:00", "end": "2026-09-07T02:31:08.685079+00:00", "maxSampleRSSKiB": 798384, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R8FullPipeline.idr
1/1: Building DGamma.R8FullPipeline (research-tests/DGamma/R8FullPipeline.idr)

RESULT {"path": "research-tests/DGamma/R8FullPipeline.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R8FullPipeline.idr", "exit": 0, "seconds": 99.45320916175842, "start": "2026-09-07T02:31:08.715781+00:00", "end": "2026-09-07T02:32:48.168989+00:00", "maxSampleRSSKiB": 40010688, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R16ConfluenceTheoremAssemblyPositive.idr
2/2: Building DGamma.R16ConfluenceTheoremAssemblyPositive (research-tests/DGamma/R16ConfluenceTheoremAssemblyPositive.idr)

RESULT {"path": "research-tests/DGamma/R16ConfluenceTheoremAssemblyPositive.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R16ConfluenceTheoremAssemblyPositive.idr", "exit": 0, "seconds": 2.072503089904785, "start": "2026-09-07T02:32:48.197400+00:00", "end": "2026-09-07T02:32:50.269903+00:00", "maxSampleRSSKiB": 944512, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R4ScannerProducerConsumers.idr
1/1: Building DGamma.R4ScannerProducerConsumers (research-tests/DGamma/R4ScannerProducerConsumers.idr)

RESULT {"path": "research-tests/DGamma/R4ScannerProducerConsumers.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R4ScannerProducerConsumers.idr", "exit": 0, "seconds": 2.08186411857605, "start": "2026-09-07T02:32:50.297718+00:00", "end": "2026-09-07T02:32:52.379582+00:00", "maxSampleRSSKiB": 3909520, "fresh": true, "expectedDiagnostic": null, "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176BareCapitalFreshnessNegative.idr
1/1: Building DGamma.R176BareCapitalFreshnessNegative (research-tests/DGamma/R176BareCapitalFreshnessNegative.idr)
Error: While processing right hand side of bareCapitalCannotSupplyFreshness. When unifying:
    TraceIndependent name key world error value keyEq initial originalFinal original
and:
    UniqueRawNameInsertions name key world error value nameEq keyEq original
Mismatch between: TraceIndependent name key world error value keyEq initial originalFinal original and UniqueRawNameInsertions name key world error value nameEq keyEq original.

DGamma.R176BareCapitalFreshnessNegative:26:6--26:38
 22 |   (UniqueRawNameInsertions name key world error value nameEq keyEq
 23 |     (canonicalTrace (canonicalSchedule capital)))
 24 | bareCapitalCannotSupplyFreshness name key world error value protocol nameEq keyEq capital =
 25 |   capitalCanonicalUniqueInsertions name key world error value protocol nameEq keyEq capital
 26 |     (originalTraceIndependent capital)
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


RESULT {"path": "research-tests/DGamma/R176BareCapitalFreshnessNegative.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176BareCapitalFreshnessNegative.idr", "exit": 1, "seconds": 1.034696340560913, "start": "2026-09-07T02:32:52.407573+00:00", "end": "2026-09-07T02:32:53.442270+00:00", "maxSampleRSSKiB": 0, "fresh": true, "expectedDiagnostic": "Mismatch between: TraceIndependent", "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176WrongOriginalTraceUniqueNegative.idr
1/1: Building DGamma.R176WrongOriginalTraceUniqueNegative (research-tests/DGamma/R176WrongOriginalTraceUniqueNegative.idr)
Error: While processing right hand side of wrongOriginalTraceFreshness. When unifying:
    UniqueRawNameInsertions name key world error value nameEq keyEq otherTrace
and:
    UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace
Mismatch between: otherTrace and leftTrace.

DGamma.R176WrongOriginalTraceUniqueNegative:37:43--37:54
 33 |     (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)
 34 | wrongOriginalTraceFreshness name key world error value nameEq keyEq protocol leftTrace rightTrace
 35 |   otherTrace sameInputs leftCapital rightCapital otherUnique rightUnique =
 36 |     canonicalSupportOrdersMatchSpike nameEq keyEq protocol leftTrace rightTrace
 37 |       sameInputs leftCapital rightCapital otherUnique rightUnique
                                                ^^^^^^^^^^^


RESULT {"path": "research-tests/DGamma/R176WrongOriginalTraceUniqueNegative.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176WrongOriginalTraceUniqueNegative.idr", "exit": 1, "seconds": 1.059027910232544, "start": "2026-09-07T02:32:53.469657+00:00", "end": "2026-09-07T02:32:54.528686+00:00", "maxSampleRSSKiB": 0, "fresh": true, "expectedDiagnostic": "Mismatch between: otherTrace and leftTrace.", "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176UnsealedOriginUniqueNegative.idr
1/1: Building DGamma.R176UnsealedOriginUniqueNegative (research-tests/DGamma/R176UnsealedOriginUniqueNegative.idr)
Error: While processing right hand side of unsealedOriginCannotTransportUnique. When unifying:
    ActionRegistrationReplayCorrespondence name key world error value source target
and:
    FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq ?source ?target
Mismatch between: ActionRegistrationReplayCorrespondence name key world error value source target and FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq ?source ?target.

DGamma.R176UnsealedOriginUniqueNegative:24:90--24:96
 20 |   (origin : ActionRegistrationReplayCorrespondence name key world error value source target) ->
 21 |   (UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
 22 |   (UniqueRawNameInsertions name key world error value nameEq keyEq target)
 23 | unsealedOriginCannotTransportUnique name key world error value protocol nameEq keyEq origin unique =
 24 |   uniqueInsertionsAfterFiniteDerivation name key world error value protocol nameEq keyEq origin unique
                                                                                               ^^^^^^


RESULT {"path": "research-tests/DGamma/R176UnsealedOriginUniqueNegative.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176UnsealedOriginUniqueNegative.idr", "exit": 1, "seconds": 1.0467422008514404, "start": "2026-09-07T02:32:54.556122+00:00", "end": "2026-09-07T02:32:55.602865+00:00", "maxSampleRSSKiB": 0, "fresh": true, "expectedDiagnostic": "Mismatch between: ActionRegistrationReplayCorrespondence", "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176ReductionUniqueDirectionNegative.idr
1/1: Building DGamma.R176ReductionUniqueDirectionNegative (research-tests/DGamma/R176ReductionUniqueDirectionNegative.idr)
Error: While processing right hand side of reductionUniqueCannotRunBackward. Can't solve constraint between: reduction .reducedFinal and originalFinal.

DGamma.R176ReductionUniqueDirectionNegative:25:93--25:106
 21 |   (reduction : ClosingFreeReduction name key world error value protocol nameEq keyEq original) ->
 22 |   (UniqueRawNameInsertions name key world error value nameEq keyEq (reducedTrace reduction)) ->
 23 |   (UniqueRawNameInsertions name key world error value nameEq keyEq (reducedTrace reduction))
 24 | reductionUniqueCannotRunBackward name key world error value protocol nameEq keyEq reduction reducedUnique =
 25 |   uniqueInsertionsAfterReduction name key world error value nameEq keyEq protocol reduction reducedUnique
                                                                                                  ^^^^^^^^^^^^^


RESULT {"path": "research-tests/DGamma/R176ReductionUniqueDirectionNegative.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R176ReductionUniqueDirectionNegative.idr", "exit": 1, "seconds": 1.054274082183838, "start": "2026-09-07T02:32:55.631653+00:00", "end": "2026-09-07T02:32:56.685933+00:00", "maxSampleRSSKiB": 0, "fresh": true, "expectedDiagnostic": "reduction .reducedFinal and originalFinal", "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R6OldPollutionNegative.idr
1/1: Building DGamma.R6OldPollutionNegative (research-tests/DGamma/R6OldPollutionNegative.idr)
Error: While processing right hand side of oldPollutionReachesO20. When unifying:
    CertifiedActorPermutation name (supportOrder (canonicalSchedule leftCapital)) (map (renameBackward (currentNameBijection (endpointRenaming sameInputs))) (supportOrder (canonicalSchedule rightCapital)))
and:
    CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital ?matching
Mismatch between: CertifiedActorPermutation name (supportOrder (canonicalSchedule leftCapital)) (map (renameBackward (currentNameBijection (endpointRenaming sameInputs))) (supportOrder (canonicalSchedule rightCapital))) and CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital ?matching.

DGamma.R6OldPollutionNegative:45:77--45:85
 41 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational)
 42 | oldPollutionReachesO20 {nameEq} {keyEq} {protocol} {leftTrace} {rightTrace}
 43 |   {sameInputs} {leftCapital} {rightCapital} leftUnique rightUnique matching polluted =
 44 |     (polluted ** canonicalSchedulesConvergeSpike nameEq keyEq protocol leftTrace
 45 |       rightTrace sameInputs leftCapital rightCapital leftUnique rightUnique polluted)
                                                                                  ^^^^^^^^


RESULT {"path": "research-tests/DGamma/R6OldPollutionNegative.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R6OldPollutionNegative.idr", "exit": 1, "seconds": 1.062546730041504, "start": "2026-09-07T02:32:56.714535+00:00", "end": "2026-09-07T02:32:57.777083+00:00", "maxSampleRSSKiB": 0, "fresh": true, "expectedDiagnostic": "Mismatch between: CertifiedActorPermutation", "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R6MixedScheduleNegative.idr
1/1: Building DGamma.R6MixedScheduleNegative (research-tests/DGamma/R6MixedScheduleNegative.idr)
Error: While processing right hand side of mixedLeftSchedule. When unifying:
    CanonicalConvergenceResult name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital operational
and:
    CanonicalConvergenceResult name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs otherLeft rightCapital operational
Mismatch between: leftCapital and otherLeft.

DGamma.R6MixedScheduleNegative:37:64--37:75
 33 |     (currentNameBijection (endpointRenaming sameInputs))
 34 | mixedLeftSchedule {nameEq} {keyEq} {protocol} {leftTrace} {rightTrace} {sameInputs}
 35 |   leftCapital otherLeft rightCapital leftUnique rightUnique convergence =
 36 |     originalEndpointsConvergeSpike nameEq keyEq protocol leftTrace rightTrace
 37 |       sameInputs otherLeft rightCapital leftUnique rightUnique convergence
                                                                     ^^^^^^^^^^^


RESULT {"path": "research-tests/DGamma/R6MixedScheduleNegative.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R6MixedScheduleNegative.idr", "exit": 1, "seconds": 1.0338830947875977, "start": "2026-09-07T02:32:57.806806+00:00", "end": "2026-09-07T02:32:58.840696+00:00", "maxSampleRSSKiB": 0, "fresh": true, "expectedDiagnostic": "Mismatch between: leftCapital and otherLeft.", "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R8WrongTraceBridgeNegative.idr
1/1: Building DGamma.R8WrongTraceBridgeNegative (research-tests/DGamma/R8WrongTraceBridgeNegative.idr)
Error: While processing right hand side of wrongTraceBridge. Can't solve constraint between: operational .operationalTargetFinal and otherFinal.

DGamma.R8WrongTraceBridgeNegative:36:60--36:89
 32 |     (canonicalTrace (canonicalSchedule leftCapital)) otherTrace) ->
 33 |   ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
 34 |     leftTrace rightTrace sameInputs leftCapital otherTrace otherOccurrences
 35 |     rightCapital
 36 | wrongTraceBridge convergence otherTrace otherOccurrences = convergenceBridge convergence
                                                                 ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


RESULT {"path": "research-tests/DGamma/R8WrongTraceBridgeNegative.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R8WrongTraceBridgeNegative.idr", "exit": 1, "seconds": 1.061357021331787, "start": "2026-09-07T02:32:58.869642+00:00", "end": "2026-09-07T02:32:59.930999+00:00", "maxSampleRSSKiB": 0, "fresh": true, "expectedDiagnostic": "operationalTargetFinal and otherFinal", "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R8WrongOccurrenceBridgeNegative.idr
1/1: Building DGamma.R8WrongOccurrenceBridgeNegative (research-tests/DGamma/R8WrongOccurrenceBridgeNegative.idr)
Error: While processing right hand side of detachBridgeOccurrenceRelation. When unifying:
    ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital replayed first rightCapital
and:
    ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital replayed second rightCapital
Mismatch between: first and second.

DGamma.R8WrongOccurrenceBridgeNegative:32:54--32:60
 28 |   ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
 29 |     leftTrace rightTrace sameInputs leftCapital replayed first rightCapital ->
 30 |   ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
 31 |     leftTrace rightTrace sameInputs leftCapital replayed second rightCapital
 32 | detachBridgeOccurrenceRelation first second bridge = bridge
                                                           ^^^^^^


RESULT {"path": "research-tests/DGamma/R8WrongOccurrenceBridgeNegative.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R8WrongOccurrenceBridgeNegative.idr", "exit": 1, "seconds": 1.0395269393920898, "start": "2026-09-07T02:32:59.960463+00:00", "end": "2026-09-07T02:33:00.999990+00:00", "maxSampleRSSKiB": 0, "fresh": true, "expectedDiagnostic": "first and second", "passed": true}
START idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R11BridgeWrongGenerationNegative.idr
1/1: Building DGamma.R11BridgeWrongGenerationNegative (research-tests/DGamma/R11BridgeWrongGenerationNegative.idr)
Error: While processing right hand side of arbitraryRightBirthCannotSatisfyBridgeGeneration. Can't solve constraint between: MkRegistrationGeneration (renameForward (currentNameBijection (endpointRenaming sameInputs)) child) (registrationOrdinal (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence rightCapital) rightBirth)) and (generatedGenerationBijection sameInputs) .generationForward (registrationGeneration (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence leftCapital) leftBirth)).

DGamma.R11BridgeWrongGenerationNegative:42:26--42:30
 38 |       (canonicalOccurrenceCorrespondence leftCapital) leftBirth)) =
 39 |   registrationGeneration (replayGeneratedRegistrationOrigin
 40 |     (canonicalOccurrenceCorrespondence rightCapital) rightBirth)
 41 | arbitraryRightBirthCannotSatisfyBridgeGeneration sameInputs leftCapital rightCapital
 42 |   leftBirth rightBirth = Refl
                               ^^^^


RESULT {"path": "research-tests/DGamma/R11BridgeWrongGenerationNegative.idr", "command": "idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R11BridgeWrongGenerationNegative.idr", "exit": 1, "seconds": 1.0406923294067383, "start": "2026-09-07T02:33:01.026089+00:00", "end": "2026-09-07T02:33:02.066784+00:00", "maxSampleRSSKiB": 0, "fresh": true, "expectedDiagnostic": "generatedGenerationBijection sameInputs", "passed": true}
PASS: 12 positive fresh checks; 9 exact diagnostic-negative fresh checks

```

## Other removed charged declarations

The three C11 declarations are fully archived in O6-R176-C11-STOP-AUDIT.md. Below are B6/C4/C8 first-attempt declarations; each was corrected only within its own micro-unit.

### B6-1

```idris
||| Same authenticated raw actor has one protocol rank at arbitrary closings.
||| The two reached states remain distinct; B13 supplies genuine cross-time coherence.
0 rawClosingRanksSameActor :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq global) ->
  (UniqueRawNameInsertions name key world error value nameEq keyEq global) ->
  (leftActor, rightActor : name) ->
  (left : LocatedClosedEpisode name key world error value nameEq keyEq leftActor global) ->
  (right : LocatedClosedEpisode name key world error value nameEq keyEq rightActor global) ->
  (leftActor = rightActor) ->
  (rawClosingOccurrenceRank name key world error value nameEq keyEq protocol global premises
    (ErasedClosingEpisodeOccurrence leftActor left) =
   rawClosingOccurrenceRank name key world error value nameEq keyEq protocol global premises
    (ErasedClosingEpisodeOccurrence rightActor right))
rawClosingRanksSameActor name key world error value nameEq keyEq protocol global premises unique
  leftActor _ left right Refl =
    uniqueRawRanksAcrossPrefixes name key world error value protocol nameEq keyEq global
      (replayAligned premises) (replayInitialEmpty premises) unique
      (prefixThroughOpening left)
      (appendTransitions (closedTransitions (locatedEpisode left)) (traceAfterClosing left))
      (rawClosingReachedCutExact name key world error value nameEq keyEq leftActor left)
      (prefixThroughOpening right)
      (appendTransitions (closedTransitions (locatedEpisode right)) (traceAfterClosing right))
      (rawClosingReachedCutExact name key world error value nameEq keyEq leftActor right)
      leftActor
      (rawClosingOccurrenceRank name key world error value nameEq keyEq protocol global premises
        (ErasedClosingEpisodeOccurrence leftActor left))
      (rawClosingOccurrenceRank name key world error value nameEq keyEq protocol global premises
        (ErasedClosingEpisodeOccurrence leftActor right))
      (rawClosingOccurrenceRankSound name key world error value nameEq keyEq protocol global premises leftActor left)
      (rawClosingOccurrenceRankSound name key world error value nameEq keyEq protocol global premises leftActor right)

```

### C4-1

```idris
||| The new action fold computes EXACTLY the existing R175 whole-trace measure
||| input, not a replacement word or a new per-actor debt.
0 canonicalWorkRankSegmentsFold :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (fixedOrder : List name) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (canonicalWorkRankSegments name key world error value nameEq fixedOrder trace =
    traceActionFold name key world error value (List (List Nat))
      (canonicalWorkRankStep name key world error value nameEq fixedOrder) [[]] trace)
canonicalWorkRankSegmentsFold name key world error value nameEq fixedOrder NoTransitions = Refl
canonicalWorkRankSegmentsFold name key world error value nameEq fixedOrder (MoreTransitions step rest) =
  cong (canonicalWorkRankStep name key world error value nameEq fixedOrder (transitionAction step))
    (canonicalWorkRankSegmentsFold name key world error value nameEq fixedOrder rest)

```

### C8-1

```idris
||| Reinspection measures the SAME actual sealed target under the SAME fixed
||| support order. This is the whole worklist measure, not a selected actor's
||| resettable debt. Strict decrease still needs an operational descending choice.
0 canonicalWorkAcceptedResultInversionMeasure :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq original) ->
  (shape : ClosingFreeTraceShape name key world error value nameEq keyEq original) ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq originalFinal) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq original) ->
  (current : CanonicalSortingWorklist name key world error value protocol nameEq keyEq original ordering) ->
  {pairFirst, pairMiddle, pairFinal : SystemState name key value world error} ->
  (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) -> (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal (sortingCurrentFinal (workReachedReplay current))) ->
  (orientation : AdjacentSwapOrientationEvidence left right) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
    (sortingCurrentTrace (workReachedReplay current)) prefixTrace left right suffix diamond) ->
  (canonicalWorkGlobalInversionMeasure name key world error value protocol nameEq keyEq ordering
    (canonicalWorkAcceptAdjacentResult name key world error value nameEq keyEq protocol
      original premises shape ordering unique current prefixTrace left right suffix orientation diamond result) =
   foldr (+) Z (map rankInversions (traceActionFold name key world error value (List (List Nat))
    (canonicalWorkRankStep name key world error value nameEq (orderedSupportNames ordering))
    (canonicalWorkRankStep name key world error value nameEq (orderedSupportNames ordering) (transitionAction right)
      (canonicalWorkRankStep name key world error value nameEq (orderedSupportNames ordering) (transitionAction left)
        (canonicalWorkRankSegments name key world error value nameEq (orderedSupportNames ordering) suffix))) prefixTrace)))
canonicalWorkAcceptedResultInversionMeasure name key world error value nameEq keyEq protocol
  original premises shape ordering unique current prefixTrace left right suffix orientation diamond result =
    cong (\segments => foldr (+) Z (map rankInversions segments))
      (canonicalWorkAdjacentTargetRankFold name key world error value nameEq keyEq protocol
        (orderedSupportNames ordering) (sortingCurrentTrace (workReachedReplay current))
        prefixTrace left right suffix diamond result)

```
