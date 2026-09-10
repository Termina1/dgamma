module DGamma.R202RetainedClosingIndexPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5O20DeletionRetainedUnloadSpike
import DGamma.CP5O20RetainedClosingIndexSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R178GeneratedOrchestrationFixtures
import DGamma.R193VestigialHistoryTransportPositive
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| The source is the actual eight-edge history, with birth at2 and Unload
||| at7 (suffix index4). The real target subsequence, native exclusion and
||| retained-birth origin remain explicit CONDITIONAL inputs. Neither target
||| Unload nor its order is an input. This is a same-segment join fixture,
||| NOT the universal three-segment deletion-step join.
export
0 r202HistoricalForeignClosingJoin :
  {first, finalState : SystemState Nat R45Key R45Value Unit String} ->
  (survivor : Transitions first finalState) ->
  (kept : GenerationActionSubsequence r45NameEq (EpisodeGenerationDeletedActor r45NameEq 2 []) Z []
    r193HistoricalClosedTrace survivor) ->
  O20RegisteredUnloadFree Nat R45Key Unit String R45Value r45NameEq [] Z [] r193HistoricalClosedTrace ->
  (retained : LocatedGeneratedRegistration 1 0 r45Child survivor) ->
  (generationSubsequenceSourceOrdinal kept (registrationOrdinal retained) = Just 2) ->
  ActionOccurs (LUnload 0) (afterRegistration retained)
r202HistoricalForeignClosingJoin survivor kept free retained birthExact =
  o20ForeignSegmentRetainedClosingBirth Nat R45Key Unit String R45Value r45NameEq 2 [] Z []
    r193HistoricalClosedTrace survivor kept free (MkRegistrationGeneration 1 2)
    (MkDeletedGenerationClassification 0 r45Child r193HistoricalBirth Refl
      (o20IndexedUnloadOccurs Nat R45Key Unit String R45Value r193HistoricalContinuation 4 0 Refl))
    absurd retained birthExact
