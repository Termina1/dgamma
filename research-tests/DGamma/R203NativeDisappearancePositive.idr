module DGamma.R203NativeDisappearancePositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5O20NativeDisappearanceSkipSpike
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

||| NONVACUOUS native slot regression: an actual checked Unload consumes one
||| source edge, has zero survivor edges, and has no target slot at ANY Nat.
||| This produces its own filter. It is a coordinate/filter fixture, NOT an
||| assertion of full DeletionResult endpoint recovery for this isolated edge.
export
0 r203ActualUnloadIsNotEpsilon :
  (filtered : GenerationActionSubsequence r45NameEq (EpisodeGenerationDeletedActor r45NameEq 0 []) 7 []
    (MoreTransitions r193HistoricalUnload NoTransitions)
    (the (Transitions r193HistoricalClosed r193HistoricalClosed) NoTransitions) **
    (o20SubsequenceTargetOrdinal filtered Z = Nothing,
     transitionCount (MoreTransitions r193HistoricalUnload NoTransitions) =
       S (transitionCount (the (Transitions r193HistoricalClosed r193HistoricalClosed) NoTransitions)),
     (target : Nat) -> Not (generationSubsequenceSourceOrdinal filtered target = Just Z)))
r203ActualUnloadIsNotEpsilon =
  let 0 filtered : GenerationActionSubsequence r45NameEq (EpisodeGenerationDeletedActor r45NameEq 0 []) 7 []
        (MoreTransitions r193HistoricalUnload NoTransitions)
        (the (Transitions r193HistoricalClosed r193HistoricalClosed) NoTransitions)
      filtered = DeleteGenerationAction r193HistoricalUnload NoTransitions
        (DeleteEpisodeGenerationLifecycle Refl Refl) GenerationActionSubsequenceEnd
      0 absent : (o20SubsequenceTargetOrdinal filtered Z = Nothing)
      absent = o20SelectedLifecycleTargetAbsent Nat R45Key Unit String R45Value r45NameEq 0 []
        filtered Z (LUnload 0) Refl Refl Refl
  in (filtered ** (absent, Refl,
    \target, origin => absurd (trans (sym absent)
      (fst (o20SubsequenceOrdinalsInverse filtered Z target) origin))))
