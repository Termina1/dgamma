module DGamma.R137O8GenerationIntervalRatification

import DGamma.R137O8RawNameReuseCountershape
import DGamma.R137O8RawNameReuseCountershapeTrace
import DGamma.R137O8RawNameReuseCountershapeProof
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP4DeletionGenerationScan
import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

0 r137OccursAfterPrefix :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, beforeState, afterState, finalState :
    SystemState name key value world error} ->
  {action : Action name key value world error} ->
  (earlier : Transitions first beforeState) ->
  (transition : Transition beforeState afterState) ->
  (suffix : Transitions afterState finalState) ->
  transitionAction transition = action ->
  ActionOccurs action
    (appendTransitions earlier (MoreTransitions transition suffix))
r137OccursAfterPrefix NoTransitions transition suffix shape =
  ActionOccursHere transition suffix shape
r137OccursAfterPrefix (MoreTransitions head rest) transition suffix shape =
  ActionOccursLater head
    (appendTransitions rest (MoreTransitions transition suffix))
    (r137OccursAfterPrefix rest transition suffix shape)

0 r137LocatedActionOccurs :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {action : Action name key value world error} ->
  {global : Transitions first finalState} ->
  LocatedActionOccurrence action global -> ActionOccurs action global
r137LocatedActionOccurs
  (MkLocatedActionOccurrence beforeState afterState before transition after
    actionShape decomposition) =
      replace {p = \trace => ActionOccurs action trace} decomposition
        (r137OccursAfterPrefix before transition after actionShape)


0 r137NoRegisteredEmpty :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (live : GenerationEnvironment name) ->
  (trace : Transitions first finalState) ->
  NoRegisteredEpisode nameEq [] ordinal live trace
r137NoRegisteredEmpty nameEq ordinal live NoTransitions =
  NoRegisteredEpisodeEnd
r137NoRegisteredEmpty nameEq ordinal live
  (MoreTransitions transition rest) =
    NoRegisteredEpisodeStep transition rest
      (\isBegin, (generation ** (current, member)) => case member of {})
      (r137NoRegisteredEmpty nameEq (S ordinal)
        (advanceGenerationEnvironment @{nameEq} ordinal
          (transitionAction transition) live) rest)

0 r137FirstBNoDependentForGeneration :
  (startOrdinal : Nat) -> (startLive : GenerationEnvironment R137Name) ->
  NoDependentClosingEpisodeForGeneration
    {global = r137Trace} ActorB startOrdinal startLive r137LocatedFirstB
r137FirstBNoDependentForGeneration startOrdinal startLive consumer episode
  scoped edge =
    r137NoLocatedBeginInsideFirstB consumer
      (scopedConsumerOpening scoped)

||| Positive ratification: the first ActorB close is now a complete O8
||| candidate.  Its installed interval contains no foreign opening, while the
||| later second-generation ActorB -> ActorA edge is correctly out of scope.
public export
0 r137RevisedO8CandidateExists :
  DeletableClosingEpisode R137Name R137Key Unit Unit R137Value
    r137NameEq r137KeyEq r137Trace
r137RevisedO8CandidateExists =
  case scanGenerations r137NameEq 0 []
    (traceBeforeOpening r137LocatedFirstB) of
    MkGenerationScanResult startOrdinal startLive beforeScan =>
      MkDeletableClosingEpisode ActorB r137LocatedFirstB []
        (\generation, member => case member of {})
        startOrdinal startLive beforeScan
        (r137FirstBRegisteredDuringEmpty startOrdinal)
        (r137FirstBNoDependentForGeneration startOrdinal startLive)
        (r137NoRegisteredEmpty r137NameEq 0 [] r137Trace)

r137FirstAInside : Transitions r137S5 r137S15
r137FirstAInside =
  MoreTransitions r137T5 (MoreTransitions r137T6
  (MoreTransitions r137T7 (MoreTransitions r137T8
  (MoreTransitions r137T9 (MoreTransitions r137T10
  (MoreTransitions r137T11 (MoreTransitions r137T12
  (MoreTransitions r137T13 (MoreTransitions r137T14 NoTransitions)))))))))

0 r137FirstAInstalled : InstalledTrace R137Name R137Key Unit Unit R137Value
  r137NameEq r137KeyEq ActorA r137FirstAInside
r137FirstAInstalled =
  InstalledStep (LAdvance ActorA) LFinishTag r137C5 _ r137InstalledAAt5
  (InstalledStep (OInsert ActorB Root r137ConsumerComponent) OInsertTag r137C6 _
    r137InstalledAAt6
  (InstalledStep (LBegin ActorB) LBeginTag r137C7 _ r137InstalledAAt7
  (InstalledStep (LAdvance ActorB) LRaiseTag r137C8 _ r137InstalledAAt8
  (InstalledStep (LUnload ActorB) LUnloadTag r137C9 _ r137InstalledAAt9
  (InstalledStep (ORetire ActorB) ORetireTag r137C10 _ r137InstalledAAt10
  (InstalledStep (ORemove ActorB) ORemoveTag r137C11 _ r137InstalledAAt11
  (InstalledStep (ORetire Anchor) ORetireTag r137C12 _ r137InstalledAAt12
  (InstalledStep (ORetire ActorA) ORetireTag r137C13 _ r137InstalledAAt13
  (InstalledStep (LLeave ActorA) LLeaveTag r137C14 NoTransitions
    r137InstalledAAt14 (InstalledEnd r137InstalledAAt15))))))))))

r137BeforeFirstA : Transitions r137S0 r137S4
r137BeforeFirstA = MoreTransitions r137T0 (MoreTransitions r137T1
  (MoreTransitions r137T2 (MoreTransitions r137T3 NoTransitions)))

r137AfterFirstA : Transitions r137S16 r137S24
r137AfterFirstA = MoreTransitions r137T16 (MoreTransitions r137T17
  (MoreTransitions r137T18 (MoreTransitions r137T19
  (MoreTransitions r137T20 (MoreTransitions r137T21
  (MoreTransitions r137T22 (MoreTransitions r137T23 NoTransitions)))))))

0 r137FirstAEpisode : ClosedEpisode R137Name R137Key Unit Unit R137Value
  r137NameEq r137KeyEq ActorA r137S4 r137S16
r137FirstAEpisode = MkClosedEpisode r137S5 r137S15
  (MkBeginStep r137C4) r137FirstAInside r137FirstAInstalled
  (MkUnloadStep r137C15)

0 r137LocatedFirstA : LocatedClosedEpisode R137Name R137Key Unit Unit R137Value
  r137NameEq r137KeyEq ActorA r137Trace
r137LocatedFirstA = MkLocatedClosedEpisode r137S4 r137S16 r137BeforeFirstA
  r137FirstAEpisode r137AfterFirstA Refl

r137InsideFirstABeforeB : Transitions r137S5 r137S7
r137InsideFirstABeforeB = MoreTransitions r137T5
  (MoreTransitions r137T6 NoTransitions)

r137InsideFirstAAfterBOpening : Transitions r137S8 r137S15
r137InsideFirstAAfterBOpening =
  MoreTransitions r137T8 (MoreTransitions r137T9
  (MoreTransitions r137T10 (MoreTransitions r137T11
  (MoreTransitions r137T12 (MoreTransitions r137T13
  (MoreTransitions r137T14 NoTransitions))))))

0 r137BOpeningInsideFirstA : LocatedActionOccurrence (LBegin ActorB)
  r137FirstAInside
r137BOpeningInsideFirstA = MkLocatedActionOccurrence r137S7 r137S8
  r137InsideFirstABeforeB r137T7 r137InsideFirstAAfterBOpening
  r137Action7 Refl

r137GenerationA3 : RegistrationGeneration R137Name
r137GenerationA3 = MkRegistrationGeneration ActorA 3

r137LiveAtFirstAOpening : GenerationEnvironment R137Name
r137LiveAtFirstAOpening =
  [(ActorA, r137GenerationA3),
   (Anchor, MkRegistrationGeneration Anchor 0)]

0 r137FirstAScopesFirstB : GenerationScopedClosingStart
  R137Name R137Key Unit Unit R137Value r137NameEq r137KeyEq r137Trace
  ActorA 4 r137LiveAtFirstAOpening r137LocatedFirstA
  ActorB r137LocatedFirstB
r137FirstAScopesFirstB = MkGenerationScopedClosingStart r137GenerationA3
  Refl Refl r137BOpeningInsideFirstA
  (trans r137LocatedFirstBOrdinal Refl)

||| Negative ratification: the repaired predicate still rejects the genuine
||| dependency whose consumer opens while this selected activation is installed.
public export
0 r137RevisedPredicateRejectsInIntervalDependency :
  NoDependentClosingEpisodeForGeneration
    {global = r137Trace} ActorA 4 r137LiveAtFirstAOpening r137LocatedFirstA ->
  Void
r137RevisedPredicateRejectsInIntervalDependency noDependent =
  noDependent ActorB r137LocatedFirstB r137FirstAScopesFirstB
    (replace {p = \state => PrecedenceEdge r137NameEq ActorA ActorB state}
      (sym r137LocatedFirstBStart) r137FirstGenerationEdge)
