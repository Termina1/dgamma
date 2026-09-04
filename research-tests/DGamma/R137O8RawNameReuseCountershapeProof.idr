module DGamma.R137O8RawNameReuseCountershapeProof

import DGamma.R137O8RawNameReuseCountershape
import DGamma.R137O8RawNameReuseCountershapeTrace
import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

r137BeforeFirstB : Transitions r137S0 r137S7
r137BeforeFirstB =
  MoreTransitions r137T0 (MoreTransitions r137T1
  (MoreTransitions r137T2 (MoreTransitions r137T3
  (MoreTransitions r137T4 (MoreTransitions r137T5
  (MoreTransitions r137T6 NoTransitions))))))

r137InsideFirstB : Transitions r137S8 r137S9
r137InsideFirstB = MoreTransitions r137T8 NoTransitions

r137AfterFirstB : Transitions r137S10 r137S24
r137AfterFirstB =
  MoreTransitions r137T10 (MoreTransitions r137T11
  (MoreTransitions r137T12 (MoreTransitions r137T13
  (MoreTransitions r137T14 (MoreTransitions r137T15
  (MoreTransitions r137T16 (MoreTransitions r137T17
  (MoreTransitions r137T18 (MoreTransitions r137T19
  (MoreTransitions r137T20 (MoreTransitions r137T21
  (MoreTransitions r137T22 (MoreTransitions r137T23 NoTransitions)))))))))))))

0 r137FirstBInstalled : InstalledTrace R137Name R137Key Unit Unit R137Value
  r137NameEq r137KeyEq ActorB r137InsideFirstB
r137FirstBInstalled = InstalledStep (LAdvance ActorB) LRaiseTag r137C8
  NoTransitions r137InstalledBAt8 (InstalledEnd r137InstalledBAt9)

0 r137FirstBEpisode : ClosedEpisode R137Name R137Key Unit Unit R137Value
  r137NameEq r137KeyEq ActorB r137S7 r137S10
r137FirstBEpisode = MkClosedEpisode r137S8 r137S9
  (MkBeginStep r137C7) r137InsideFirstB r137FirstBInstalled
  (MkUnloadStep r137C9)

public export
0 r137LocatedFirstB : LocatedClosedEpisode R137Name R137Key Unit Unit R137Value
  r137NameEq r137KeyEq ActorB r137Trace
r137LocatedFirstB = MkLocatedClosedEpisode r137S7 r137S10
  r137BeforeFirstB r137FirstBEpisode r137AfterFirstB Refl


r137BeforeSecondA : Transitions r137S0 r137S21
r137BeforeSecondA =
  MoreTransitions r137T0 (MoreTransitions r137T1
  (MoreTransitions r137T2 (MoreTransitions r137T3
  (MoreTransitions r137T4 (MoreTransitions r137T5
  (MoreTransitions r137T6 (MoreTransitions r137T7
  (MoreTransitions r137T8 (MoreTransitions r137T9
  (MoreTransitions r137T10 (MoreTransitions r137T11
  (MoreTransitions r137T12 (MoreTransitions r137T13
  (MoreTransitions r137T14 (MoreTransitions r137T15
  (MoreTransitions r137T16 (MoreTransitions r137T17
  (MoreTransitions r137T18 (MoreTransitions r137T19
  (MoreTransitions r137T20 NoTransitions))))))))))))))))))))

r137InsideSecondA : Transitions r137S22 r137S23
r137InsideSecondA = MoreTransitions r137T22 NoTransitions

0 r137SecondAInstalled : InstalledTrace R137Name R137Key Unit Unit R137Value
  r137NameEq r137KeyEq ActorA r137InsideSecondA
r137SecondAInstalled = InstalledStep (LAdvance ActorA) LRaiseTag r137C22
  NoTransitions r137InstalledAAt22 (InstalledEnd r137InstalledAAt23)

0 r137SecondAEpisode : ClosedEpisode R137Name R137Key Unit Unit R137Value
  r137NameEq r137KeyEq ActorA r137S21 r137S24
r137SecondAEpisode = MkClosedEpisode r137S22 r137S23
  (MkBeginStep r137C21) r137InsideSecondA r137SecondAInstalled
  (MkUnloadStep r137C23)

public export
0 r137LocatedSecondA : LocatedClosedEpisode R137Name R137Key Unit Unit R137Value
  r137NameEq r137KeyEq ActorA r137Trace
r137LocatedSecondA = MkLocatedClosedEpisode r137S21 r137S24
  r137BeforeSecondA r137SecondAEpisode NoTransitions Refl



||| The first ActorA generation supports ActorB's closing episode.  Therefore
||| the raw-name predicate rejects ActorA even though that generation is removed
||| before ActorA is born again as a consumer.
public export
0 r137RawActorANotDeletionMaximal :
  NoDependentClosingEpisode {nameEq = r137NameEq} {keyEq = r137KeyEq}
    ActorA r137Trace -> Void
r137RawActorANotDeletionMaximal noDependent =
  noDependent ActorB r137LocatedFirstB r137FirstGenerationEdge

||| The second ActorB generation supports ActorA's later closing episode.
||| Therefore the same raw-name predicate also rejects ActorB because of a
||| different birth of each endpoint.
public export
0 r137RawActorBNotDeletionMaximal :
  NoDependentClosingEpisode {nameEq = r137NameEq} {keyEq = r137KeyEq}
    ActorB r137Trace -> Void
r137RawActorBNotDeletionMaximal noDependent =
  noDependent ActorA r137LocatedSecondA r137SecondGenerationEdge

public export
0 r137LocatedFirstBInside :
  closedInside (locatedEpisode r137LocatedFirstB) =
    MoreTransitions r137T8 NoTransitions
r137LocatedFirstBInside = Refl

public export
0 r137LocatedFirstBStart :
  closedStartState (locatedEpisode r137LocatedFirstB) = r137S8
r137LocatedFirstBStart = Refl

public export
0 r137LocatedFirstBOrdinal :
  transitionCount (traceBeforeOpening r137LocatedFirstB) = 7
r137LocatedFirstBOrdinal = Refl

0 r137ProofOccursAfterPrefix :
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
r137ProofOccursAfterPrefix NoTransitions transition suffix shape =
  ActionOccursHere transition suffix shape
r137ProofOccursAfterPrefix (MoreTransitions head rest) transition suffix shape =
  ActionOccursLater head
    (appendTransitions rest (MoreTransitions transition suffix))
    (r137ProofOccursAfterPrefix rest transition suffix shape)

0 r137ProofLocatedActionOccurs :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {action : Action name key value world error} ->
  {global : Transitions first finalState} ->
  LocatedActionOccurrence action global -> ActionOccurs action global
r137ProofLocatedActionOccurs
  (MkLocatedActionOccurrence beforeState afterState before transition after
    actionShape decomposition) =
      replace {p = \trace => ActionOccurs action trace} decomposition
        (r137ProofOccursAfterPrefix before transition after actionShape)

0 r137NoBeginInFirstBInsideExact :
  (consumer : R137Name) ->
  ActionOccurs (LBegin consumer) r137InsideFirstB -> Void
r137NoBeginInFirstBInsideExact consumer
  (ActionOccursHere _ _ shape) =
    case trans (sym r137Action8) shape of Refl impossible
r137NoBeginInFirstBInsideExact consumer
  (ActionOccursLater _ _ later) = case later of
    ActionOccursHere transition rest shape impossible
    ActionOccursLater transition rest deeper impossible

public export
0 r137NoLocatedBeginInsideFirstB :
  (consumer : R137Name) ->
  LocatedActionOccurrence (LBegin consumer)
    (closedInside (locatedEpisode r137LocatedFirstB)) -> Void
r137NoLocatedBeginInsideFirstB consumer occurrence =
  r137NoBeginInFirstBInsideExact consumer
    (r137ProofLocatedActionOccurs occurrence)

r137FirstBCenter : Transitions r137S7 r137S10
r137FirstBCenter = MoreTransitions r137T7
  (MoreTransitions r137T8 (MoreTransitions r137T9 NoTransitions))

0 r137NoInsertInFirstBCenterExact :
  (child : R137Name) -> (parent : Parent R137Name) ->
  (component : Component R137Key R137Value Unit Unit) ->
  ActionOccurs (OInsert child parent component) r137FirstBCenter -> Void
r137NoInsertInFirstBCenterExact child parent component
  (ActionOccursHere _ _ shape) =
    case trans (sym r137Action7) shape of Refl impossible
r137NoInsertInFirstBCenterExact child parent component
  (ActionOccursLater _ _ (ActionOccursHere _ _ shape)) =
    case trans (sym r137Action8) shape of Refl impossible
r137NoInsertInFirstBCenterExact child parent component
  (ActionOccursLater _ _
    (ActionOccursLater _ _ (ActionOccursHere _ _ shape))) =
      case trans (sym r137Action9) shape of Refl impossible
r137NoInsertInFirstBCenterExact child parent component
  (ActionOccursLater _ _
    (ActionOccursLater _ _ (ActionOccursLater _ _ later))) = case later of
      ActionOccursHere transition rest shape impossible
      ActionOccursLater transition rest deeper impossible

public export
0 r137FirstBRegisteredDuringEmpty : (startOrdinal : Nat) ->
  RegisteredGenerationsDuring ActorB startOrdinal []
    (MoreTransitions
      (beginTransition (closedOpening (locatedEpisode r137LocatedFirstB)))
      (closedTransitions (locatedEpisode r137LocatedFirstB)))
r137FirstBRegisteredDuringEmpty startOrdinal =
  ( (\generation, member => case member of {}),
    (\child, component, birth =>
      void (r137NoInsertInFirstBCenterExact child (ChildOf ActorB) component
        (r137ProofLocatedActionOccurs birth))) )
