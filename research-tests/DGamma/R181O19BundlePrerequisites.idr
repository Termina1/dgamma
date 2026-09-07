module DGamma.R181O19BundlePrerequisites

import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP3Support
import DGamma.CP4Support
import DGamma.CP4SupportQuiescence
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorEndpoint
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ObservedInstalledLifecycleSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.Metatheory
import DGamma.Section3Example
import DGamma.R179O19ObservedExecution
import DGamma.R180O19ObservedCompletion
import DGamma.R181O19SafetyCompletion
import DGamma.R181O19LocatedBlocks
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| F1: authoritative block selector, computed from the actor VALUE rather
||| than comparing erased Elem certificates. Both returned blocks are E's
||| fully constructed occurrences in the actual same whole trace.
public export
0 r181BlocksByActor : (actor : Nat) -> Elem actor [0, 1] ->
  LocatedOpenEpisodeBlock Nat ToyKey ToyRuntime String ToyValue
    (the (DecEq Nat) %search) (the (DecEq ToyKey) %search) actor r181WholeTrace
r181BlocksByActor Z member = r181ProviderLocatedBlock
r181BlocksByActor (S Z) member = r181ConsumerLocatedBlock
r181BlocksByActor (S (S later)) member = case member of
  Here impossible
  There Here impossible
  There (There absent) => case absent of Here impossible; There tail impossible

||| F2: all strict-order witnesses in [0,1] select the actual E7 ordering.
||| Impossible tails are eliminated structurally, not by an assumed ordering.
public export
0 r181BlocksFollowOrder : (earlier, later : Nat) ->
  (earlierMember : Elem earlier [0, 1]) -> (laterMember : Elem later [0, 1]) ->
  BeforeIn earlier later [0, 1] ->
  BlockBefore Nat ToyKey ToyRuntime String ToyValue
    (the (DecEq Nat) %search) (the (DecEq ToyKey) %search) r181WholeTrace earlier later
    (r181BlocksByActor earlier earlierMember) (r181BlocksByActor later laterMember)
r181BlocksFollowOrder _ _ earlierMember laterMember (BeforeHere following) =
  case following of
    Here => r181ProviderBeforeConsumer
    There absent => case absent of Here impossible; There rest impossible
r181BlocksFollowOrder _ _ earlierMember laterMember (BeforeThere following) =
  case following of
    BeforeHere absent => case absent of Here impossible; There rest impossible
    BeforeThere absent =>
      case absent of BeforeHere member impossible; BeforeThere rest impossible

||| F3: exact 3x2 half-open block ranges: left global positions2/3/4,
||| right positions5/6. Consume the ACTUAL selected block fields structurally;
||| no scalar observation of an opaque certified execution builder is assumed.
public export
0 r181BlockRangesApart : (earlier, later : Nat) ->
  (earlierMember : Elem earlier [0, 1]) -> (laterMember : Elem later [0, 1]) ->
  BeforeIn earlier later [0, 1] ->
  (earlierPosition, laterPosition : Nat) ->
  LTE (S earlierPosition)
    (S (transitionCount (blockBody (r181BlocksByActor earlier earlierMember)))) ->
  LTE (S laterPosition)
    (S (transitionCount (blockBody (r181BlocksByActor later laterMember)))) ->
  Not (transitionCount (traceBeforeBlock (r181BlocksByActor earlier earlierMember)) +
      earlierPosition =
    transitionCount (traceBeforeBlock (r181BlocksByActor later laterMember)) + laterPosition)
r181BlockRangesApart _ _ earlierMember laterMember (BeforeHere following)
  Z laterPosition earlierBound laterBound same = case following of
    Here => case same of Refl impossible
    There absent => case absent of Here impossible; There rest impossible
r181BlockRangesApart _ _ earlierMember laterMember (BeforeHere following)
  (S Z) laterPosition earlierBound laterBound same = case following of
    Here => case same of Refl impossible
    There absent => case absent of Here impossible; There rest impossible
r181BlockRangesApart _ _ earlierMember laterMember (BeforeHere following)
  (S (S Z)) laterPosition earlierBound laterBound same = case following of
    Here => case same of Refl impossible
    There absent => case absent of Here impossible; There rest impossible
r181BlockRangesApart _ _ earlierMember laterMember (BeforeHere following)
  (S (S (S tailPosition))) laterPosition earlierBound laterBound same =
    case earlierBound of
      LTESucc (LTESucc (LTESucc impossibleBound)) =>
        case impossibleBound of LTEZero impossible; LTESucc rest impossible
r181BlockRangesApart _ _ earlierMember laterMember (BeforeThere following)
  earlierPosition laterPosition earlierBound laterBound same = case following of
    BeforeHere absent => case absent of Here impossible; There rest impossible
    BeforeThere absent =>
      case absent of BeforeHere member impossible; BeforeThere rest impossible

||| F4: complete authoritative decomposition, not merely two located blocks.
||| The SAME selector owns order, disjoint coordinate ranges and all coverage.
public export
0 r181ActorBlockDecomposition : ActorBlockDecomposition Nat ToyKey ToyRuntime String
  ToyValue (the (DecEq Nat) %search) (the (DecEq ToyKey) %search) [0, 1] r181WholeTrace
r181ActorBlockDecomposition = MkActorBlockDecomposition r181BlocksByActor
  r181BlocksFollowOrder r181BlockRangesApart r181BlockLifecycleCoverage
