module DGamma.CP5O20SafeBlockSelectionSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Exact finite-list location of the two neighboring actors, including the
||| source BeforeIn witness. This does not infer whole-trace block adjacency.
export
0 o20AdjacentListFacts :
  {name : Type} -> (earlier : List name) -> (left, right : name) -> (later : List name) ->
  (Elem left (earlier ++ (left :: right :: later)),
   Elem right (earlier ++ (left :: right :: later)),
   BeforeIn left right (earlier ++ (left :: right :: later)))
o20AdjacentListFacts [] left right later = (Here, There Here, BeforeHere Here)
o20AdjacentListFacts (head :: rest) left right later =
  (There (Builtin.fst (o20AdjacentListFacts rest left right later)),
   There (Builtin.fst (Builtin.snd (o20AdjacentListFacts rest left right later))),
   BeforeThere (Builtin.snd (Builtin.snd (o20AdjacentListFacts rest left right later))))

||| Reindex B1 by the exact source-word equation owned by a chosen pure swap.
||| Only list facts are produced here; B6/B8 check the actual block gap/cut.
export
0 o20ChosenActorFacts :
  {name : Type} -> {sourceOrder, targetOrder : List name} ->
  (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  (Elem (actorLeft swap) sourceOrder, Elem (actorRight swap) sourceOrder,
   BeforeIn (actorLeft swap) (actorRight swap) sourceOrder)
o20ChosenActorFacts {sourceOrder} swap =
  replace {p = \order => (Elem (actorLeft swap) order, Elem (actorRight swap) order,
    BeforeIn (actorLeft swap) (actorRight swap) order)} (sym (actorBeforeExact swap))
      (o20AdjacentListFacts (actorPrefix swap) (actorLeft swap) (actorRight swap) (actorSuffix swap))

||| Executable single-action observation; root insertions are not children.
||| Public computation is required by the next certified negative checker.
public export
o20GeneratedChildName :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  Action name key value world error -> Maybe name
o20GeneratedChildName (OInsert child (ChildOf parent) component) = Just child
o20GeneratedChildName _ = Nothing

||| Certify a negative child observation without deciding component equality.
||| The finite name check is sufficient: an alleged generated insertion must
||| project to the forbidden name under B3.
export
0 o20CheckNoGeneratedAction :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (forbidden : name) ->
  (action : Action name key value world error) ->
  Maybe ((parent : name) -> (component : Component key value world error) ->
    (action = OInsert forbidden (ChildOf parent) component) -> Void)
o20CheckNoGeneratedAction nameEq forbidden action =
  case decEq (o20GeneratedChildName action) (Just forbidden) of
    Yes same => Nothing
    No different => Just (\parent, component, sameAction =>
      different (cong o20GeneratedChildName sameAction))

||| Produce the whole NoGeneratedChild certificate by traversing the ACTUAL
||| block body. A failure is not a canonicality/completeness claim.
export
0 o20CheckNoGeneratedChild :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (forbidden : name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> Maybe (NoGeneratedChild forbidden trace)
o20CheckNoGeneratedChild nameEq forbidden NoTransitions = Just NoGeneratedChildEnd
o20CheckNoGeneratedChild nameEq forbidden (MoreTransitions step rest) =
  (NoGeneratedChildStep step rest) <$>
    (o20CheckNoGeneratedAction nameEq forbidden (transitionAction step)) <*>
    (o20CheckNoGeneratedChild nameEq forbidden rest)

||| Select ONLY the zero constructor of the actual between-block trace.
||| This rejects intervening roots rather than pretending actor adjacency is
||| block adjacency. Refl observes the empty spine, not a replay builder.
export
0 o20CheckEmptyGap :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (gap : Transitions first finalState) -> Maybe (transitionCount gap = 0)
o20CheckEmptyGap NoTransitions = Just Refl
o20CheckEmptyGap (MoreTransitions step rest) = Nothing

||| R179's authenticated evaluator is run at the ACTUAL selected left block's
||| pre-opening cut, not traceDescentBefore of an unrelated adjacent-node pair.
||| Thus the cut-alignment obligation is satisfied by the producer's index.
export
0 o20CheckRightAtLeftOpening :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (left, right : name) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq left trace) ->
  Maybe (CheckedEarlyApplication name key world error value nameEq keyEq
    (blockPreStart block) (LBegin right) LBeginTag)
o20CheckRightAtLeftOpening {name} {key} {world} {error} {value}
  nameEq keyEq left right trace block =
    checkedEarlyApplicationObserved name key world error value nameEq keyEq
      (blockPreStart block) (LBegin right) LBeginTag
      (checkedApplyAction @{nameEq} @{keyEq} (LBegin right) (blockPreStart block)) Refl

||| Positive WHOLE-BLOCK safety producer at explicit list locations. It derives
||| both child exclusions, actual empty gap and exact pre-left-cut Begin guard.
||| No desired diamond, replay, target trace or safety clause is an input.
export
0 o20CheckSafetyAtMembers :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} ->
  (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) ->
  (leftIn : Elem (actorLeft swap) sourceOrder) ->
  (rightIn : Elem (actorRight swap) sourceOrder) ->
  BeforeIn (actorLeft swap) (actorRight swap) sourceOrder ->
  Maybe (AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap trace blocks premises)
o20CheckSafetyAtMembers nameEq keyEq protocol swap trace blocks premises leftIn rightIn ordered =
  (\leftSafe, rightSafe, early, adjacent => MkAdjacentActorSwapSafety leftIn rightIn ordered
    (decomposedBlocksFollowOrder blocks (actorLeft swap) (actorRight swap) leftIn rightIn ordered)
    leftSafe rightSafe early adjacent) <$>
  (o20CheckNoGeneratedChild nameEq (actorRight swap)
    (blockBody (decomposedBlock blocks (actorLeft swap) leftIn))) <*>
  (o20CheckNoGeneratedChild nameEq (actorLeft swap)
    (blockBody (decomposedBlock blocks (actorRight swap) rightIn))) <*>
  (o20CheckRightAtLeftOpening nameEq keyEq (actorLeft swap) (actorRight swap) trace
    (decomposedBlock blocks (actorLeft swap) leftIn)) <*>
  (o20CheckEmptyGap (betweenBlocks
    (decomposedBlocksFollowOrder blocks (actorLeft swap) (actorRight swap) leftIn rightIn ordered)))

||| A selected candidate owns its target actor word, pure transposition,
||| complete positive safety and ORIGINAL source insertion uniqueness. It is
||| NOT an operational permutation: no O19 replay is fabricated or assumed.
public export
record O20ChosenSafeSwap
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key) (sourceOrder : List name)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState)
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace)
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) where
  constructor MkO20ChosenSafeSwap
  chosenTargetOrder : List name
  chosenOrderSwap : AdjacentActorOrderSwap name sourceOrder chosenTargetOrder
  chosenSafety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq
    chosenOrderSwap trace blocks premises
  0 chosenSourceUnique : UniqueRawNameInsertions name key world error value nameEq keyEq trace

||| Explicit candidate elimination followed by actual certification; only the
||| original input uniqueness is retained, never reconstructed for a substitute.
export
0 o20CheckCandidate :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) -> (sourceOrder : List name) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) ->
  (0 unique : UniqueRawNameInsertions name key world error value nameEq keyEq trace) ->
  (candidate : (targetOrder : List name ** AdjacentActorOrderSwap name sourceOrder targetOrder)) ->
  Maybe (O20ChosenSafeSwap name key world error value protocol nameEq keyEq sourceOrder trace blocks premises)
o20CheckCandidate nameEq keyEq protocol sourceOrder trace blocks premises unique (targetOrder ** swap) =
  map (\safety => MkO20ChosenSafeSwap targetOrder swap safety unique)
    (o20CheckSafetyAtMembers nameEq keyEq protocol swap trace blocks premises
      (Builtin.fst (o20ChosenActorFacts swap))
      (Builtin.fst (Builtin.snd (o20ChosenActorFacts swap)))
      (Builtin.snd (Builtin.snd (o20ChosenActorFacts swap))))

||| Enumerate every distinct NEIGHBORING actor pair, preserving the exact
||| source word at each structural cut. This enumerates possible safe swaps,
||| not yet inversions of a fixed accepted support/ancestor extension.
export
0 o20AdjacentCandidates :
  {name : Type} -> (nameEq : DecEq name) ->
  (sourceOrder, earlier, later : List name) -> (sourceOrder = earlier ++ later) ->
  List (targetOrder : List name ** AdjacentActorOrderSwap name sourceOrder targetOrder)
o20AdjacentCandidates nameEq sourceOrder earlier [] exact = []
o20AdjacentCandidates nameEq sourceOrder earlier [last] exact = []
o20AdjacentCandidates nameEq sourceOrder earlier (left :: right :: rest) exact =
  case decEq @{nameEq} left right of
    Yes same => o20AdjacentCandidates nameEq sourceOrder (earlier ++ [left]) (right :: rest)
      (trans exact (appendAssociative earlier [left] (right :: rest)))
    No distinct =>
      (earlier ++ (right :: left :: rest) **
        MkAdjacentActorOrderSwap earlier left right rest exact Refl distinct) ::
      o20AdjacentCandidates nameEq sourceOrder (earlier ++ [left]) (right :: rest)
        (trans exact (appendAssociative earlier [left] (right :: rest)))

||| Finite whole-block POSITIVE selector: unlike R179's first-node probe, a
||| rejected candidate does not prevent checking later pairs. Every returned
||| pair carries BOTH revised clauses, both child exclusions and sourceUnique.
||| Nothing is not a theorem of canonicality; target-extension orientation,
||| operational replay/reselection and strict descent remain unproved.
export
0 o20SelectSafeAdjacentBlocks :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) -> (sourceOrder : List name) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) ->
  (0 unique : UniqueRawNameInsertions name key world error value nameEq keyEq trace) ->
  Maybe (O20ChosenSafeSwap name key world error value protocol nameEq keyEq sourceOrder trace blocks premises)
o20SelectSafeAdjacentBlocks nameEq keyEq protocol sourceOrder trace blocks premises unique =
  head' (mapMaybe (o20CheckCandidate nameEq keyEq protocol sourceOrder trace blocks premises unique)
    (o20AdjacentCandidates nameEq sourceOrder [] sourceOrder Refl))

||| Completeness of the ACTUAL empty-gap checker. The physical zero-gap
||| premise is explicit here and must still be derived at an accepted pair.
export
0 o20CheckEmptyGapComplete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (gap : Transitions first finalState) -> transitionCount gap = 0 ->
  isJust (o20CheckEmptyGap gap) = True
o20CheckEmptyGapComplete NoTransitions empty = Refl
o20CheckEmptyGapComplete (MoreTransitions step rest) Refl impossible

||| Generated-child exclusion implies a negative finite name observation;
||| no component equality decision or metadata replacement is needed.
export
0 o20NoGeneratedObservation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (forbidden : name) -> (action : Action name key value world error) ->
  ((parent : name) -> (component : Component key value world error) ->
    action = OInsert forbidden (ChildOf parent) component -> Void) ->
  Not (o20GeneratedChildName action = Just forbidden)
o20NoGeneratedObservation forbidden (OInsert forbidden (ChildOf parent) component) notChild Refl = notChild parent component Refl
o20NoGeneratedObservation forbidden (OInsert selected Root component) notChild Refl impossible
o20NoGeneratedObservation forbidden (ORetire selected) notChild Refl impossible
o20NoGeneratedObservation forbidden (ORemove selected) notChild Refl impossible
o20NoGeneratedObservation forbidden (LBegin selected) notChild Refl impossible
o20NoGeneratedObservation forbidden (LAdvance selected) notChild Refl impossible
o20NoGeneratedObservation forbidden (LDivert selected) notChild Refl impossible
o20NoGeneratedObservation forbidden (LLeave selected) notChild Refl impossible
o20NoGeneratedObservation forbidden (LUnload selected) notChild Refl impossible

||| Scalar observed-result elimination for the actual finite action checker;
||| this does not observe a nested replay or existential producer.
export
0 o20CheckNoGeneratedActionCompleteObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (forbidden : name) -> (action : Action name key value world error) ->
  (observed : Dec (o20GeneratedChildName action = Just forbidden)) ->
  (0 checked : decEq (o20GeneratedChildName action) (Just forbidden) = observed) ->
  Not (o20GeneratedChildName action = Just forbidden) ->
  isJust (o20CheckNoGeneratedAction nameEq forbidden action) = True
o20CheckNoGeneratedActionCompleteObserved nameEq forbidden action (Yes same) checked negative = absurd (negative same)
o20CheckNoGeneratedActionCompleteObserved nameEq forbidden action (No different) checked negative = rewrite checked in Refl

||| Complete the actual name-only child-action checker from its logical
||| exclusion clause. Both the observation and scalar authentication are owned.
export
0 o20CheckNoGeneratedActionComplete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (forbidden : name) -> (action : Action name key value world error) ->
  ((parent : name) -> (component : Component key value world error) ->
    action = OInsert forbidden (ChildOf parent) component -> Void) ->
  isJust (o20CheckNoGeneratedAction nameEq forbidden action) = True
o20CheckNoGeneratedActionComplete nameEq forbidden action notChild =
  o20CheckNoGeneratedActionCompleteObserved nameEq forbidden action
    (decEq (o20GeneratedChildName action) (Just forbidden)) Refl
    (o20NoGeneratedObservation forbidden action notChild)

||| Two finite positive observations compose through the SAME applicative
||| expression used by the recursive actual trace checker.
export
0 o20MapApplyPresent :
  {a, b, c : Type} -> (combine : a -> b -> c) -> (left : Maybe a) -> (right : Maybe b) ->
  isJust left = True -> isJust right = True -> isJust (combine <$> left <*> right) = True
o20MapApplyPresent combine Nothing right Refl rightPresent impossible
o20MapApplyPresent combine (Just left) Nothing leftPresent Refl impossible
o20MapApplyPresent combine (Just left) (Just right) leftPresent rightPresent = Refl

||| Structural completeness of the ACTUAL whole-trace child checker. This
||| proves the check cannot reject an established NoGeneratedChild clause;
||| obtaining both clauses at an accepted inversion is a separate obligation.
export
0 o20CheckNoGeneratedChildComplete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (forbidden : name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> NoGeneratedChild forbidden trace ->
  isJust (o20CheckNoGeneratedChild nameEq forbidden trace) = True
o20CheckNoGeneratedChildComplete nameEq forbidden NoTransitions NoGeneratedChildEnd = Refl
o20CheckNoGeneratedChildComplete nameEq forbidden (MoreTransitions step rest)
  (NoGeneratedChildStep step rest notChild notRest) =
    o20MapApplyPresent (NoGeneratedChildStep step rest)
      (o20CheckNoGeneratedAction nameEq forbidden (transitionAction step))
      (o20CheckNoGeneratedChild nameEq forbidden rest)
      (o20CheckNoGeneratedActionComplete nameEq forbidden (transitionAction step) notChild)
      (o20CheckNoGeneratedChildComplete nameEq forbidden rest notRest)

||| Completeness of the actual selected pre-left-cut Begin checker. This
||| checks the same action, tag and cut as the physical early certificate.
export
0 o20CheckRightAtLeftOpeningComplete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (left, right : name) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq left trace) ->
  CheckedEarlyApplication name key world error value nameEq keyEq (blockPreStart block) (LBegin right) LBeginTag ->
  isJust (o20CheckRightAtLeftOpening nameEq keyEq left right trace block) = True
o20CheckRightAtLeftOpeningComplete nameEq keyEq left right trace block early =
  rewrite earlyApplicationChecked early in Refl

||| The four actual safety observations compose without changing which
||| candidate, block cuts or logical certificates the checker selected.
export
0 o20FourChecksPresent :
  {a, b, c, d, result : Type} -> (combine : a -> b -> c -> d -> result) ->
  (first : Maybe a) -> (second : Maybe b) -> (third : Maybe c) -> (fourth : Maybe d) ->
  isJust first = True -> isJust second = True -> isJust third = True -> isJust fourth = True ->
  isJust (combine <$> first <*> second <*> third <*> fourth) = True
o20FourChecksPresent combine Nothing second third fourth Refl secondYes thirdYes fourthYes impossible
o20FourChecksPresent combine (Just first) Nothing third fourth firstYes Refl thirdYes fourthYes impossible
o20FourChecksPresent combine (Just first) (Just second) Nothing fourth firstYes secondYes Refl fourthYes impossible
o20FourChecksPresent combine (Just first) (Just second) (Just third) Nothing firstYes secondYes thirdYes Refl impossible
o20FourChecksPresent combine (Just first) (Just second) (Just third) (Just fourth) firstYes secondYes thirdYes fourthYes = Refl

||| COMPLETE actual safety check at its precise member-selected cuts. All
||| four logical clauses refer to the checker's OWN decomposed blocks/gap;
||| no proof irrelevance identifies them with a separately guessed split.
export
0 o20CheckSafetyAtMembersComplete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, finalState : SystemState name key value world error} -> (trace : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) ->
  (leftIn : Elem (actorLeft swap) sourceOrder) -> (rightIn : Elem (actorRight swap) sourceOrder) ->
  (ordered : BeforeIn (actorLeft swap) (actorRight swap) sourceOrder) ->
  NoGeneratedChild (actorRight swap) (blockBody (decomposedBlock blocks (actorLeft swap) leftIn)) ->
  NoGeneratedChild (actorLeft swap) (blockBody (decomposedBlock blocks (actorRight swap) rightIn)) ->
  CheckedEarlyApplication name key world error value nameEq keyEq
    (blockPreStart (decomposedBlock blocks (actorLeft swap) leftIn)) (LBegin (actorRight swap)) LBeginTag ->
  (transitionCount (betweenBlocks (decomposedBlocksFollowOrder blocks (actorLeft swap) (actorRight swap) leftIn rightIn ordered)) = 0) ->
  isJust (o20CheckSafetyAtMembers nameEq keyEq protocol swap trace blocks premises leftIn rightIn ordered) = True
o20CheckSafetyAtMembersComplete nameEq keyEq protocol swap trace blocks premises leftIn rightIn ordered leftSafe rightSafe early adjacent =
  o20FourChecksPresent
    (\leftSafe, rightSafe, early, adjacent => MkAdjacentActorSwapSafety leftIn rightIn ordered
      (decomposedBlocksFollowOrder blocks (actorLeft swap) (actorRight swap) leftIn rightIn ordered) leftSafe rightSafe early adjacent)
    (o20CheckNoGeneratedChild nameEq (actorRight swap) (blockBody (decomposedBlock blocks (actorLeft swap) leftIn)))
    (o20CheckNoGeneratedChild nameEq (actorLeft swap) (blockBody (decomposedBlock blocks (actorRight swap) rightIn)))
    (o20CheckRightAtLeftOpening nameEq keyEq (actorLeft swap) (actorRight swap) trace (decomposedBlock blocks (actorLeft swap) leftIn))
    (o20CheckEmptyGap (betweenBlocks (decomposedBlocksFollowOrder blocks (actorLeft swap) (actorRight swap) leftIn rightIn ordered)))
    (o20CheckNoGeneratedChildComplete nameEq (actorRight swap) (blockBody (decomposedBlock blocks (actorLeft swap) leftIn)) leftSafe)
    (o20CheckNoGeneratedChildComplete nameEq (actorLeft swap) (blockBody (decomposedBlock blocks (actorRight swap) rightIn)) rightSafe)
    (o20CheckRightAtLeftOpeningComplete nameEq keyEq (actorLeft swap) (actorRight swap) trace (decomposedBlock blocks (actorLeft swap) leftIn) early)
    (o20CheckEmptyGapComplete (betweenBlocks (decomposedBlocksFollowOrder blocks (actorLeft swap) (actorRight swap) leftIn rightIn ordered)) adjacent)

||| Scalar case elimination for exhaustive finite filtering. A failed head
||| preserves a later positive; a successful head already makes selection total.
export
0 o20HeadMapMaybeObserved :
  {a, b : Type} -> (check : a -> Maybe b) -> (head : a) -> (rest : List a) ->
  (observed : Maybe b) -> (0 checked : check head = observed) ->
  Either (isJust observed = True) (isJust (head' (mapMaybe check rest)) = True) ->
  isJust (head' (mapMaybe check (head :: rest))) = True
o20HeadMapMaybeObserved check head rest Nothing checked (Left Refl) impossible
o20HeadMapMaybeObserved check head rest Nothing checked (Right laterPresent) = rewrite checked in laterPresent
o20HeadMapMaybeObserved check head rest (Just selected) checked positive = rewrite checked in Refl

||| Exhaustive finite selection cannot return Nothing when ANY enumerated
||| candidate actually succeeds. Structural induction follows its membership;
||| earlier rejections never terminate the search prematurely.
export
0 o20MapMaybeSelectionComplete :
  {a, b : Type} -> (check : a -> Maybe b) -> (candidates : List a) -> (selected : a) ->
  Elem selected candidates -> isJust (check selected) = True ->
  isJust (head' (mapMaybe check candidates)) = True
o20MapMaybeSelectionComplete check [] selected found selectedPresent impossible
o20MapMaybeSelectionComplete check (head :: rest) head Here selectedPresent =
  o20HeadMapMaybeObserved check head rest (check head) Refl (Left selectedPresent)
o20MapMaybeSelectionComplete check (head :: rest) selected (There later) selectedPresent =
  o20HeadMapMaybeObserved check head rest (check head) Refl
    (Right (o20MapMaybeSelectionComplete check rest selected later selectedPresent))

||| Exact constructor equation owned by the native candidate producer. This
||| exposes its SAME swap/safety packet to completeness consumers without
||| changing visibility or equating independently computed observations.
export
0 o20CandidateOwnedEquation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) -> (sourceOrder : List name) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq trace) ->
  (targetOrder : List name) -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  (o20CheckCandidate nameEq keyEq protocol sourceOrder trace blocks premises unique (targetOrder ** swap) =
   map (\safety => MkO20ChosenSafeSwap targetOrder swap safety unique)
    (o20CheckSafetyAtMembers nameEq keyEq protocol swap trace blocks premises
      (Builtin.fst (o20ChosenActorFacts swap))
      (Builtin.fst (Builtin.snd (o20ChosenActorFacts swap)))
      (Builtin.snd (Builtin.snd (o20ChosenActorFacts swap)))))
o20CandidateOwnedEquation nameEq keyEq protocol sourceOrder trace blocks premises unique targetOrder swap = Refl

||| A REAL enumerated candidate, retaining its own swap and membership rather
||| than equating it to a separately constructed proof-carrying swap record.
public export
record O20EnumeratedPair
  (name : Type) (sourceOrder : List name)
  (candidates : List (targetOrder : List name ** AdjacentActorOrderSwap name sourceOrder targetOrder))
  (left, right : name) where
  constructor MkO20EnumeratedPair
  enumeratedTarget : List name
  enumeratedSwap : AdjacentActorOrderSwap name sourceOrder enumeratedTarget
  0 enumeratedMember : Elem (enumeratedTarget ** enumeratedSwap) candidates
  0 enumeratedLeftExact : (actorLeft enumeratedSwap = left)
  0 enumeratedRightExact : (actorRight enumeratedSwap = right)
