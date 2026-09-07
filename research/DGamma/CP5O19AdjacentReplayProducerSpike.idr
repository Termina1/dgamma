module DGamma.CP5O19AdjacentReplayProducerSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4TerminalRecovery
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| B1: public lower-level internality, without opening any frozen private
||| helper or changing a visibility boundary. Single observed-root elimination.
public export
0 o19LifecycleInternal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {before, afterState : SystemState name key value world error} ->
  (step : Transition before afterState) ->
  (isLifecycleAction (transitionAction step) = True) ->
  RootOrchestrationStep nameEq step -> Void
o19LifecycleInternal nameEq step lifecycle (RootInsertStep action) =
  uninhabited (trans (sym (cong isLifecycleAction action)) lifecycle)
o19LifecycleInternal nameEq step lifecycle (RootRetireStep fiber found parent action) =
  uninhabited (trans (sym (cong isLifecycleAction action)) lifecycle)
o19LifecycleInternal nameEq step lifecycle (RootRemoveStep fiber found parent action) =
  uninhabited (trans (sym (cong isLifecycleAction action)) lifecycle)

||| B2: consume an actual paper activation constructor, not a Boolean oracle.
public export
0 o19ActivationInternal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {before, afterState : SystemState name key value world error} ->
  (step : Transition before afterState) -> PaperActivationStep step ->
  RootOrchestrationStep nameEq step -> Void
o19ActivationInternal nameEq step (PaperBeginStep action tag) =
  o19LifecycleInternal nameEq step (trans (cong isLifecycleAction action) Refl)
o19ActivationInternal nameEq step (PaperIterStep action tag) =
  o19LifecycleInternal nameEq step (trans (cong isLifecycleAction action) Refl)
o19ActivationInternal nameEq step (PaperFinishStep action tag) =
  o19LifecycleInternal nameEq step (trans (cong isLifecycleAction action) Refl)

||| B3: exact four-node external evidence for the SAME diamond. Nothing about
||| root placement or independently invented moved transitions is assumed.
public export
0 o19ActivationPairExternal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, last : SystemState name key value world error} ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  PaperActivationStep left -> PaperActivationStep right ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  SameExternalOrchestration nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions (movedRight diamond) (MoreTransitions (movedLeft diamond) NoTransitions))
o19ActivationPairExternal nameEq keyEq left right leftActivation rightActivation diamond =
  SkipLeftInternal left (MoreTransitions right NoTransitions)
    (o19ActivationInternal nameEq left leftActivation)
    (SkipLeftInternal right NoTransitions (o19ActivationInternal nameEq right rightActivation)
      (SkipRightInternal (movedRight diamond) (MoreTransitions (movedLeft diamond) NoTransitions)
        (o19ActivationInternal nameEq (movedRight diamond) (movedRightActivationBranch diamond rightActivation))
        (SkipRightInternal (movedLeft diamond) NoTransitions
          (o19ActivationInternal nameEq (movedLeft diamond) (movedLeftActivationBranch diamond leftActivation))
          SameExternalOrchestrationEnd)))

||| B4: authentic two-node occurrence embedding with explicit observed
||| occurrence. No captured iterator descriptor and no inferred local view.
public export
0 o19PairOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, first, middle, last, finalState, selectedBefore, selectedAfter :
    SystemState name key value world error} ->
  (earlier : Transitions initial first) ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  (later : Transitions last finalState) ->
  (selected : Transition selectedBefore selectedAfter) ->
  OccursIn selected (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  OccursIn selected (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)))
o19PairOccurrence NoTransitions left right later _ OccursHere = OccursHere
o19PairOccurrence NoTransitions left right later _ (OccursLater OccursHere) =
  OccursLater OccursHere
o19PairOccurrence NoTransitions left right later _ (OccursLater (OccursLater absent)) impossible
o19PairOccurrence (MoreTransitions head rest) left right later selected occurs =
  OccursLater (o19PairOccurrence rest left right later selected occurs)

||| B5: derive the three local diamond premises from the SAME whole bundle
||| and source decomposition. No extra pair-independent or well-formed oracle.
public export
0 o19SourcePairFacts :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, first, middle, last, finalState : SystemState name key value world error} ->
  (original : Transitions initial finalState) -> (earlier : Transitions initial first) ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  (later : Transitions last finalState) ->
  (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)) = original) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq original ->
  (AlignedTransitions name key world error value nameEq keyEq
     (MoreTransitions left (MoreTransitions right NoTransitions)),
   (registryWellFormed {name = name} {key = key} {value = value} {world = world}
     {error = error} @{nameEq} @{keyEq} first = True),
   TraceIndependent name key world error value keyEq
     (MoreTransitions left (MoreTransitions right NoTransitions)))
o19SourcePairFacts {name} {key} {world} {error} {value}
  nameEq keyEq protocol original earlier left right later decomposition premises =
  (Builtin.fst (alignedAppendSplit (MoreTransitions left (MoreTransitions right NoTransitions)) later
    (Builtin.snd (alignedAppendSplit earlier (MoreTransitions left (MoreTransitions right later))
      (replace {p = AlignedTransitions name key world error value nameEq keyEq}
        (sym decomposition) (replayAligned premises))))),
   alignedTraceWellFormedEnd nameEq keyEq earlier
     (Builtin.fst (alignedAppendSplit earlier (MoreTransitions left (MoreTransitions right later))
       (replace {p = AlignedTransitions name key world error value nameEq keyEq}
         (sym decomposition) (replayAligned premises))))
     (replayInitialWellFormed premises),
   traceIndependentUnderEmbedding
     (\selected, occurs => replace {p = OccursIn selected} decomposition
       (o19PairOccurrence earlier left right later selected occurs))
     (replayIndependent premises))

||| B6: ACTUAL A/A diamond producer from the exact positive early check and
||| existing source bundle. No supplied diamond, target state, or view equality.
||| Propagating block-level applicability to EVERY later crossing remains open.
public export
0 o19ActivationDiamond :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, first, middle, last, finalState : SystemState name key value world error} ->
  (original : Transitions initial finalState) -> (earlier : Transitions initial first) ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  (later : Transitions last finalState) ->
  (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)) = original) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq original ->
  PaperActivationStep left -> PaperActivationStep right ->
  Not (transitionActor left = transitionActor right) ->
  CheckedEarlyApplication name key world error value nameEq keyEq first
    (transitionAction right) (transitionTag right) ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
o19ActivationDiamond {first} nameEq keyEq protocol original earlier left right later
  decomposition premises leftActivation rightActivation distinct early =
  activationActivationDiamondSpike nameEq keyEq left right
    (Fired {before = first} {afterState = earlyApplicationFinal early} nameEq keyEq
      (transitionAction right) (transitionTag right) (earlyApplicationChecked early))
    (Builtin.fst (o19SourcePairFacts nameEq keyEq protocol original earlier left right later decomposition premises))
    (AlignedStep (transitionAction right) (transitionTag right) (earlyApplicationChecked early) NoTransitions AlignedEnd)
    Refl Refl leftActivation rightActivation distinct
    (Builtin.fst (Builtin.snd (o19SourcePairFacts nameEq keyEq protocol original earlier left right later decomposition premises)))
    (Builtin.snd (Builtin.snd (o19SourcePairFacts nameEq keyEq protocol original earlier left right later decomposition premises)))

||| B7: ACTUAL sealed suffix replay, not a result supplied by a caller. The
||| frozen producer transports registration discipline and all15 bundle fields;
||| B3 derives the exact external evidence for the same locally built diamond.
public export
0 o19ActivationPairReplay :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, first, middle, last, finalState : SystemState name key value world error} ->
  (original : Transitions initial finalState) -> (earlier : Transitions initial first) ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  (later : Transitions last finalState) ->
  (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)) = original) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq original ->
  PaperActivationStep left -> PaperActivationStep right ->
  Not (transitionActor left = transitionActor right) ->
  CheckedEarlyApplication name key world error value nameEq keyEq first
    (transitionAction right) (transitionTag right) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right **
   AdjacentSwapResult name key world error value protocol nameEq keyEq original earlier left right later diamond)
o19ActivationPairReplay nameEq keyEq protocol original earlier left right later
  decomposition premises leftActivation rightActivation distinct early =
  (o19ActivationDiamond nameEq keyEq protocol original earlier left right later
      decomposition premises leftActivation rightActivation distinct early **
   adjacentSwapSuffixSpike nameEq keyEq protocol original earlier left right later
     decomposition premises
     (o19ActivationDiamond nameEq keyEq protocol original earlier left right later
      decomposition premises leftActivation rightActivation distinct early)
     (o19ActivationPairExternal nameEq keyEq left right leftActivation rightActivation
       (o19ActivationDiamond nameEq keyEq protocol original earlier left right later
      decomposition premises leftActivation rightActivation distinct early)))

||| B8: genuine one-node operational advance, with the ORIGINAL erased
||| uniqueness premise transported through the sealed actual occurrence fold.
||| Result itself owns the reached bundle/external/registration correspondence.
||| This is one A/A node, NOT yet a WholeBlockSwapDerivation/Cartesian loop.
public export
0 o19AdvanceActivationPair :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, first, middle, last, finalState : SystemState name key value world error} ->
  (original : Transitions initial finalState) -> (earlier : Transitions initial first) ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  (later : Transitions last finalState) ->
  (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)) = original) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq original ->
  (0 sourceUnique : UniqueRawNameInsertions name key world error value nameEq keyEq original) ->
  PaperActivationStep left -> PaperActivationStep right ->
  Not (transitionActor left = transitionActor right) ->
  CheckedEarlyApplication name key world error value nameEq keyEq first
    (transitionAction right) (transitionTag right) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right **
   (result : AdjacentSwapResult name key world error value protocol nameEq keyEq original earlier left right later diamond **
     (NonEmptyFiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq original (swappedTrace result),
      UniqueRawNameInsertions name key world error value nameEq keyEq (swappedTrace result))))
o19AdvanceActivationPair {name} {key} {world} {error} {value}
  nameEq keyEq protocol original earlier left right later decomposition premises
  sourceUnique leftActivation rightActivation distinct early =
  case o19ActivationPairReplay nameEq keyEq protocol original earlier left right later
    decomposition premises leftActivation rightActivation distinct early of
      (diamond ** result) => (diamond ** (result **
        (NonEmptyAdjacentSwap original earlier left right later
          (AdjacentActivationActivation left right leftActivation rightActivation)
          diamond result (swappedTrace result) FiniteAdjacentSwapDone,
         uniqueInsertionsAfterFiniteDerivation name key world error value protocol nameEq keyEq
           (FiniteAdjacentSwapStep original earlier left right later
             (AdjacentActivationActivation left right leftActivation rightActivation)
             diamond result (swappedTrace result) FiniteAdjacentSwapDone) sourceUnique)))

||| B13: identify a reached destination from its ACTUAL aligned equation and
||| another exact checked result. B14 also DERIVES its tag, rather than requiring
||| tag equality first. This avoids ANY observer over a replay builder.
public export
0 o19AlignedDestination :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {before, actualAfter, finalState : SystemState name key value world error} ->
  (step : Transition before actualAfter) -> (rest : Transitions actualAfter finalState) ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions step rest) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (transitionAction step = action) ->
  (expectedAfter : SystemState name key value world error) ->
  (checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, expectedAfter)) ->
  ((transitionTag step = tag), (actualAfter = expectedAfter))
o19AlignedDestination {before} nameEq keyEq _ _
  (AlignedStep actualAction actualTag checked _ _) action tag sameAction expectedAfter expected =
    (cong Builtin.fst (justInjective (trans (sym checked)
      (trans (cong (\observedAction => checkedApplyAction @{nameEq} @{keyEq} observedAction before) sameAction) expected))),
     cong Builtin.snd (justInjective (trans (sym checked)
      (trans (cong (\observedAction => checkedApplyAction @{nameEq} @{keyEq} observedAction before) sameAction) expected))))

||| B15: authenticate the opaque diamond's moved-right cut by DETERMINISM,
||| using its actual alignment/labels. No scalar evaluation of the builder.
public export
0 o19MovedRightDestination :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, last : SystemState name key value world error} ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  (early : CheckedEarlyApplication name key world error value nameEq keyEq first
    (transitionAction right) (transitionTag right)) ->
  (swappedMiddle diamond = earlyApplicationFinal early)
o19MovedRightDestination nameEq keyEq left right diamond early =
  Builtin.snd (o19AlignedDestination nameEq keyEq (movedRight diamond)
    (MoreTransitions (movedLeft diamond) NoTransitions) (movedPairAligned diamond)
    (transitionAction right) (transitionTag right) (movedRightAction diamond)
    (earlyApplicationFinal early) (earlyApplicationChecked early))
