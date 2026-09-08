module DGamma.CP5O19PairObservationSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19MixedActivationRowSpike
import DGamma.CP5O19ResolvedOpeningRowSpike
import DGamma.CP5O19ActivationInsertionRowSpike
import DGamma.CP5O19CartesianInsertionSpike
import Data.List
import Decidable.Equality

%default total
%unbound_implicits off

||| Supervisor-authorized D4 representation cure. Four typed ACTUAL pair
||| observations, with source values/equations only. The orientation index
||| allows each producer helper to eliminate exactly ONE constructor. No guard,
||| diamond, replay, row, target state or caller result is stored here.
public export
data O19PairObservation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (leftParent, rightParent : name) ->
  {first, middle, last : SystemState name key value world error} ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  AdjacentSwapOrientationEvidence left right -> Type where
  ObservedAA :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {leftParent, rightParent : name} ->
    {first, middle, last : SystemState name key value world error} ->
    {left : Transition first middle} -> {right : Transition middle last} ->
    (0 leftActivation : PaperActivationStep left) -> (0 rightActivation : PaperActivationStep right) ->
    (0 leftOwner : transitionActor left = leftParent) -> (0 rightOwner : transitionActor right = rightParent) ->
    O19PairObservation name key world error value leftParent rightParent left right
      (AdjacentActivationActivation left right leftActivation rightActivation)
  ObservedOA :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {leftParent, rightParent : name} ->
    {first, middle, last : SystemState name key value world error} ->
    {left : Transition first middle} -> {right : Transition middle last} ->
    (child : name) -> (component : Component key value world error) ->
    (0 inserted : transitionAction left = OInsert child (ChildOf leftParent) component) ->
    (0 rightActivation : PaperActivationStep right) -> (0 rightOwner : transitionActor right = rightParent) ->
    (0 childSafe : Not (rightParent = child)) ->
    O19PairObservation name key world error value leftParent rightParent left right
      (AdjacentOrchestrationActivation left right (PaperInsertStep inserted) rightActivation)
  ObservedAO :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {leftParent, rightParent : name} ->
    {first, middle, last : SystemState name key value world error} ->
    {left : Transition first middle} -> {right : Transition middle last} ->
    (child : name) -> (component : Component key value world error) ->
    (0 inserted : transitionAction right = OInsert child (ChildOf rightParent) component) ->
    (0 leftActivation : PaperActivationStep left) -> (0 distinct : Not (child = transitionActor left)) ->
    (0 licensing : (licensor : name) -> (ChildOf rightParent = ChildOf licensor) -> Not (transitionActor left = licensor)) ->
    O19PairObservation name key world error value leftParent rightParent left right
      (AdjacentActivationOrchestration left right leftActivation (PaperInsertStep inserted))
  ObservedOO :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {leftParent, rightParent : name} ->
    {first, middle, last : SystemState name key value world error} ->
    {left : Transition first middle} -> {right : Transition middle last} ->
    (leftChild, rightChild : name) -> (leftComponent, rightComponent : Component key value world error) ->
    (0 leftInsert : transitionAction left = OInsert leftChild (ChildOf leftParent) leftComponent) ->
    (0 rightInsert : transitionAction right = OInsert rightChild (ChildOf rightParent) rightComponent) ->
    (0 distinct : Not (rightChild = leftChild)) ->
    (0 leftLicense : (licensor : name) -> (ChildOf leftParent = ChildOf licensor) -> Not (rightChild = licensor)) ->
    (0 rightLicense : (licensor : name) -> (ChildOf rightParent = ChildOf licensor) -> Not (leftChild = licensor)) ->
    (0 tag : transitionTag right = OInsertTag) ->
    O19PairObservation name key world error value leftParent rightParent left right
      (AdjacentOrchestrationOrchestration left right (PaperInsertStep leftInsert) (PaperInsertStep rightInsert))

||| Single-observation A/A producer: only ObservedAA can inhabit this index.
||| Original sanctioned safety and the actual current full bundle derive the
||| backwards guard, then the real diamond/sealed suffix replay is built.
export
0 o19ObservedAAReplay :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, originalFinal, first, middle, last : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder original) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq original) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap original blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (cursor : O19ReachedCursor name key world error value protocol nameEq keyEq original) ->
  (earlier : Transitions initial first) -> (left : Transition first middle) -> (right : Transition middle last) ->
  (later : Transitions last (cursorFinal cursor)) ->
  (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)) = cursorTrace cursor) ->
  {leftActivation : PaperActivationStep left} -> {rightActivation : PaperActivationStep right} ->
  O19PairObservation name key world error value (actorLeft swap) (actorRight swap) left right
    (AdjacentActivationActivation left right leftActivation rightActivation) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right **
    AdjacentSwapResult name key world error value protocol nameEq keyEq (cursorTrace cursor) earlier left right later diamond)
o19ObservedAAReplay nameEq keyEq protocol swap original blocks premises safety unique cursor earlier left right later decomposition
  (ObservedAA leftActivation rightActivation leftOwner rightOwner) =
    o19ActivationPairReplay nameEq keyEq protocol (cursorTrace cursor) earlier left right later decomposition (cursorBundle cursor)
      leftActivation rightActivation (\same => actorDistinct swap (trans (sym leftOwner) (trans same rightOwner)))
      (o19ReplayedActivationAligned nameEq keyEq protocol swap original blocks premises safety unique cursor earlier later left right
        decomposition leftOwner rightOwner leftActivation rightActivation
        (fst (o19SourcePairFacts nameEq keyEq protocol (cursorTrace cursor) earlier left right later decomposition (cursorBundle cursor))))

||| Single-observation O/A producer; actual insertion and later activation
||| produce the guard/domain, licensing follows from this observed pair.
export
0 o19ObservedOAReplay :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, originalFinal, first, middle, last : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder original) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq original) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap original blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (cursor : O19ReachedCursor name key world error value protocol nameEq keyEq original) ->
  (earlier : Transitions initial first) -> (left : Transition first middle) -> (right : Transition middle last) ->
  (later : Transitions last (cursorFinal cursor)) ->
  (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)) = cursorTrace cursor) ->
  {leftOrchestration : PaperOrchestrationStep left} -> {rightActivation : PaperActivationStep right} ->
  O19PairObservation name key world error value (actorLeft swap) (actorRight swap) left right
    (AdjacentOrchestrationActivation left right leftOrchestration rightActivation) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right **
    AdjacentSwapResult name key world error value protocol nameEq keyEq (cursorTrace cursor) earlier left right later diamond)
o19ObservedOAReplay nameEq keyEq protocol swap original blocks premises safety unique cursor earlier left right later decomposition
  (ObservedOA child component inserted rightActivation rightOwner childSafe) =
    o19InsertActivationReplay nameEq keyEq protocol child (ChildOf (actorLeft swap)) component (cursorTrace cursor) earlier left right later
      decomposition (cursorBundle cursor) inserted rightActivation
      (\same => childSafe (trans (sym rightOwner) same))
      (\licensor, sameParent, sameActor => case sameParent of Refl => actorDistinct swap (trans (sym sameActor) rightOwner))
      (o19InsertionActivationAligned nameEq keyEq child (ChildOf (actorLeft swap)) component left right inserted
        (\same => childSafe (trans (sym rightOwner) same)) (fst (snd (o19SourcePairFacts nameEq keyEq protocol (cursorTrace cursor) earlier left right later decomposition (cursorBundle cursor)))) (snd (snd (o19SourcePairFacts nameEq keyEq protocol (cursorTrace cursor) earlier left right later decomposition (cursorBundle cursor)))) rightActivation (fst (o19SourcePairFacts nameEq keyEq protocol (cursorTrace cursor) earlier left right later decomposition (cursorBundle cursor))))

||| Single-observation A/O producer uses the actual source insertion and
||| observed licensing, never caller-supplied applicability or replay.
export
0 o19ObservedAOReplay :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, originalFinal, first, middle, last : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder original) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq original) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap original blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (cursor : O19ReachedCursor name key world error value protocol nameEq keyEq original) ->
  (earlier : Transitions initial first) -> (left : Transition first middle) -> (right : Transition middle last) ->
  (later : Transitions last (cursorFinal cursor)) ->
  (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)) = cursorTrace cursor) ->
  {leftActivation : PaperActivationStep left} -> {rightOrchestration : PaperOrchestrationStep right} ->
  O19PairObservation name key world error value (actorLeft swap) (actorRight swap) left right
    (AdjacentActivationOrchestration left right leftActivation rightOrchestration) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right **
    AdjacentSwapResult name key world error value protocol nameEq keyEq (cursorTrace cursor) earlier left right later diamond)
o19ObservedAOReplay nameEq keyEq protocol swap original blocks premises safety unique cursor earlier left right later decomposition
  (ObservedAO child component inserted leftActivation distinct licensing) =
    o19ActivationInsertReplay nameEq keyEq protocol child (ChildOf (actorRight swap)) component (cursorTrace cursor)
      earlier left right later decomposition (cursorBundle cursor) leftActivation inserted distinct licensing

||| Single-observation generated O/O producer: actual children/components,
||| action equations, cross-licensing and right tag feed the proven real node.
export
0 o19ObservedOOReplay :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, originalFinal, first, middle, last : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder original) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq original) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap original blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (cursor : O19ReachedCursor name key world error value protocol nameEq keyEq original) ->
  (earlier : Transitions initial first) -> (left : Transition first middle) -> (right : Transition middle last) ->
  (later : Transitions last (cursorFinal cursor)) ->
  (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)) = cursorTrace cursor) ->
  {leftOrchestration : PaperOrchestrationStep left} -> {rightOrchestration : PaperOrchestrationStep right} ->
  O19PairObservation name key world error value (actorLeft swap) (actorRight swap) left right
    (AdjacentOrchestrationOrchestration left right leftOrchestration rightOrchestration) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right **
    AdjacentSwapResult name key world error value protocol nameEq keyEq (cursorTrace cursor) earlier left right later diamond)
o19ObservedOOReplay nameEq keyEq protocol swap original blocks premises safety unique cursor earlier left right later decomposition
  (ObservedOO leftChild rightChild leftComponent rightComponent leftInsert rightInsert distinct leftLicense rightLicense tag) =
    o19GeneratedInsertionReplay nameEq keyEq protocol leftChild rightChild (actorLeft swap) (actorRight swap) leftComponent rightComponent
      (cursorTrace cursor) earlier left right later decomposition (cursorBundle cursor) leftInsert rightInsert distinct leftLicense rightLicense tag

||| TOTAL producer is a projection over the typed actual observation. Each
||| branch delegates to its single-constructor producer; no nested Either/
||| DPair case, speculative classification or separately chosen node remains.
export
0 o19ObservedPairReplay :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, originalFinal, first, middle, last : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder original) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq original) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap original blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (cursor : O19ReachedCursor name key world error value protocol nameEq keyEq original) ->
  (earlier : Transitions initial first) -> (left : Transition first middle) -> (right : Transition middle last) ->
  (later : Transitions last (cursorFinal cursor)) ->
  (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)) = cursorTrace cursor) ->
  {orientation : AdjacentSwapOrientationEvidence left right} ->
  O19PairObservation name key world error value (actorLeft swap) (actorRight swap) left right orientation ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right **
    AdjacentSwapResult name key world error value protocol nameEq keyEq (cursorTrace cursor) earlier left right later diamond)
o19ObservedPairReplay nameEq keyEq protocol swap original blocks premises safety unique cursor earlier left right later decomposition
  (ObservedAA leftActivation rightActivation leftOwner rightOwner) =
    o19ObservedAAReplay nameEq keyEq protocol swap original blocks premises safety unique cursor earlier left right later decomposition (ObservedAA leftActivation rightActivation leftOwner rightOwner)
o19ObservedPairReplay nameEq keyEq protocol swap original blocks premises safety unique cursor earlier left right later decomposition
  (ObservedOA child component inserted rightActivation rightOwner childSafe) =
    o19ObservedOAReplay nameEq keyEq protocol swap original blocks premises safety unique cursor earlier left right later decomposition (ObservedOA child component inserted rightActivation rightOwner childSafe)
o19ObservedPairReplay nameEq keyEq protocol swap original blocks premises safety unique cursor earlier left right later decomposition
  (ObservedAO child component inserted leftActivation distinct licensing) =
    o19ObservedAOReplay nameEq keyEq protocol swap original blocks premises safety unique cursor earlier left right later decomposition (ObservedAO child component inserted leftActivation distinct licensing)
o19ObservedPairReplay nameEq keyEq protocol swap original blocks premises safety unique cursor earlier left right later decomposition
  (ObservedOO leftChild rightChild leftComponent rightComponent leftInsert rightInsert distinct leftLicense rightLicense tag) =
    o19ObservedOOReplay nameEq keyEq protocol swap original blocks premises safety unique cursor earlier left right later decomposition (ObservedOO leftChild rightChild leftComponent rightComponent leftInsert rightInsert distinct leftLicense rightLicense tag)

||| Supervisor-authorized D10: flat SOURCE observations for two still
||| separated nodes. Independent endpoints are deliberate. Values and exact
||| action/tag/owner/licensing equations transport to the later actual pair;
||| no future check, guard, diamond, replay or row is predicted here.
public export
data O19SourcePairObservation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (leftParent, rightParent : name) ->
  {leftBefore, leftAfter, rightBefore, rightAfter : SystemState name key value world error} ->
  (left : Transition leftBefore leftAfter) -> (right : Transition rightBefore rightAfter) ->
  Type where
  SourceAA :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {leftParent, rightParent : name} ->
    {leftBefore, leftAfter, rightBefore, rightAfter : SystemState name key value world error} ->
    {left : Transition leftBefore leftAfter} -> {right : Transition rightBefore rightAfter} ->
    (0 leftActivation : PaperActivationStep left) -> (0 rightActivation : PaperActivationStep right) ->
    (0 leftOwner : transitionActor left = leftParent) -> (0 rightOwner : transitionActor right = rightParent) ->
    O19SourcePairObservation name key world error value leftParent rightParent left right
  SourceOA :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {leftParent, rightParent : name} ->
    {leftBefore, leftAfter, rightBefore, rightAfter : SystemState name key value world error} ->
    {left : Transition leftBefore leftAfter} -> {right : Transition rightBefore rightAfter} ->
    (child : name) -> (component : Component key value world error) ->
    (0 inserted : transitionAction left = OInsert child (ChildOf leftParent) component) ->
    (0 rightActivation : PaperActivationStep right) -> (0 rightOwner : transitionActor right = rightParent) ->
    (0 childSafe : Not (rightParent = child)) ->
    O19SourcePairObservation name key world error value leftParent rightParent left right
  SourceAO :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {leftParent, rightParent : name} ->
    {leftBefore, leftAfter, rightBefore, rightAfter : SystemState name key value world error} ->
    {left : Transition leftBefore leftAfter} -> {right : Transition rightBefore rightAfter} ->
    (child : name) -> (component : Component key value world error) ->
    (0 inserted : transitionAction right = OInsert child (ChildOf rightParent) component) ->
    (0 leftActivation : PaperActivationStep left) -> (0 distinct : Not (child = transitionActor left)) ->
    (0 licensing : (licensor : name) -> (ChildOf rightParent = ChildOf licensor) -> Not (transitionActor left = licensor)) ->
    O19SourcePairObservation name key world error value leftParent rightParent left right
  SourceOO :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {leftParent, rightParent : name} ->
    {leftBefore, leftAfter, rightBefore, rightAfter : SystemState name key value world error} ->
    {left : Transition leftBefore leftAfter} -> {right : Transition rightBefore rightAfter} ->
    (leftChild, rightChild : name) -> (leftComponent, rightComponent : Component key value world error) ->
    (0 leftInsert : transitionAction left = OInsert leftChild (ChildOf leftParent) leftComponent) ->
    (0 rightInsert : transitionAction right = OInsert rightChild (ChildOf rightParent) rightComponent) ->
    (0 distinct : Not (rightChild = leftChild)) ->
    (0 leftLicense : (licensor : name) -> (ChildOf leftParent = ChildOf licensor) -> Not (rightChild = licensor)) ->
    (0 rightLicense : (licensor : name) -> (ChildOf rightParent = ChildOf licensor) -> Not (leftChild = licensor)) ->
    (0 tag : transitionTag right = OInsertTag) ->
    O19SourcePairObservation name key world error value leftParent rightParent left right

||| Structural paper-branch transport through the ACTUAL right action/tag
||| equations. No checked edge or successful tag is guessed by this adapter.
export
0 o19PaperActivationRelabel :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {sourceBefore, sourceAfter, reachedBefore, reachedAfter : SystemState name key value world error} ->
  (source : Transition sourceBefore sourceAfter) -> (reached : Transition reachedBefore reachedAfter) ->
  (transitionAction reached = transitionAction source) -> (transitionTag reached = transitionTag source) ->
  PaperActivationStep source -> PaperActivationStep reached
o19PaperActivationRelabel source reached action tag (PaperBeginStep sameAction sameTag) =
  PaperBeginStep (trans action sameAction) (trans tag sameTag)
o19PaperActivationRelabel source reached action tag (PaperIterStep sameAction sameTag) =
  PaperIterStep (trans action sameAction) (trans tag sameTag)
o19PaperActivationRelabel source reached action tag (PaperFinishStep sameAction sameTag) =
  PaperFinishStep (trans action sameAction) (trans tag sameTag)

||| Project one flat SOURCE observation onto the ACTUAL adjacent right node,
||| using ONLY its producer-owned action/tag/actor equations. No nested Either
||| or computed existential is eliminated. No applicability/replay is assumed.
export
0 o19SourcePairAtReachedRight :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (leftParent, rightParent : name) ->
  {leftBefore, leftAfter, rightBefore, rightAfter, reachedAfter : SystemState name key value world error} ->
  (left : Transition leftBefore leftAfter) -> (right : Transition rightBefore rightAfter) ->
  (reached : Transition leftAfter reachedAfter) ->
  (transitionAction reached = transitionAction right) -> (transitionTag reached = transitionTag right) ->
  (transitionActor reached = transitionActor right) ->
  O19SourcePairObservation name key world error value leftParent rightParent left right ->
  (orientation : AdjacentSwapOrientationEvidence left reached **
    O19PairObservation name key world error value leftParent rightParent left reached orientation)
o19SourcePairAtReachedRight leftParent rightParent left right reached action tag actor
  (SourceAA leftActivation rightActivation leftOwner rightOwner) =
    (AdjacentActivationActivation left reached leftActivation (o19PaperActivationRelabel right reached action tag rightActivation) **
      ObservedAA leftActivation (o19PaperActivationRelabel right reached action tag rightActivation) leftOwner (trans actor rightOwner))
o19SourcePairAtReachedRight leftParent rightParent left right reached action tag actor
  (SourceOA child component inserted rightActivation rightOwner childSafe) =
    (AdjacentOrchestrationActivation left reached (PaperInsertStep inserted) (o19PaperActivationRelabel right reached action tag rightActivation) **
      ObservedOA child component inserted (o19PaperActivationRelabel right reached action tag rightActivation) (trans actor rightOwner) childSafe)
o19SourcePairAtReachedRight leftParent rightParent left right reached action tag actor
  (SourceAO child component inserted leftActivation distinct licensing) =
    (AdjacentActivationOrchestration left reached leftActivation (PaperInsertStep (trans action inserted)) **
      ObservedAO child component (trans action inserted) leftActivation distinct licensing)
o19SourcePairAtReachedRight leftParent rightParent left right reached action tag actor
  (SourceOO leftChild rightChild leftComponent rightComponent leftInsert rightInsert distinct leftLicense rightLicense rightTag) =
    (AdjacentOrchestrationOrchestration left reached (PaperInsertStep leftInsert) (PaperInsertStep (trans action rightInsert)) **
      ObservedOO leftChild rightChild leftComponent rightComponent leftInsert (trans action rightInsert) distinct leftLicense rightLicense (trans tag rightTag))
