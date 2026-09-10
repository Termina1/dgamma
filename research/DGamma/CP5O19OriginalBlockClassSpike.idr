module DGamma.CP5O19OriginalBlockClassSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5ConfluenceRankObservationSpike
import DGamma.CP5O19PairObservationSpike
import Data.List
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Producer-owned ORIGINAL block-word values and child exclusion. Lifecycle
||| ownership is not silently cast to PaperActivationStep: recovery/tag
||| exclusion still needs the actual final-active/no-unload evolution proof.
public export
data O19BlockWordObservation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (actor, forbidden : name) -> Action name key value world error -> Type where
  BlockOwnLifecycle :
    {name, key, world, error : Type} -> {value : key -> Type} -> {actor, forbidden : name} ->
    {action : Action name key value world error} ->
    (0 lifecycle : isLifecycleAction action = True) -> (0 owner : actionOwner action = actor) ->
    O19BlockWordObservation name key world error value actor forbidden action
  BlockGenerated :
    {name, key, world, error : Type} -> {value : key -> Type} -> {actor, forbidden : name} ->
    {action : Action name key value world error} ->
    (child : name) -> (component : Component key value world error) ->
    (0 inserted : action = OInsert child (ChildOf actor) component) ->
    (0 childSafe : Not (child = forbidden)) ->
    O19BlockWordObservation name key world error value actor forbidden action

||| R206 restricted legacy body: lifecycle and yielded-child edges ONLY.
||| Its embedding uses ActorWithoutForcedRoots; neither owned-child controls
||| nor attached root bundles can be manufactured by this predicate.
public export
data LegacyActorOnly :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (selected : name) -> {first, last : SystemState name key value world error} ->
  Transitions first last -> Type where
  LegacyActorEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {selected : name} -> {state : SystemState name key value world error} ->
    LegacyActorOnly selected (NoTransitions {state})
  LegacyActorStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {selected : name} -> {first, middle, last : SystemState name key value world error} ->
    (step : Transition first middle) -> (rest : Transitions middle last) ->
    (0 lifecycle : isLifecycleAction (transitionAction step) = True) ->
    (0 owned : transitionActor step = selected) ->
    (0 tail : LegacyActorOnly selected rest) ->
    LegacyActorOnly selected (MoreTransitions step rest)
  LegacyActorYield :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {selected, child : name} -> {childComponent : Component key value world error} ->
    {first, middle, last : SystemState name key value world error} ->
    (step : Transition first middle) -> (rest : Transitions middle last) ->
    (0 inserted : transitionAction step = OInsert child (ChildOf selected) childComponent) ->
    (0 tail : LegacyActorOnly selected rest) ->
    LegacyActorOnly selected (MoreTransitions step rest)

||| Derive every ORIGINAL body-word observation simultaneously from actual
||| the EXPLICIT restricted LegacyActorOnly and NoGeneratedChild spines. Registration
||| child/component values and the opposite-actor exclusion are produced.
export
0 o19OwnedSafeWord :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (actor, forbidden : name) -> {first, last : SystemState name key value world error} ->
  (trace : Transitions first last) -> LegacyActorOnly actor trace -> NoGeneratedChild forbidden trace ->
  (action : Action name key value world error) -> Elem action (o19ActionWord trace) ->
  O19BlockWordObservation name key world error value actor forbidden action
o19OwnedSafeWord actor forbidden _ LegacyActorEnd NoGeneratedChildEnd action absent = void (uninhabited absent)
o19OwnedSafeWord actor forbidden _ (LegacyActorStep step rest lifecycle owner tail)
  (NoGeneratedChildStep _ _ excluded safeTail) _ Here =
    BlockOwnLifecycle lifecycle (trans (sym (o19TransitionActorOwner step)) owner)
o19OwnedSafeWord actor forbidden _ (LegacyActorStep step rest lifecycle owner tail)
  (NoGeneratedChildStep _ _ excluded safeTail) action (There member) =
    o19OwnedSafeWord actor forbidden rest tail safeTail action member
o19OwnedSafeWord actor forbidden _ (LegacyActorYield {child} {childComponent} step rest inserted tail)
  (NoGeneratedChildStep _ _ excluded safeTail) _ Here =
    BlockGenerated child childComponent inserted
      (\same => excluded actor childComponent (trans inserted (cong (\selected => OInsert selected (ChildOf actor) childComponent) same)))
o19OwnedSafeWord actor forbidden _ (LegacyActorYield step rest inserted tail)
  (NoGeneratedChildStep _ _ excluded safeTail) action (There member) =
    o19OwnedSafeWord actor forbidden rest tail safeTail action member

||| CONDITIONAL legacy located block-word values/ownership/licensing exclusion:
||| the actual Begin supplies the head; the EXPLICIT legacy/safe body supplies
||| every tail occurrence. No word classifier is assumed from the caller.
export
0 o19OriginalBlockWord :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> (actor, forbidden : name) ->
  {initial, finalState : SystemState name key value world error} ->
  {source : Transitions initial finalState} ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq actor source) ->
  LegacyActorOnly actor (blockBody block) ->
  NoGeneratedChild forbidden (blockBody block) ->
  (action : Action name key value world error) -> Elem action (o19ActionWord (actorBlockTrace block)) ->
  O19BlockWordObservation name key world error value actor forbidden action
o19OriginalBlockWord actor forbidden block legacy safe _ Here = BlockOwnLifecycle Refl Refl
o19OriginalBlockWord actor forbidden block legacy safe action (There member) =
  o19OwnedSafeWord actor forbidden (blockBody block) legacy safe action member

||| Actual ORIGINAL births with distinct licensing parents have distinct raw
||| child names, by original UniqueRawNameInsertions and immutable birth
||| metadata. No independent row collision/renaming assumption is requested.
export
0 o19OriginalChildrenDistinct :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) -> UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  (leftParent, rightParent, leftChild, rightChild : name) ->
  (leftComponent, rightComponent : Component key value world error) -> Not (leftParent = rightParent) ->
  LocatedActionOccurrence (OInsert leftChild (ChildOf leftParent) leftComponent) source ->
  LocatedActionOccurrence (OInsert rightChild (ChildOf rightParent) rightComponent) source ->
  Not (rightChild = leftChild)
o19OriginalChildrenDistinct {name} {key} {world} {error} {value} nameEq keyEq source unique leftParent rightParent leftChild rightChild
  leftComponent rightComponent parentsDifferent leftBirth rightBirth same = case same of
    Refl => case cong Builtin.fst
      (uniqueRawBirthMetadata name key world error value nameEq keyEq source unique leftChild
        (ChildOf leftParent) (ChildOf rightParent) leftComponent rightComponent leftBirth rightBirth) of
      Refl => parentsDifferent Refl

||| CONDITIONAL selected legacy block observations. The actual safety owns
||| both child exclusions, but no longer implies the two legacy shape inputs.
||| Production attached blocks must instead use the expanded observation.
export
0 o19SanctionedOriginalWords :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  LegacyActorOnly (actorLeft swap) (blockBody (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) ->
  LegacyActorOnly (actorRight swap) (blockBody (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))) ->
  (leftAction, rightAction : Action name key value world error) ->
  Elem leftAction (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ->
  Elem rightAction (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ->
  (O19BlockWordObservation name key world error value (actorLeft swap) (actorRight swap) leftAction,
   O19BlockWordObservation name key world error value (actorRight swap) (actorLeft swap) rightAction)
o19SanctionedOriginalWords nameEq keyEq protocol swap source blocks premises safety leftLegacy rightLegacy leftAction rightAction leftMember rightMember =
  (o19OriginalBlockWord (actorLeft swap) (actorRight swap) (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))
     leftLegacy (safetyLeftDoesNotGenerateRight safety) leftAction leftMember,
   o19OriginalBlockWord (actorRight swap) (actorLeft swap) (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))
     rightLegacy (safetyRightDoesNotGenerateLeft safety) rightAction rightMember)

||| The actual explicit insertion-plan constructor owns its exact source tag.
||| This is a constructor elimination, not a Refl observer of an independent
||| nested builder. Used to discharge genuine original O/O and A/O tags.
export
0 o19ObservedOriginalInsertTag :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) -> (parent : Parent name) ->
  (component : Component key value world error) -> (ambient : world) ->
  (source : Registry name key value world error) -> (tag : RuleTag) ->
  (afterState : SystemState name key value world error) ->
  ForeignInsertPlanView name key world error value nameEq keyEq child parent component ambient source tag afterState ->
  tag = OInsertTag
o19ObservedOriginalInsertTag nameEq keyEq child parent component ambient source _ _ (MkForeignInsertPlanView absent guards) = Refl

||| Original aligned actual insertion discharges its tag through the actual
||| checked application and explicit F6 plan observation. No tag premise.
export
0 o19AlignedOriginalInsertTag :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) -> (parent : Parent name) ->
  (component : Component key value world error) -> (before, afterState : SystemState name key value world error) ->
  (step : Transition before afterState) ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions step NoTransitions) ->
  transitionAction step = OInsert child parent component -> transitionTag step = OInsertTag
o19AlignedOriginalInsertTag nameEq keyEq child parent component (MkSystemState ambient fibers) afterState _
  (AlignedStep action tag checked _ AlignedEnd) inserted = case inserted of
    Refl => o19ObservedOriginalInsertTag nameEq keyEq child parent component ambient fibers tag afterState
      (foreignInsertPlanView nameEq keyEq child parent component ambient fibers tag afterState
        (checkedActionProjects nameEq keyEq (OInsert child parent component) (MkSystemState ambient fibers) afterState tag checked))

||| CONDITIONAL assembler, NOT the original classifier. The two VISIBLE
||| PaperActivationStep completeness arguments remain hard open: they must
||| be produced from actual block final-active/no-unload evolution excluding
||| absorbing Unloading. Installed-at-cuts is NOT a paper-rule cast. These
||| are NOT new public O19 premises and this conditional result does NOT
||| authorize an input-free column instantiation or any O19 body.
|||
||| All four static constructor/licensing branches are assembled from the
||| explicit producer-owned F5 observations and actual ORIGINAL locations.
||| O/O derives collision exclusion from original unique births and its
||| actual original right tag from original aligned checked application;
||| that branch does not invoke either missing paper-branch argument.
export
0 o19OriginalClassesConditional :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  {leftAction, rightAction : Action name key value world error} ->
  (leftOrigin : LocatedActionOccurrence leftAction source) -> (rightOrigin : LocatedActionOccurrence rightAction source) ->
  (observed : (O19BlockWordObservation name key world error value (actorLeft swap) (actorRight swap) leftAction,
               O19BlockWordObservation name key world error value (actorRight swap) (actorLeft swap) rightAction)) ->
  (0 leftPaperBranch : isLifecycleAction leftAction = True -> PaperActivationStep (locatedTransition leftOrigin)) ->
  (0 rightPaperBranch : isLifecycleAction rightAction = True -> PaperActivationStep (locatedTransition rightOrigin)) ->
  O19SourcePairObservation name key world error value (actorLeft swap) (actorRight swap)
    (locatedTransition leftOrigin) (locatedTransition rightOrigin)
o19OriginalClassesConditional nameEq keyEq protocol swap source premises unique leftOrigin rightOrigin
  (BlockOwnLifecycle leftLife leftOwner, BlockOwnLifecycle rightLife rightOwner) leftPaperBranch rightPaperBranch =
    SourceAA (leftPaperBranch leftLife) (rightPaperBranch rightLife)
      (trans (o19TransitionActorOwner (locatedTransition leftOrigin)) (trans (cong actionOwner (locatedAction leftOrigin)) leftOwner))
      (trans (o19TransitionActorOwner (locatedTransition rightOrigin)) (trans (cong actionOwner (locatedAction rightOrigin)) rightOwner))
o19OriginalClassesConditional nameEq keyEq protocol swap source premises unique leftOrigin rightOrigin
  (BlockGenerated child component inserted childSafe, BlockOwnLifecycle rightLife rightOwner) leftPaperBranch rightPaperBranch =
    SourceOA child component (trans (locatedAction leftOrigin) inserted) (rightPaperBranch rightLife)
      (trans (o19TransitionActorOwner (locatedTransition rightOrigin)) (trans (cong actionOwner (locatedAction rightOrigin)) rightOwner))
      (\same => childSafe (sym same))
o19OriginalClassesConditional nameEq keyEq protocol swap source premises unique leftOrigin rightOrigin
  (BlockOwnLifecycle leftLife leftOwner, BlockGenerated child component inserted childSafe) leftPaperBranch rightPaperBranch =
    SourceAO child component (trans (locatedAction rightOrigin) inserted) (leftPaperBranch leftLife)
      (\same => childSafe (trans same
        (trans (o19TransitionActorOwner (locatedTransition leftOrigin)) (trans (cong actionOwner (locatedAction leftOrigin)) leftOwner))))
      (\licensor, parentSame, ownerSame => case parentSame of
        Refl => actorDistinct swap (trans
          (sym (trans (o19TransitionActorOwner (locatedTransition leftOrigin)) (trans (cong actionOwner (locatedAction leftOrigin)) leftOwner))) ownerSame))
o19OriginalClassesConditional {name} {key} {world} {error} {value} nameEq keyEq protocol swap source premises unique leftOrigin rightOrigin
  (BlockGenerated leftChild leftComponent leftInsert leftSafe, BlockGenerated rightChild rightComponent rightInsert rightSafe)
  leftPaperBranch rightPaperBranch =
    SourceOO leftChild rightChild leftComponent rightComponent (trans (locatedAction leftOrigin) leftInsert) (trans (locatedAction rightOrigin) rightInsert)
      (o19OriginalChildrenDistinct nameEq keyEq source unique (actorLeft swap) (actorRight swap) leftChild rightChild leftComponent rightComponent (actorDistinct swap)
        (MkLocatedActionOccurrence (actionBeforeState leftOrigin) (actionAfterState leftOrigin) (beforeActionOccurrence leftOrigin)
          (locatedTransition leftOrigin) (afterActionOccurrence leftOrigin) (trans (locatedAction leftOrigin) leftInsert) (actionOccurrenceDecomposition leftOrigin))
        (MkLocatedActionOccurrence (actionBeforeState rightOrigin) (actionAfterState rightOrigin) (beforeActionOccurrence rightOrigin)
          (locatedTransition rightOrigin) (afterActionOccurrence rightOrigin) (trans (locatedAction rightOrigin) rightInsert) (actionOccurrenceDecomposition rightOrigin)))
      (\licensor, parentSame, childSame => case parentSame of Refl => rightSafe childSame)
      (\licensor, parentSame, childSame => case parentSame of Refl => leftSafe childSame)
      (o19AlignedOriginalInsertTag nameEq keyEq rightChild (ChildOf (actorRight swap)) rightComponent
        (actionBeforeState rightOrigin) (actionAfterState rightOrigin) (locatedTransition rightOrigin)
        (fst (alignedAppendSplit (MoreTransitions (locatedTransition rightOrigin) NoTransitions) (afterActionOccurrence rightOrigin)
          (snd (alignedAppendSplit (beforeActionOccurrence rightOrigin) (MoreTransitions (locatedTransition rightOrigin) (afterActionOccurrence rightOrigin))
            (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym (actionOccurrenceDecomposition rightOrigin)) (replayAligned premises))))))
        (trans (locatedAction rightOrigin) rightInsert))

||| R206 honest enlarged ORIGINAL word observation. Child controls retain
||| their actual source lookup and owner-parent metadata; attached roots retain
||| root tags/source metadata. These are NOT replay-frame facts at a new cut.
public export
data O19ExpandedBlockWordObservation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (actor, forbidden : name) ->
  Action name key value world error -> Type where
  ExpandedLegacy :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor, forbidden : name} ->
    {action : Action name key value world error} ->
    O19BlockWordObservation name key world error value actor forbidden action ->
    O19ExpandedBlockWordObservation name key world error value nameEq actor forbidden action
  ExpandedChildRetire :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor, forbidden : name} ->
    {action : Action name key value world error} ->
    (controlled : name) -> (fiber : Fiber name key value world error) ->
    (before : SystemState name key value world error) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} controlled (registry before) = Just fiber) ->
    (0 parent : fiberParent fiber = ChildOf actor) ->
    (0 actionExact : action = ORetire controlled) ->
    O19ExpandedBlockWordObservation name key world error value nameEq actor forbidden action
  ExpandedChildRemove :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor, forbidden : name} ->
    {action : Action name key value world error} ->
    (controlled : name) -> (fiber : Fiber name key value world error) ->
    (before : SystemState name key value world error) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} controlled (registry before) = Just fiber) ->
    (0 parent : fiberParent fiber = ChildOf actor) ->
    (0 actionExact : action = ORemove controlled) ->
    O19ExpandedBlockWordObservation name key world error value nameEq actor forbidden action
  ExpandedRootRetire :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor, forbidden : name} ->
    {action : Action name key value world error} ->
    (controlled : name) -> (fiber : Fiber name key value world error) ->
    (before : SystemState name key value world error) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} controlled (registry before) = Just fiber) ->
    (0 parent : fiberParent fiber = Root) ->
    (0 actionExact : action = ORetire controlled) ->
    O19ExpandedBlockWordObservation name key world error value nameEq actor forbidden action
  ExpandedRootRemove :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor, forbidden : name} ->
    {action : Action name key value world error} ->
    (controlled : name) -> (fiber : Fiber name key value world error) ->
    (before : SystemState name key value world error) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} controlled (registry before) = Just fiber) ->
    (0 parent : fiberParent fiber = Root) ->
    (0 actionExact : action = ORemove controlled) ->
    O19ExpandedBlockWordObservation name key world error value nameEq actor forbidden action
  ExpandedRootInsert :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor, forbidden : name} ->
    {action : Action name key value world error} ->
    (root : name) -> (component : Component key value world error) ->
    (0 inserted : action = OInsert root Root component) ->
    O19ExpandedBlockWordObservation name key world error value nameEq actor forbidden action

||| Complete production CORE observation, including both owned-child controls.
||| NoGeneratedChild only excludes generated insertions, never existing children.
export
0 o19CoreSafeWord :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor, forbidden : name) ->
  {first, last : SystemState name key value world error} ->
  (trace : Transitions first last) -> ActorLifecycleCore nameEq actor trace ->
  NoGeneratedChild forbidden trace ->
  (action : Action name key value world error) -> Elem action (o19ActionWord trace) ->
  O19ExpandedBlockWordObservation name key world error value nameEq actor forbidden action
o19CoreSafeWord nameEq actor forbidden _ CoreLifecycleEnd NoGeneratedChildEnd action absent =
  void (uninhabited absent)
o19CoreSafeWord nameEq actor forbidden _ (CoreLifecycleStep step rest lifecycle owner tail)
  (NoGeneratedChildStep _ _ excluded safeTail) action member = case member of
    Here => ExpandedLegacy (BlockOwnLifecycle lifecycle (trans (sym (o19TransitionActorOwner step)) owner))
    There later => o19CoreSafeWord nameEq actor forbidden rest tail safeTail action later
o19CoreSafeWord nameEq actor forbidden _ (CoreYieldedRegistrationStep {child} {component} step rest inserted tail)
  (NoGeneratedChildStep _ _ excluded safeTail) action member = case member of
    Here => ExpandedLegacy (BlockGenerated child component inserted
      (\same => excluded actor component (trans inserted (cong (\selected => OInsert selected (ChildOf actor) component) same))))
    There later => o19CoreSafeWord nameEq actor forbidden rest tail safeTail action later
o19CoreSafeWord nameEq actor forbidden _ (CoreChildRetireStep {first} step rest child fiber found parent controlled tail)
  (NoGeneratedChildStep _ _ excluded safeTail) action member = case member of
    Here => ExpandedChildRetire child fiber first found parent controlled
    There later => o19CoreSafeWord nameEq actor forbidden rest tail safeTail action later
o19CoreSafeWord nameEq actor forbidden _ (CoreChildRemoveStep {first} step rest child fiber found parent controlled tail)
  (NoGeneratedChildStep _ _ excluded safeTail) action member = case member of
    Here => ExpandedChildRemove child fiber first found parent controlled
    There later => o19CoreSafeWord nameEq actor forbidden rest tail safeTail action later

||| Every attached-bundle word is a root insertion or a root control. The
||| weaker word view does not assert transport of its original forcing reason.
export
0 o19BundleWord :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor, forbidden : name) ->
  {first, coreEnd, bundleStart, last : SystemState name key value world error} ->
  {core : Transitions first coreEnd} -> {priorRoots : List name} ->
  (bundle : Transitions bundleStart last) ->
  OrderedForcedRootBundle nameEq actor core priorRoots bundle ->
  (action : Action name key value world error) -> Elem action (o19ActionWord bundle) ->
  O19ExpandedBlockWordObservation name key world error value nameEq actor forbidden action
o19BundleWord nameEq actor forbidden _ ForcedBundleEnd action absent = void (uninhabited absent)
o19BundleWord nameEq actor forbidden _ (ForcedBundleInsert root component step rest inserted forced tail) action member = case member of
  Here => ExpandedRootInsert root component inserted
  There later => o19BundleWord nameEq actor forbidden rest tail action later
o19BundleWord nameEq actor forbidden _ (ForcedBundleRetire {before} root fiber step rest bundled found parent controlled tail) action member = case member of
  Here => ExpandedRootRetire root fiber before found parent controlled
  There later => o19BundleWord nameEq actor forbidden rest tail action later
o19BundleWord nameEq actor forbidden _ (ForcedBundleRemove {before} root fiber step rest bundled found parent controlled tail) action member = case member of
  Here => ExpandedRootRemove root fiber before found parent controlled
  There later => o19BundleWord nameEq actor forbidden rest tail action later

||| Restrict authentic generated-child exclusion to the actual native prefix.
export
0 o19NoGeneratedPrefix :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (forbidden : name) -> {first, middle, last : SystemState name key value world error} ->
  (prior : Transitions first middle) -> (suffix : Transitions middle last) ->
  NoGeneratedChild forbidden (appendTransitions prior suffix) ->
  NoGeneratedChild forbidden prior
o19NoGeneratedPrefix forbidden NoTransitions suffix safe = NoGeneratedChildEnd
o19NoGeneratedPrefix forbidden (MoreTransitions step rest) suffix (NoGeneratedChildStep _ _ excluded safeTail) =
  NoGeneratedChildStep step rest excluded (o19NoGeneratedPrefix forbidden rest suffix safeTail)

||| Consumer-shaped elimination of an actual native append word membership.
||| This avoids inventing a source-state view from a copied action label.
export
0 o19NativeWordAppendCases :
  {name, key, world, error : Type} -> {value : key -> Type} -> {result : Type} ->
  {first, middle, last : SystemState name key value world error} ->
  (prior : Transitions first middle) -> (later : Transitions middle last) ->
  (action : Action name key value world error) ->
  (Elem action (o19ActionWord prior) -> result) ->
  (Elem action (o19ActionWord later) -> result) ->
  Elem action (o19ActionWord (appendTransitions prior later)) -> result
o19NativeWordAppendCases NoTransitions later action inPrior inLater member = inLater member
o19NativeWordAppendCases (MoreTransitions step rest) later _ inPrior inLater Here = inPrior Here
o19NativeWordAppendCases (MoreTransitions step rest) later action inPrior inLater (There member) =
  o19NativeWordAppendCases rest later action (\there => inPrior (There there)) inLater member

||| TOTAL production body observation: both attached wrappers and every core
||| and bundle constructor are covered. The old four-orientation classifier
||| consumes only the separately restricted legacy observation.
export
0 o19ExpandedOwnedSafeWord :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor, forbidden : name) ->
  {first, last : SystemState name key value world error} ->
  (trace : Transitions first last) -> ActorLifecycleOnly nameEq actor trace ->
  NoGeneratedChild forbidden trace ->
  (action : Action name key value world error) -> Elem action (o19ActionWord trace) ->
  O19ExpandedBlockWordObservation name key world error value nameEq actor forbidden action
o19ExpandedOwnedSafeWord nameEq actor forbidden _ (ActorWithoutForcedRoots core only) safe action member =
  o19CoreSafeWord nameEq actor forbidden core only safe action member
o19ExpandedOwnedSafeWord nameEq actor forbidden _ (ActorWithForcedRoots core only bundle ordered) safe action member =
  o19NativeWordAppendCases core bundle action
    (o19CoreSafeWord nameEq actor forbidden core only (o19NoGeneratedPrefix forbidden core bundle safe) action)
    (o19BundleWord nameEq actor forbidden bundle ordered action) member
