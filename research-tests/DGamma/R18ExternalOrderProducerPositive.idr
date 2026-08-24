module DGamma.R18ExternalOrderProducerPositive

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP3StatementChecks
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

||| Exact node classification supplied by `LocatedOpenEpisodeBlock`: the opening
||| and ordinary body steps are lifecycle actions; yielded registrations are
||| child insertions and therefore are not externally-rooted inputs.
public export
data O19BlockNode :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  (selected : name) ->
  (transition : Transition before afterState) -> Type where
  O19LifecycleNode :
    isLifecycleAction (transitionAction transition) = True ->
    O19BlockNode selected transition
  O19YieldedChildNode :
    transitionAction transition =
      OInsert child (ChildOf selected) component ->
    O19BlockNode selected transition

0 o19BlockNodeInternal :
  O19BlockNode selected transition ->
  RootOrchestrationStep nameEq transition -> Void
o19BlockNodeInternal (O19LifecycleNode lifecycle) =
  lifecycleCannotBeRoot transition lifecycle
o19BlockNodeInternal (O19YieldedChildNode childAction) =
  childInsertCannotBeRoot transition childAction

0 movedO19BlockNode :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {sourceBefore, sourceAfter, movedBefore, movedAfter :
    SystemState name key value world error} ->
  {selected : name} ->
  {source : Transition sourceBefore sourceAfter} ->
  {moved : Transition movedBefore movedAfter} ->
  O19BlockNode selected source ->
  transitionAction moved = transitionAction source ->
  O19BlockNode selected moved
movedO19BlockNode (O19LifecycleNode lifecycle) movedAction =
  O19LifecycleNode (trans (cong isLifecycleAction movedAction) lifecycle)
movedO19BlockNode (O19YieldedChildNode childAction) movedAction =
  O19YieldedChildNode (trans movedAction childAction)

||| Exact projection from the accepted block-body producer. This covers both
||| ordinary lifecycle nodes and yielded child registrations without a caller
||| selecting the classification.
0 o19BodyHeadNode :
  ActorLifecycleOnly selected (MoreTransitions transition rest) ->
  O19BlockNode selected transition
o19BodyHeadNode
  (ActorLifecycleStep transition rest lifecycle selectedActor restOnly) =
    O19LifecycleNode lifecycle
o19BodyHeadNode
  (ActorYieldedRegistrationStep transition rest childAction restOnly) =
    O19YieldedChildNode childAction

||| The separately stored block opening is L-Begin, hence is the third genuine
||| O19 node form required by the Cartesian whole-block producer.
0 o19BeginNode :
  (opening : BeginStep nameEq keyEq selected before afterState) ->
  O19BlockNode selected (beginTransition opening)
o19BeginNode opening = O19LifecycleNode Refl

||| Pair-local external-order capital for one O19 Cartesian crossing. Both
||| source nodes come from exact block positions; the moved classifications are
||| transported only along the local diamond's action equalities.
0 o19InternalPairExternal :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  O19BlockNode leftActor left ->
  O19BlockNode rightActor right ->
  SameExternalOrchestration nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions (movedRight diamond)
      (MoreTransitions (movedLeft diamond) NoTransitions))
o19InternalPairExternal nameEq keyEq left right diamond leftNode rightNode =
  let movedRightNode : O19BlockNode rightActor (movedRight diamond)
      movedRightNode = movedO19BlockNode rightNode (movedRightAction diamond)
      movedLeftNode : O19BlockNode leftActor (movedLeft diamond)
      movedLeftNode = movedO19BlockNode leftNode (movedLeftAction diamond)
  in SkipLeftInternal left (MoreTransitions right NoTransitions)
       (o19BlockNodeInternal leftNode)
       (SkipLeftInternal right NoTransitions
         (o19BlockNodeInternal rightNode)
         (SkipRightInternal (movedRight diamond)
           (MoreTransitions (movedLeft diamond) NoTransitions)
           (o19BlockNodeInternal movedRightNode)
           (SkipRightInternal (movedLeft diamond) NoTransitions
             (o19BlockNodeInternal movedLeftNode)
             SameExternalOrchestrationEnd)))

||| Genuine block-body producer: the classifications are projections of the two
||| `ActorLifecycleOnly` witnesses, not extra premises supplied to O6.
0 genuineO19BodyBodyExternalProducer :
  (nameEq : DecEq name) ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  ActorLifecycleOnly leftActor (MoreTransitions left leftRest) ->
  ActorLifecycleOnly rightActor (MoreTransitions right rightRest) ->
  SameExternalOrchestration nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions (movedRight diamond)
      (MoreTransitions (movedLeft diamond) NoTransitions))
genuineO19BodyBodyExternalProducer nameEq left right diamond leftOnly rightOnly =
  o19InternalPairExternal nameEq keyEq left right diamond
    (o19BodyHeadNode leftOnly) (o19BodyHeadNode rightOnly)

||| Genuine L-Begin/L-Begin producer for the two separately stored block
||| openings. Mixed opening/body crossings use the same `o19InternalPairExternal`
||| constructor with `o19BeginNode` and `o19BodyHeadNode` respectively.
0 genuineO19BeginBeginExternalProducer :
  (nameEq : DecEq name) ->
  (leftOpening : BeginStep nameEq keyEq leftActor first middle) ->
  (rightOpening : BeginStep nameEq keyEq rightActor middle originalFinal) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    (beginTransition leftOpening) (beginTransition rightOpening)) ->
  SameExternalOrchestration nameEq
    (MoreTransitions (beginTransition leftOpening)
      (MoreTransitions (beginTransition rightOpening) NoTransitions))
    (MoreTransitions (movedRight diamond)
      (MoreTransitions (movedLeft diamond) NoTransitions))
genuineO19BeginBeginExternalProducer nameEq leftOpening rightOpening diamond =
  o19InternalPairExternal nameEq keyEq (beginTransition leftOpening)
    (beginTransition rightOpening) diamond (o19BeginNode leftOpening)
    (o19BeginNode rightOpening)

||| Lookup framing derived only from a genuinely checked foreign transition.
||| This is the operational fact needed for state-sensitive root retire/remove;
||| it is not caller-selected registry equality.
0 checkedForeignLookupR18 :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  {before, afterState : SystemState name key value world error} ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  Not (selected = actionOwner action) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} selected (registry afterState) =
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} selected (registry before)
checkedForeignLookupR18 nameEq keyEq selected {before} {afterState} action tag
  checked distinct =
    let raw = checkedActionProjects nameEq keyEq action before afterState tag
          checked
        update = applyActionLocalUpdate nameEq keyEq action before afterState tag
          raw
    in systemLocalUpdateForeign nameEq selected (actionOwner action) distinct
      before afterState update

||| Stable internal/root case. The source internal transition is checked with
||| the outer dictionaries. Root O-Insert transports by action equality;
||| Root O-Retire and O-Remove transport their exact fiber and Root parent across
||| the checked foreign transition via `checkedForeignLookupR18`.
0 movedRootAfterCheckedSourceForeign :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal, movedFinal :
    SystemState name key value world error} ->
  (foreignAction : Action name key value world error) ->
  (foreignTag : RuleTag) ->
  (foreignChecked : checkedApplyAction @{nameEq} @{keyEq} foreignAction first =
    Just (foreignTag, middle)) ->
  (rootSource : Transition middle originalFinal) ->
  (movedRoot : Transition first movedFinal) ->
  Not (actionOwner (transitionAction rootSource) =
    actionOwner foreignAction) ->
  RootOrchestrationStep nameEq rootSource ->
  transitionAction movedRoot = transitionAction rootSource ->
  RootOrchestrationStep nameEq movedRoot
movedRootAfterCheckedSourceForeign nameEq keyEq foreignAction foreignTag
  foreignChecked rootSource movedRoot distinct
  (RootInsertStep sourceAction) movedAction =
    RootInsertStep (trans movedAction sourceAction)
movedRootAfterCheckedSourceForeign nameEq keyEq foreignAction foreignTag
  foreignChecked rootSource movedRoot distinct
  (RootRetireStep {n} fiber sourceFound rootParent sourceAction) movedAction =
    let notForeign : Not (n = actionOwner foreignAction)
        notForeign same = distinct
          (trans (cong actionOwner sourceAction) same)
        0 lookupFrame : lookupFiber @{nameEq} {key = key} {value = value}
          {world = world} {error = error} n (registry middle) =
          lookupFiber @{nameEq} {key = key} {value = value} {world = world}
            {error = error} n (registry first)
        lookupFrame = checkedForeignLookupR18 nameEq keyEq n
          {before = first} {afterState = middle} foreignAction foreignTag
          foreignChecked notForeign
        0 movedFound : lookupFiber @{nameEq} {key = key} {value = value}
          {world = world} {error = error} n (registry first) = Just fiber
        movedFound = trans (sym lookupFrame) sourceFound
    in RootRetireStep {nameEq = nameEq} {transition = movedRoot} {n = n} fiber movedFound
         rootParent
         (trans movedAction sourceAction)
movedRootAfterCheckedSourceForeign nameEq keyEq foreignAction foreignTag
  foreignChecked rootSource movedRoot distinct
  (RootRemoveStep {n} fiber sourceFound rootParent sourceAction) movedAction =
    let notForeign : Not (n = actionOwner foreignAction)
        notForeign same = distinct
          (trans (cong actionOwner sourceAction) same)
        0 lookupFrame : lookupFiber @{nameEq} {key = key} {value = value}
          {world = world} {error = error} n (registry middle) =
          lookupFiber @{nameEq} {key = key} {value = value} {world = world}
            {error = error} n (registry first)
        lookupFrame = checkedForeignLookupR18 nameEq keyEq n
          {before = first} {afterState = middle} foreignAction foreignTag
          foreignChecked notForeign
        0 movedFound : lookupFiber @{nameEq} {key = key} {value = value}
          {world = world} {error = error} n (registry first) = Just fiber
        movedFound = trans (sym lookupFrame) sourceFound
    in RootRemoveStep {nameEq = nameEq} {transition = movedRoot} {n = n} fiber movedFound
         rootParent
         (trans movedAction sourceAction)

record R18AlignedHeadView
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {before, afterState, finalState : SystemState name key value world error}
  (transition : Transition before afterState)
  (rest : Transitions afterState finalState) where
  constructor MkR18AlignedHeadView
  r18AlignedAction : Action name key value world error
  r18AlignedTag : RuleTag
  0 r18AlignedChecked : checkedApplyAction @{nameEq} @{keyEq}
    r18AlignedAction before = Just (r18AlignedTag, afterState)
  0 r18AlignedActionProjection : transitionAction transition = r18AlignedAction

0 r18AlignedHeadView :
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions transition rest) ->
  R18AlignedHeadView name key world error value nameEq keyEq transition rest
r18AlignedHeadView (AlignedStep action tag checked rest alignedRest) =
  MkR18AlignedHeadView action tag checked Refl

||| Stable root/internal case. Here the genuine early moved internal transition
||| is aligned with the outer dictionaries. The same checked framing preserves a
||| source root fiber into the moved-left source state; the Retire and Remove
||| branches below therefore derive, rather than assume, their moved root proof.
0 movedRootAfterAlignedMovedForeign :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (rootSource : Transition first middle) ->
  (foreignSource : Transition middle originalFinal) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    rootSource foreignSource) ->
  (0 movedAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions (movedRight diamond) NoTransitions)) ->
  Not (actionOwner (transitionAction rootSource) =
    actionOwner (transitionAction foreignSource)) ->
  RootOrchestrationStep nameEq rootSource ->
  RootOrchestrationStep nameEq (movedLeft diamond)
movedRootAfterAlignedMovedForeign nameEq keyEq rootSource foreignSource diamond
  movedAligned distinct root =
    let view = r18AlignedHeadView movedAligned
        movedAction : Action name key value world error
        movedAction = r18AlignedAction view
        movedTag : RuleTag
        movedTag = r18AlignedTag view
        0 movedChecked : checkedApplyAction @{nameEq} @{keyEq} movedAction
          first = Just (movedTag, swappedMiddle diamond)
        movedChecked = r18AlignedChecked view
        0 movedProjection : transitionAction (movedRight diamond) = movedAction
        movedProjection = r18AlignedActionProjection view
        notForeign : Not (actionOwner (transitionAction rootSource) =
          actionOwner movedAction)
        notForeign same = distinct
          (trans same
            (trans (sym (cong actionOwner movedProjection))
              (cong actionOwner (movedRightAction diamond))))
    in case root of
      RootInsertStep sourceAction =>
        RootInsertStep (trans (movedLeftAction diamond) sourceAction)
      RootRetireStep {n} fiber sourceFound rootParent sourceAction =>
        let notSelected : Not (n = actionOwner movedAction)
            notSelected same = notForeign
              (trans (cong actionOwner sourceAction) same)
            0 lookupFrame : lookupFiber @{nameEq} {key = key} {value = value}
              {world = world} {error = error} n
              (registry (swappedMiddle diamond)) =
              lookupFiber @{nameEq} {key = key} {value = value} {world = world}
                {error = error} n (registry first)
            lookupFrame = checkedForeignLookupR18 nameEq keyEq n
              {before = first} {afterState = swappedMiddle diamond} movedAction
              movedTag movedChecked notSelected
            0 movedFound : lookupFiber @{nameEq} {key = key} {value = value}
              {world = world} {error = error} n
              (registry (swappedMiddle diamond)) = Just fiber
            movedFound = trans lookupFrame sourceFound
        in RootRetireStep {nameEq = nameEq} {transition = movedLeft diamond} {n = n} fiber
             movedFound rootParent
             (trans (movedLeftAction diamond) sourceAction)
      RootRemoveStep {n} fiber sourceFound rootParent sourceAction =>
        let notSelected : Not (n = actionOwner movedAction)
            notSelected same = notForeign
              (trans (cong actionOwner sourceAction) same)
            0 lookupFrame : lookupFiber @{nameEq} {key = key} {value = value}
              {world = world} {error = error} n
              (registry (swappedMiddle diamond)) =
              lookupFiber @{nameEq} {key = key} {value = value} {world = world}
                {error = error} n (registry first)
            lookupFrame = checkedForeignLookupR18 nameEq keyEq n
              {before = first} {afterState = swappedMiddle diamond} movedAction
              movedTag movedChecked notSelected
            0 movedFound : lookupFiber @{nameEq} {key = key} {value = value}
              {world = world} {error = error} n
              (registry (swappedMiddle diamond)) = Just fiber
            movedFound = trans lookupFrame sourceFound
        in RootRemoveStep {nameEq = nameEq} {transition = movedLeft diamond} {n = n} fiber
             movedFound rootParent
             (trans (movedLeftAction diamond) sourceAction)

||| O17 stable internal/root producer. Alignment of the selected source pair is
||| projected from the replay bundle; no dictionary identity is assumed.
0 genuineO17InternalRootExternalProducer :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  (0 sourceAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  O19BlockNode internalActor left ->
  RootOrchestrationStep nameEq right ->
  Not (actionOwner (transitionAction right) =
    actionOwner (transitionAction left)) ->
  SameExternalOrchestration nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions (movedRight diamond)
      (MoreTransitions (movedLeft diamond) NoTransitions))
genuineO17InternalRootExternalProducer nameEq keyEq left right diamond
  sourceAligned leftNode rightRoot distinct =
    let view = r18AlignedHeadView sourceAligned
        leftAction : Action name key value world error
        leftAction = r18AlignedAction view
        leftTag : RuleTag
        leftTag = r18AlignedTag view
        0 leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first =
          Just (leftTag, middle)
        leftChecked = r18AlignedChecked view
        0 leftProjection : transitionAction left = leftAction
        leftProjection = r18AlignedActionProjection view
        rootNotLeft : Not (actionOwner (transitionAction right) =
          actionOwner leftAction)
        rootNotLeft same = distinct
          (trans same (sym (cong actionOwner leftProjection)))
        movedRoot : RootOrchestrationStep nameEq (movedRight diamond)
        movedRoot = movedRootAfterCheckedSourceForeign nameEq keyEq leftAction
          leftTag leftChecked right (movedRight diamond) rootNotLeft rightRoot
          (movedRightAction diamond)
        0 movedLeftNode : O19BlockNode internalActor (movedLeft diamond)
        movedLeftNode = movedO19BlockNode leftNode (movedLeftAction diamond)
    in SkipLeftInternal left (MoreTransitions right NoTransitions)
         (o19BlockNodeInternal leftNode)
         (MatchExternalInput (transitionAction right) right NoTransitions
           rightRoot (movedRight diamond)
           (MoreTransitions (movedLeft diamond) NoTransitions) movedRoot Refl
           (movedRightAction diamond)
           (SkipRightInternal (movedLeft diamond) NoTransitions
             (o19BlockNodeInternal movedLeftNode)
             SameExternalOrchestrationEnd))

||| O17 stable root/internal producer. The early moved transition's alignment is
||| exact capital already constructed by each accepted local-diamond producer.
0 genuineO17RootInternalExternalProducer :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  (0 movedAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions (movedRight diamond) NoTransitions)) ->
  RootOrchestrationStep nameEq left ->
  O19BlockNode internalActor right ->
  Not (actionOwner (transitionAction left) =
    actionOwner (transitionAction right)) ->
  SameExternalOrchestration nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions (movedRight diamond)
      (MoreTransitions (movedLeft diamond) NoTransitions))
genuineO17RootInternalExternalProducer nameEq keyEq left right diamond
  movedAligned leftRoot rightNode distinct =
    let movedLeftRoot : RootOrchestrationStep nameEq (movedLeft diamond)
        movedLeftRoot = movedRootAfterAlignedMovedForeign nameEq keyEq left
          right diamond movedAligned distinct leftRoot
        0 movedRightNode : O19BlockNode internalActor (movedRight diamond)
        movedRightNode = movedO19BlockNode rightNode (movedRightAction diamond)
    in SkipRightInternal (movedRight diamond)
         (MoreTransitions (movedLeft diamond) NoTransitions)
         (o19BlockNodeInternal movedRightNode)
         (MatchExternalInput (transitionAction left) left
           (MoreTransitions right NoTransitions) leftRoot
           (movedLeft diamond) NoTransitions movedLeftRoot Refl
           (movedLeftAction diamond)
           (SkipLeftInternal right NoTransitions
             (o19BlockNodeInternal rightNode)
             SameExternalOrchestrationEnd))
