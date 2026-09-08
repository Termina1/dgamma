module DGamma.CP5O19PaperBranchCompletenessSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignLifecycleDivert
import DGamma.CP4DeletionSelectedForeignLifecycleLeave
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5ConfluenceRankObservationSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5O19PairObservationSpike
import DGamma.CP5O19OriginalBlockClassSpike
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Unloading is absorbing under an ACTUAL own action other than L-Unload.
||| The source lookup owns the exact callback/view/outcome. An insertion at
||| that already-present name contradicts the real insertion plan's absence;
||| all other lifecycle actions are inapplicable, and retirement keeps phase.
export
0 o19UnloadingOwnAction :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) -> (outcome : Maybe error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) fibers =
    Just (MkFiber component parent retiredFlag table (Unloading accumulator view outcome))) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  (applyAction @{nameEq} @{keyEq} action (MkSystemState ambient fibers) = Just (tag, afterState)) ->
  Not (action = LUnload (actionOwner action)) ->
  (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) afterState = True)
o19UnloadingOwnAction nameEq keyEq (OInsert actor newParent newComponent) ambient fibers component parent retiredFlag table accumulator view outcome found tag afterState raw notUnload =
  void (nothingIsNotJust (trans (sym (foreignInsertViewAbsent
    (foreignInsertPlanView nameEq keyEq actor newParent newComponent ambient fibers tag afterState raw))) found))
o19UnloadingOwnAction nameEq keyEq (ORetire actor) ambient fibers component parent retiredFlag table accumulator view outcome found tag afterState raw notUnload =
  replace {p = \state => unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} actor state = True}
    (cong Builtin.snd (justInjective (trans
      (sym (the (applyAction @{nameEq} @{keyEq} (ORetire actor) (MkSystemState ambient fibers) =
        Just (ORetireTag, MkSystemState ambient (replaceBinding @{nameEq} actor
          (MkFiber component parent True table (Unloading accumulator view outcome)) fibers)))
        (rewrite found in Refl))) raw)))
    (rewrite lookupReplacedFiber @{nameEq} actor
      (MkFiber component parent retiredFlag table (Unloading accumulator view outcome))
      (MkFiber component parent True table (Unloading accumulator view outcome)) fibers found in Refl)
o19UnloadingOwnAction nameEq keyEq (ORemove actor) ambient fibers component parent False table accumulator view outcome found tag afterState raw notUnload =
  void (nothingIsNotJust (trans (sym (the (applyAction @{nameEq} @{keyEq} (ORemove actor) (MkSystemState ambient fibers) = Nothing)
    (rewrite found in Refl))) raw))
o19UnloadingOwnAction nameEq keyEq (ORemove actor) ambient fibers component parent True table accumulator view outcome found tag afterState raw notUnload =
  void (nothingIsNotJust (trans (sym (the (applyAction @{nameEq} @{keyEq} (ORemove actor) (MkSystemState ambient fibers) = Nothing)
    (rewrite found in Refl))) raw))
o19UnloadingOwnAction nameEq keyEq (LBegin actor) ambient fibers component parent retiredFlag table accumulator view outcome found tag afterState raw notUnload =
  void (nothingIsNotJust (trans (sym (the (applyAction @{nameEq} @{keyEq} (LBegin actor) (MkSystemState ambient fibers) = Nothing)
    (rewrite found in Refl))) raw))
o19UnloadingOwnAction nameEq keyEq (LAdvance actor) ambient fibers component parent retiredFlag table accumulator view outcome found tag afterState raw notUnload =
  void (nothingIsNotJust (trans (sym (the (applyAction @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState ambient fibers) = Nothing)
    (rewrite found in Refl))) raw))
o19UnloadingOwnAction nameEq keyEq (LDivert actor) ambient fibers component parent retiredFlag table accumulator view outcome found tag afterState raw notUnload =
  void (nothingIsNotJust (trans (sym (the (applyAction @{nameEq} @{keyEq} (LDivert actor) (MkSystemState ambient fibers) = Nothing)
    (rewrite found in Refl))) raw))
o19UnloadingOwnAction nameEq keyEq (LLeave actor) ambient fibers component parent retiredFlag table accumulator view outcome found tag afterState raw notUnload =
  void (nothingIsNotJust (trans (sym (the (applyAction @{nameEq} @{keyEq} (LLeave actor) (MkSystemState ambient fibers) = Nothing)
    (rewrite found in Refl))) raw))
o19UnloadingOwnAction nameEq keyEq (LUnload actor) ambient fibers component parent retiredFlag table accumulator view outcome found tag afterState raw notUnload =
  void (notUnload Refl)

||| Source observation plus real checked local update extends absorption to
||| arbitrary actions. Foreign actions preserve the selected lookup exactly;
||| the own branch uses A1, never an installed-to-paper cast.
export
0 o19UnloadingStepObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (afterState : SystemState name key value world error) ->
  (raw : applyAction @{nameEq} @{keyEq} action (MkSystemState ambient fibers) = Just (tag, afterState)) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected fibers = observed) ->
  (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} selected (MkSystemState ambient fibers) = True) ->
  Not (action = LUnload selected) ->
  (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} selected afterState = True)
o19UnloadingStepObserved nameEq keyEq selected action tag ambient fibers afterState raw Nothing found unloading notUnload =
  void (uninhabited (trans (sym (the (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} selected (MkSystemState ambient fibers) = False)
    (rewrite found in Refl))) unloading))
o19UnloadingStepObserved nameEq keyEq selected action tag ambient fibers afterState raw
  (Just (MkFiber component parent retiredFlag table (Inactive outcome))) found unloading notUnload =
  void (uninhabited (trans (sym (the (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} selected (MkSystemState ambient fibers) = False)
    (rewrite found in Refl))) unloading))
o19UnloadingStepObserved nameEq keyEq selected action tag ambient fibers afterState raw
  (Just (MkFiber component parent retiredFlag table (Reloading remaining accumulator view))) found unloading notUnload =
  void (uninhabited (trans (sym (the (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} selected (MkSystemState ambient fibers) = False)
    (rewrite found in Refl))) unloading))
o19UnloadingStepObserved nameEq keyEq selected action tag ambient fibers afterState raw
  (Just (MkFiber component parent retiredFlag table (Active accumulator view))) found unloading notUnload =
  void (uninhabited (trans (sym (the (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} selected (MkSystemState ambient fibers) = False)
    (rewrite found in Refl))) unloading))
o19UnloadingStepObserved nameEq keyEq selected action tag ambient fibers afterState raw
  (Just (MkFiber component parent retiredFlag table (Unloading accumulator view outcome))) found unloading notUnload =
  case decEq @{nameEq} selected (actionOwner action) of
    Yes Refl => o19UnloadingOwnAction nameEq keyEq action ambient fibers component parent retiredFlag table accumulator view outcome found tag afterState raw notUnload
    No distinct => rewrite systemLocalUpdateForeign nameEq selected (actionOwner action) distinct
      (MkSystemState ambient fibers) afterState (applyActionLocalUpdate nameEq keyEq action (MkSystemState ambient fibers) afterState tag raw) in
        rewrite found in Refl

||| Actual aligned no-unload evolution: once Unloading, every remaining cut
||| including the endpoint is Unloading. No assumption about installed being
||| a paper activation is made anywhere in this induction.
export
0 o19UnloadingTrace :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  NoParentUnload selected trace ->
  (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} selected first = True) ->
  (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} selected finalState = True)
o19UnloadingTrace nameEq keyEq selected _ AlignedEnd NoParentUnloadEnd unloading = unloading
o19UnloadingTrace {first = MkSystemState ambient fibers} nameEq keyEq selected _
  (AlignedStep action tag checked rest alignedTail) (NoParentUnloadStep _ _ excluded tail) unloading =
    o19UnloadingTrace nameEq keyEq selected rest alignedTail tail
      (o19UnloadingStepObserved nameEq keyEq selected action tag ambient fibers _
        (checkedActionProjects nameEq keyEq action (MkSystemState ambient fibers) _ tag checked)
        (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected fibers) Refl unloading excluded)

||| An actual final-active observation excludes Unloading at that same cut.
||| Together with A3 this rules out recovery branches anywhere in a no-unload
||| suffix, rather than mistaking installation for paper-rule completeness.
export
0 o19ActiveNotUnloadingObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) -> (state : SystemState name key value world error) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry state) = observed) ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected state = True) ->
  (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} selected state = False)
o19ActiveNotUnloadingObserved nameEq selected state Nothing found active = rewrite found in Refl
o19ActiveNotUnloadingObserved nameEq selected state
  (Just (MkFiber component parent retiredFlag table (Inactive outcome))) found active = rewrite found in Refl
o19ActiveNotUnloadingObserved nameEq selected state
  (Just (MkFiber component parent retiredFlag table (Reloading remaining accumulator view))) found active = rewrite found in Refl
o19ActiveNotUnloadingObserved nameEq selected state
  (Just (MkFiber component parent retiredFlag table (Active accumulator view))) found active = rewrite found in Refl
o19ActiveNotUnloadingObserved nameEq selected state
  (Just (MkFiber component parent retiredFlag table (Unloading accumulator view outcome))) found active =
    void (uninhabited (trans (sym (the (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected state = False)
      (rewrite found in Refl))) active))

||| Prepend an actual no-lifecycle segment to a no-unload suffix. This will
||| account for BOTH outside-block segments, not merely the installed body.
export
0 o19NoLifecyclePrependNoUnload :
  {name, key, world, error : Type} -> {value : key -> Type} -> (selected : name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (earlier : Transitions first middle) -> (later : Transitions middle finalState) ->
  NoLifecycleBy selected earlier -> NoParentUnload selected later ->
  NoParentUnload selected (appendTransitions earlier later)
o19NoLifecyclePrependNoUnload selected _ later NoLifecycleByEnd noUnload = noUnload
o19NoLifecyclePrependNoUnload selected _ later (NoLifecycleByStep step rest excluded tail) noUnload =
  NoParentUnloadStep step (appendTransitions rest later)
    (\same => excluded (trans (cong isLifecycleAction same) Refl)
      (trans (o19TransitionActorOwner step) (cong actionOwner same)))
    (o19NoLifecyclePrependNoUnload selected rest later tail noUnload)

||| Every installed boundary is real: L-Unload would make its target false,
||| contradicting the actual next InstalledTrace constructor. Prepend the
||| whole body while retaining an arbitrary already-certified later segment.
export
0 o19InstalledPrependNoUnload :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (earlier : Transitions first middle) -> (later : Transitions middle finalState) ->
  InstalledTrace name key world error value nameEq keyEq selected earlier -> NoParentUnload selected later ->
  NoParentUnload selected (appendTransitions earlier later)
o19InstalledPrependNoUnload nameEq keyEq selected _ later (InstalledEnd installed) noUnload = noUnload
o19InstalledPrependNoUnload nameEq keyEq selected _ later
  (InstalledStep {first = before} {middle = afterState} action tag checked rest installed tail) noUnload =
    NoParentUnloadStep (Fired nameEq keyEq action tag checked) (appendTransitions rest later)
      (\same => case same of
        Refl => uninhabited (trans
          (sym (snd (snd (lUnloadBoundary nameEq keyEq selected before afterState tag
            (checkedActionProjects nameEq keyEq (LUnload selected) before afterState tag checked)))))
          (installedTraceStart tail)))
      (o19InstalledPrependNoUnload nameEq keyEq selected rest later tail noUnload)

||| The complete original source contains NO selected L-Unload: the exact
||| opening is Begin, the body is installed at every cut, and both outside
||| segments have no selected lifecycle action. No extra O19 premise.
export
0 o19OriginalBlockNoUnload :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected source) ->
  NoParentUnload selected source
o19OriginalBlockNoUnload nameEq keyEq selected source block =
  replace {p = NoParentUnload selected} (blockDecomposition block)
    (o19NoLifecyclePrependNoUnload selected (traceBeforeBlock block)
      (MoreTransitions (beginTransition (blockOpening block)) (appendTransitions (blockBody block) (traceAfterBlock block)))
      (noEarlierLifecycle block)
      (NoParentUnloadStep (beginTransition (blockOpening block)) (appendTransitions (blockBody block) (traceAfterBlock block))
        (\same => case same of Refl impossible)
        (o19InstalledPrependNoUnload nameEq keyEq selected (blockBody block) (traceAfterBlock block) (blockBodyInstalled block)
          (replace {p = NoParentUnload selected}
            (currentBirthTraceAppendEmpty name key world error value (traceAfterBlock block))
            (o19NoLifecyclePrependNoUnload selected (traceAfterBlock block) NoTransitions (noLaterLifecycle block) NoParentUnloadEnd)))))

||| An explicit ACTUAL AdvanceStructure leaves exactly Iter and Finish when
||| the reached cut cannot be Unloading. The rejected Divert/Raise branches
||| use their genuine endpoint fact; the callback payload is never recast.
export
0 o19PaperAdvanceNoUnloading :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance selected) before = Just (tag, afterState)) ->
  Not (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} selected afterState = True) ->
  AdvanceStructure name key world error value nameEq keyEq selected tag before afterState ->
  PaperActivationStep (Fired {before} {afterState} nameEq keyEq (LAdvance selected) tag checked)
o19PaperAdvanceNoUnloading nameEq keyEq selected before afterState _ checked excluded
  (IterAdvance fiber found payload reloading) = PaperIterStep Refl Refl
o19PaperAdvanceNoUnloading nameEq keyEq selected before afterState _ checked excluded
  (FinishAdvance fiber found payload active) = PaperFinishStep Refl Refl
o19PaperAdvanceNoUnloading nameEq keyEq selected before afterState _ checked excluded
  (DivertAdvance unloading) = void (excluded unloading)
o19PaperAdvanceNoUnloading nameEq keyEq selected before afterState _ checked excluded
  (RaiseAdvance unloading) = void (excluded unloading)

||| Classify the real checked lifecycle action when it neither unloads nor
||| reaches Unloading. Begin's actual tag and Advance's actual branch are
||| produced; Divert/Leave are contradicted by their exact producer-owned
||| endpoint equations. These two exclusions are discharged from a block below.
export
0 o19LifecyclePaperChecked :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  (isLifecycleAction action = True) -> Not (action = LUnload (actionOwner action)) ->
  Not (unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) afterState = True) ->
  PaperActivationStep (Fired {before} {afterState} nameEq keyEq action tag checked)
o19LifecyclePaperChecked nameEq keyEq (OInsert actor parent component) tag before afterState checked lifecycle excluded notUnloading = void (uninhabited lifecycle)
o19LifecyclePaperChecked nameEq keyEq (ORetire actor) tag before afterState checked lifecycle excluded notUnloading = void (uninhabited lifecycle)
o19LifecyclePaperChecked nameEq keyEq (ORemove actor) tag before afterState checked lifecycle excluded notUnloading = void (uninhabited lifecycle)
o19LifecyclePaperChecked nameEq keyEq (LBegin actor) tag before afterState checked lifecycle excluded notUnloading =
  PaperBeginStep Refl (fst (lBeginBoundary nameEq keyEq actor before afterState tag checked))
o19LifecyclePaperChecked nameEq keyEq (LAdvance actor) tag before afterState checked lifecycle excluded notUnloading =
  o19PaperAdvanceNoUnloading nameEq keyEq actor before afterState tag checked notUnloading
    (advanceStructureTheorem nameEq keyEq actor before afterState tag
      (checkedActionProjects nameEq keyEq (LAdvance actor) before afterState tag checked))
o19LifecyclePaperChecked nameEq keyEq (LDivert actor) tag (MkSystemState ambient fibers) afterState checked lifecycle excluded notUnloading =
  void (notUnloading (divertUnloading (abortDivertStructureTheorem nameEq keyEq actor (MkSystemState ambient fibers) afterState
    (replace {p = \observedTag => applyAction @{nameEq} @{keyEq} (LDivert actor) (MkSystemState ambient fibers) = Just (observedTag, afterState)}
      (foreignDivertPlanViewTag (divertPlanView (foreignDivertPlanView nameEq keyEq actor ambient fibers tag afterState (checkedActionProjects nameEq keyEq (LDivert actor) (MkSystemState ambient fibers) afterState tag checked)))) (checkedActionProjects nameEq keyEq (LDivert actor) (MkSystemState ambient fibers) afterState tag checked)))))
o19LifecyclePaperChecked nameEq keyEq (LLeave actor) tag (MkSystemState ambient fibers) afterState checked lifecycle excluded notUnloading =
  void (notUnloading
    (replace {p = \state => unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} actor state = True}
      (leaveReplayAfterShape (foreignLeaveReplayData (leavePlanView (foreignLeavePlanView nameEq keyEq actor ambient fibers tag afterState (checkedActionProjects nameEq keyEq (LLeave actor) (MkSystemState ambient fibers) afterState tag checked)))))
      (rewrite lookupReplacedFiber @{nameEq} actor
        (MkFiber (leaveReplayComponent (foreignLeaveReplayData (leavePlanView (foreignLeavePlanView nameEq keyEq actor ambient fibers tag afterState (checkedActionProjects nameEq keyEq (LLeave actor) (MkSystemState ambient fibers) afterState tag checked))))) (leaveReplayParent (foreignLeaveReplayData (leavePlanView (foreignLeavePlanView nameEq keyEq actor ambient fibers tag afterState (checkedActionProjects nameEq keyEq (LLeave actor) (MkSystemState ambient fibers) afterState tag checked))))) (leaveReplayRetired (foreignLeaveReplayData (leavePlanView (foreignLeavePlanView nameEq keyEq actor ambient fibers tag afterState (checkedActionProjects nameEq keyEq (LLeave actor) (MkSystemState ambient fibers) afterState tag checked))))) (leaveReplayTable (foreignLeaveReplayData (leavePlanView (foreignLeavePlanView nameEq keyEq actor ambient fibers tag afterState (checkedActionProjects nameEq keyEq (LLeave actor) (MkSystemState ambient fibers) afterState tag checked))))) (Active (leaveReplayAccumulator (foreignLeaveReplayData (leavePlanView (foreignLeavePlanView nameEq keyEq actor ambient fibers tag afterState (checkedActionProjects nameEq keyEq (LLeave actor) (MkSystemState ambient fibers) afterState tag checked))))) (leaveReplayView (foreignLeaveReplayData (leavePlanView (foreignLeavePlanView nameEq keyEq actor ambient fibers tag afterState (checkedActionProjects nameEq keyEq (LLeave actor) (MkSystemState ambient fibers) afterState tag checked)))))))
        (MkFiber (leaveReplayComponent (foreignLeaveReplayData (leavePlanView (foreignLeavePlanView nameEq keyEq actor ambient fibers tag afterState (checkedActionProjects nameEq keyEq (LLeave actor) (MkSystemState ambient fibers) afterState tag checked))))) (leaveReplayParent (foreignLeaveReplayData (leavePlanView (foreignLeavePlanView nameEq keyEq actor ambient fibers tag afterState (checkedActionProjects nameEq keyEq (LLeave actor) (MkSystemState ambient fibers) afterState tag checked))))) (leaveReplayRetired (foreignLeaveReplayData (leavePlanView (foreignLeavePlanView nameEq keyEq actor ambient fibers tag afterState (checkedActionProjects nameEq keyEq (LLeave actor) (MkSystemState ambient fibers) afterState tag checked))))) (leaveReplayTable (foreignLeaveReplayData (leavePlanView (foreignLeavePlanView nameEq keyEq actor ambient fibers tag afterState (checkedActionProjects nameEq keyEq (LLeave actor) (MkSystemState ambient fibers) afterState tag checked))))) (Unloading (leaveReplayAccumulator (foreignLeaveReplayData (leavePlanView (foreignLeavePlanView nameEq keyEq actor ambient fibers tag afterState (checkedActionProjects nameEq keyEq (LLeave actor) (MkSystemState ambient fibers) afterState tag checked))))) (leaveReplayView (foreignLeaveReplayData (leavePlanView (foreignLeavePlanView nameEq keyEq actor ambient fibers tag afterState (checkedActionProjects nameEq keyEq (LLeave actor) (MkSystemState ambient fibers) afterState tag checked))))) Nothing))
        fibers (trans (leavePlanOwnerFound (foreignLeavePlanView nameEq keyEq actor ambient fibers tag afterState (checkedActionProjects nameEq keyEq (LLeave actor) (MkSystemState ambient fibers) afterState tag checked))) (cong Just (leaveReplayOwnerShape (foreignLeaveReplayData (leavePlanView (foreignLeavePlanView nameEq keyEq actor ambient fibers tag afterState (checkedActionProjects nameEq keyEq (LLeave actor) (MkSystemState ambient fibers) afterState tag checked))))))) in Refl)))
o19LifecyclePaperChecked nameEq keyEq (LUnload actor) tag before afterState checked lifecycle excluded notUnloading = void (excluded Refl)

||| Extract both actual no-unload facts at a dependent source cut: the
||| selected transition cannot unload, and its entire actual suffix cannot.
||| The structural earlier spine identifies this occurrence, not its label.
export
0 o19NoUnloadAtCut :
  {name, key, world, error : Type} -> {value : key -> Type} -> (selected : name) ->
  {initial, before, afterState, finalState : SystemState name key value world error} ->
  (earlier : Transitions initial before) -> (step : Transition before afterState) -> (later : Transitions afterState finalState) ->
  NoParentUnload selected (appendTransitions earlier (MoreTransitions step later)) ->
  (Not (transitionAction step = LUnload selected), NoParentUnload selected later)
o19NoUnloadAtCut selected NoTransitions step later (NoParentUnloadStep _ _ excluded tail) = (excluded, tail)
o19NoUnloadAtCut selected (MoreTransitions head rest) step later (NoParentUnloadStep _ _ excluded tail) =
  o19NoUnloadAtCut selected rest step later tail

||| ORIGINAL paper-branch completeness for an actual block-owned lifecycle
||| occurrence. The two actual block boundaries plus no-earlier/no-later give
||| whole-source no-unload; its actual suffix would carry any Unloading output
||| to the final-active endpoint, contradiction. The explicit alignment is a
||| projection of the original bundle at this exact dependent cut.
export
0 o19OriginalPaperBranch :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected, forbidden : name) ->
  {initial, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected source) ->
  {action : Action name key value world error} ->
  (origin : LocatedActionOccurrence action source) ->
  O19BlockWordObservation name key world error value selected forbidden action ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions (locatedTransition origin) (afterActionOccurrence origin)) ->
  (isLifecycleAction action = True) -> PaperActivationStep (locatedTransition origin)
o19OriginalPaperBranch {finalState} nameEq keyEq selected forbidden source block
  (MkLocatedActionOccurrence before afterState earlier _ later actionExact decomposition)
  (BlockOwnLifecycle ownLifecycle owner) (AlignedStep checkedAction tag checked _ alignedTail) lifecycle =
    o19LifecyclePaperChecked nameEq keyEq checkedAction tag before afterState checked
      (trans (cong isLifecycleAction actionExact) lifecycle)
      (\same => fst (o19NoUnloadAtCut selected earlier (Fired nameEq keyEq checkedAction tag checked) later
        (replace {p = NoParentUnload selected} (sym decomposition)
          (o19OriginalBlockNoUnload nameEq keyEq selected source block)))
        (trans same (cong LUnload (trans (cong actionOwner actionExact) owner))))
      (\unloading => uninhabited (trans
        (sym (o19ActiveNotUnloadingObserved nameEq selected finalState
          (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry finalState)) Refl (blockActiveAtFinal block)))
        (o19UnloadingTrace nameEq keyEq selected later alignedTail
          (snd (o19NoUnloadAtCut selected earlier (Fired nameEq keyEq checkedAction tag checked) later
            (replace {p = NoParentUnload selected} (sym decomposition)
              (o19OriginalBlockNoUnload nameEq keyEq selected source block))))
          (replace {p = \actor => unloadingEndpoint {name} {key} {value} {world} {error} @{nameEq} actor afterState = True}
            (trans (cong actionOwner actionExact) owner) unloading))))
o19OriginalPaperBranch nameEq keyEq selected forbidden source block origin
  (BlockGenerated child component inserted safe) aligned lifecycle =
    void (uninhabited (trans (sym (trans (cong isLifecycleAction inserted) Refl)) lifecycle))

||| UNCONDITIONAL ORIGINAL four-orientation classifier. Every input is an
||| existing O19 premise or an original location/word membership requested by
||| the approved static interface. Both Conditional paper-branch hypotheses
||| are now PRODUCED from the selected actual block; no paper, future row,
||| reached safety/decomposition, callback, or early-guard oracle remains.
export
0 o19OriginalClasses :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  {leftAction, rightAction : Action name key value world error} ->
  (leftOrigin : LocatedActionOccurrence leftAction source) -> (rightOrigin : LocatedActionOccurrence rightAction source) ->
  Elem leftAction (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ->
  Elem rightAction (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ->
  O19SourcePairObservation name key world error value (actorLeft swap) (actorRight swap)
    (locatedTransition leftOrigin) (locatedTransition rightOrigin)
o19OriginalClasses {leftAction} {rightAction} nameEq keyEq protocol swap source blocks premises safety unique
  leftOrigin rightOrigin leftMember rightMember =
    o19OriginalClassesConditional nameEq keyEq protocol swap source premises unique leftOrigin rightOrigin
      (o19SanctionedOriginalWords nameEq keyEq protocol swap source blocks premises safety leftAction rightAction leftMember rightMember)
      (o19OriginalPaperBranch nameEq keyEq (actorLeft swap) (actorRight swap) source
        (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)) leftOrigin
        (o19OriginalBlockWord (actorLeft swap) (actorRight swap) (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)) (safetyLeftDoesNotGenerateRight safety) leftAction leftMember)
        (snd (alignedAppendSplit (beforeActionOccurrence leftOrigin)
          (MoreTransitions (locatedTransition leftOrigin) (afterActionOccurrence leftOrigin))
          (replace {p = AlignedTransitions name key world error value nameEq keyEq}
            (sym (actionOccurrenceDecomposition leftOrigin)) (replayAligned premises)))))
      (o19OriginalPaperBranch nameEq keyEq (actorRight swap) (actorLeft swap) source
        (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)) rightOrigin
        (o19OriginalBlockWord (actorRight swap) (actorLeft swap) (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)) (safetyRightDoesNotGenerateLeft safety) rightAction rightMember)
        (snd (alignedAppendSplit (beforeActionOccurrence rightOrigin)
          (MoreTransitions (locatedTransition rightOrigin) (afterActionOccurrence rightOrigin))
          (replace {p = AlignedTransitions name key world error value nameEq keyEq}
            (sym (actionOccurrenceDecomposition rightOrigin)) (replayAligned premises)))))
