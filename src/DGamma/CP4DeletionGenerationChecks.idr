module DGamma.CP4DeletionGenerationChecks

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Metatheory
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

public export
data ReissueKey = Missing

public export
implementation DecEq ReissueKey where
  decEq Missing Missing = Yes Refl

0 notInEmpty : Not (Elem item [])
notInEmpty elem impossible

0 justInjective : Just left = Just right -> left = right
justInjective Refl = Refl

public export
ReissueValue : ReissueKey -> Type
ReissueValue Missing = Unit

reuseEmptySpec : CoeffectSpec ReissueKey
reuseEmptySpec = MkCoeffectSpec [] UniqueNil

missingSpec : CoeffectSpec ReissueKey
missingSpec = MkCoeffectSpec [Missing] (UniqueCons notInEmpty UniqueNil)

registeringStep : StepEffect ReissueKey ReissueValue Unit String []
  DGamma.CP4DeletionGenerationChecks.reuseEmptySpec
registeringStep = MkStepEffect (Just 0)
  (\NoDepValues, before => Right (before, id))
  (\NoDepValues, before, after, undo, returned, canonical =>
    replace
      {p = \outcome => case outcome of
        Left failure => Unit
        Right (next, inverse) => inverse
          (normalizeLocal DGamma.CP4DeletionGenerationChecks.reuseEmptySpec next) =
          before}
      returned canonical)

selectedComponent : Component ReissueKey ReissueValue Unit String
selectedComponent = MkComponent
  DGamma.CP4DeletionGenerationChecks.reuseEmptySpec
  DGamma.CP4DeletionGenerationChecks.reuseEmptySpec [registeringStep]

childComponent : Component ReissueKey ReissueValue Unit String
childComponent = MkComponent
  DGamma.CP4DeletionGenerationChecks.reuseEmptySpec
  DGamma.CP4DeletionGenerationChecks.reuseEmptySpec []

reissuedRootComponent : Component ReissueKey ReissueValue Unit String
reissuedRootComponent = MkComponent missingSpec
  DGamma.CP4DeletionGenerationChecks.reuseEmptySpec []

initial : SystemState Nat ReissueKey ReissueValue Unit String
initial = MkSystemState () emptyContext

nameEq : DecEq Nat
nameEq = %search

keyEq : DecEq ReissueKey
keyEq = %search

record CheckedAction
  (action : Action Nat ReissueKey ReissueValue Unit String)
  (before : SystemState Nat ReissueKey ReissueValue Unit String) where
  constructor MkCheckedAction
  checkedAfter : SystemState Nat ReissueKey ReissueValue Unit String
  checkedTag : RuleTag
  0 checkedEquation : checkedApplyAction @{DGamma.CP4DeletionGenerationChecks.nameEq}
    @{DGamma.CP4DeletionGenerationChecks.keyEq} action before =
      Just (checkedTag, checkedAfter)
  checkedTransition : Transition before checkedAfter
  0 checkedActionExact : transitionAction checkedTransition = action

checkAction :
  (action : Action Nat ReissueKey ReissueValue Unit String) ->
  (before : SystemState Nat ReissueKey ReissueValue Unit String) ->
  Maybe (CheckedAction action before)
checkAction action before with
  (checkedApplyAction @{DGamma.CP4DeletionGenerationChecks.nameEq}
    @{DGamma.CP4DeletionGenerationChecks.keyEq} action before) proof checked
  checkAction action before | Nothing = Nothing
  checkAction action before | Just (tag, afterState) =
    Just (MkCheckedAction afterState tag checked
      (Fired nameEq keyEq action tag checked) Refl)

public export
record ReissueTrace where
  constructor MkReissueTrace
  insertSelected : CheckedAction
    (OInsert 0 Root DGamma.CP4DeletionGenerationChecks.selectedComponent)
    DGamma.CP4DeletionGenerationChecks.initial
  beginSelected : CheckedAction (LBegin 0) (checkedAfter insertSelected)
  insertChild : CheckedAction
    (OInsert 1 (ChildOf 0) DGamma.CP4DeletionGenerationChecks.childComponent)
    (checkedAfter beginSelected)
  retireChild : CheckedAction (ORetire 1) (checkedAfter insertChild)
  finishSelected : CheckedAction (LAdvance 0) (checkedAfter retireChild)
  retireSelected : CheckedAction (ORetire 0) (checkedAfter finishSelected)
  leaveSelected : CheckedAction (LLeave 0) (checkedAfter retireSelected)
  unloadSelected : CheckedAction (LUnload 0) (checkedAfter leaveSelected)
  removeChild : CheckedAction (ORemove 1) (checkedAfter unloadSelected)
  reissueChildRawName : CheckedAction
    (OInsert 1 Root DGamma.CP4DeletionGenerationChecks.reissuedRootComponent)
    (checkedAfter removeChild)

buildReissueTrace : Maybe ReissueTrace
buildReissueTrace = do
  s0 <- checkAction (OInsert 0 Root selectedComponent) initial
  s1 <- checkAction (LBegin 0) (checkedAfter s0)
  s2 <- checkAction (OInsert 1 (ChildOf 0) childComponent) (checkedAfter s1)
  s3 <- checkAction (ORetire 1) (checkedAfter s2)
  s4 <- checkAction (LAdvance 0) (checkedAfter s3)
  s5 <- checkAction (ORetire 0) (checkedAfter s4)
  s6 <- checkAction (LLeave 0) (checkedAfter s5)
  s7 <- checkAction (LUnload 0) (checkedAfter s6)
  s8 <- checkAction (ORemove 1) (checkedAfter s7)
  s9 <- checkAction (OInsert 1 Root reissuedRootComponent) (checkedAfter s8)
  pure (MkReissueTrace s0 s1 s2 s3 s4 s5 s6 s7 s8 s9)

public export
reissueRuntimeCheck : Bool
reissueRuntimeCheck = case buildReissueTrace of
  Nothing => False
  Just trace =>
    quiet @{DGamma.CP4DeletionGenerationChecks.nameEq}
      @{DGamma.CP4DeletionGenerationChecks.keyEq}
      (checkedAfter (reissueChildRawName trace)) &&
    case lookupFiber @{DGamma.CP4DeletionGenerationChecks.nameEq} 1
      (registry (checkedAfter (reissueChildRawName trace))) of
      Nothing => False
      Just fiber => not (retired fiber)

public export
reissueTrace : (trace : ReissueTrace) ->
  Transitions DGamma.CP4DeletionGenerationChecks.initial
    (checkedAfter (reissueChildRawName trace))
reissueTrace trace =
  MoreTransitions (checkedTransition (insertSelected trace))
  (MoreTransitions (checkedTransition (beginSelected trace))
  (MoreTransitions (checkedTransition (insertChild trace))
  (MoreTransitions (checkedTransition (retireChild trace))
  (MoreTransitions (checkedTransition (finishSelected trace))
  (MoreTransitions (checkedTransition (retireSelected trace))
  (MoreTransitions (checkedTransition (leaveSelected trace))
  (MoreTransitions (checkedTransition (unloadSelected trace))
  (MoreTransitions (checkedTransition (removeChild trace))
  (MoreTransitions (checkedTransition (reissueChildRawName trace))
    NoTransitions)))))))))

oldChildGeneration : RegistrationGeneration Nat
oldChildGeneration = MkRegistrationGeneration 1 2

newChildGeneration : RegistrationGeneration Nat
newChildGeneration = MkRegistrationGeneration 1 9

liveAfterOldChildRemoval : GenerationEnvironment Nat
liveAfterOldChildRemoval = [(0, MkRegistrationGeneration 0 0)]

||| The old raw filter necessarily deletes the later root generation's O-Insert.
public export
0 rawFilterDeletesReissue :
  RegisteredActor [1]
    (OInsert 1 Root DGamma.CP4DeletionGenerationChecks.reissuedRootComponent)
rawFilterDeletesReissue = Here

0 oldGenerationDoesNotOwnReissue :
  GenerationOwnedActor DGamma.CP4DeletionGenerationChecks.nameEq
    [DGamma.CP4DeletionGenerationChecks.oldChildGeneration] 9 DGamma.CP4DeletionGenerationChecks.liveAfterOldChildRemoval
    (OInsert 1 Root DGamma.CP4DeletionGenerationChecks.reissuedRootComponent) ->
  Void
oldGenerationDoesNotOwnReissue (generation ** (stamp, present)) =
  case DGamma.CP4DeletionGenerationChecks.justInjective stamp of
    Refl => oldGenerationNotElem present
  where
  0 oldGenerationNotElem : Not (Elem DGamma.CP4DeletionGenerationChecks.newChildGeneration [DGamma.CP4DeletionGenerationChecks.oldChildGeneration])
  oldGenerationNotElem Here impossible
  oldGenerationNotElem (There later) = absurd later

0 transitionNotOwnedByOldGeneration :
  (step : CheckedAction
    (OInsert 1 Root DGamma.CP4DeletionGenerationChecks.reissuedRootComponent)
    before) ->
  GenerationOwnedActor DGamma.CP4DeletionGenerationChecks.nameEq
    [DGamma.CP4DeletionGenerationChecks.oldChildGeneration] 9 DGamma.CP4DeletionGenerationChecks.liveAfterOldChildRemoval
    (transitionAction (checkedTransition step)) -> Void
transitionNotOwnedByOldGeneration step owned = oldGenerationDoesNotOwnReissue
  (replace
    {p = \action => GenerationOwnedActor
      DGamma.CP4DeletionGenerationChecks.nameEq [DGamma.CP4DeletionGenerationChecks.oldChildGeneration] 9
      DGamma.CP4DeletionGenerationChecks.liveAfterOldChildRemoval action}
    (checkedActionExact step) owned)

||| One-action regression: generation filtering keeps the later O-Insert while
||| the old raw-name `ActionSubsequence` deletes that exact checked transition.
public export
0 generationFilterPreservesReissue : (trace : ReissueTrace) ->
  GenerationActionSubsequence DGamma.CP4DeletionGenerationChecks.nameEq
    (GenerationOwnedActor DGamma.CP4DeletionGenerationChecks.nameEq
      [DGamma.CP4DeletionGenerationChecks.oldChildGeneration])
    9 DGamma.CP4DeletionGenerationChecks.liveAfterOldChildRemoval
    (MoreTransitions (checkedTransition (reissueChildRawName trace))
      NoTransitions)
    (MoreTransitions (checkedTransition (reissueChildRawName trace))
      NoTransitions)
generationFilterPreservesReissue trace =
  KeepGenerationAction
    (checkedTransition (reissueChildRawName trace)) NoTransitions
    (checkedTransition (reissueChildRawName trace)) NoTransitions
    (transitionNotOwnedByOldGeneration (reissueChildRawName trace))
    Refl GenerationActionSubsequenceEnd

public export
0 rawActionSubsequenceDeletesReissue : (trace : ReissueTrace) ->
  ActionSubsequence (RegisteredActor [1])
    (MoreTransitions (checkedTransition (reissueChildRawName trace))
      NoTransitions) NoTransitions
rawActionSubsequenceDeletesReissue trace = DeleteAction
  (checkedTransition (reissueChildRawName trace)) NoTransitions
  (rewrite checkedActionExact (reissueChildRawName trace) in Here)
  ActionSubsequenceEnd
