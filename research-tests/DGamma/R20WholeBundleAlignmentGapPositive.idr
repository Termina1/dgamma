module DGamma.R20WholeBundleAlignmentGapPositive

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4Support
import DGamma.CP4SupportSolution
import DGamma.CP4Lemma70
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R19CrossStateRetireReplayProbePositive
import DGamma.R21MovedOutputAlignmentScopingPositive
import DGamma.R20CorrectedSealedReplayEnvelopeScopingPositive
import Data.Nat
import Decidable.Equality

%default total

public export
data R20Key : Type where

public export
implementation DecEq R20Key where
  decEq key impossible

public export
R20Value : R20Key -> Type
R20Value key impossible

public export
r20Component : Component R20Key R20Value Unit Unit
r20Component = MkComponent emptySpec emptySpec []

public export
r20Protocol : RegistrationProtocol R20Key R20Value Unit Unit
r20Protocol = MkRegistrationProtocol
  (\tag => Nothing)
  (\component => Just Z)
  (\parent, child, step, tag, parentRank, childRank, occurs, parentRanked,
    childRanked, yields, catalog => case catalog of Refl impossible)
  (\provider, consumer, providerRank, consumerRank, providerRanked,
    consumerRanked, key, provided, required => case key of _ impossible)

r20Fiber : Fiber Nat R20Key R20Value Unit Unit
r20Fiber = freshFiber DGamma.R20WholeBundleAlignmentGapPositive.r20Component Root

r20InitialRegistry : Registry Nat R20Key R20Value Unit Unit
r20InitialRegistry = emptyContext

r20PrefixRegistry : Registry Nat R20Key R20Value Unit Unit
r20PrefixRegistry = insertBinding 0 DGamma.R20WholeBundleAlignmentGapPositive.r20Fiber DGamma.R20WholeBundleAlignmentGapPositive.r20InitialRegistry Refl

r20LeftRegistry : Registry Nat R20Key R20Value Unit Unit
r20LeftRegistry = insertBinding 1 DGamma.R20WholeBundleAlignmentGapPositive.r20Fiber DGamma.R20WholeBundleAlignmentGapPositive.r20PrefixRegistry Refl

r20OriginalPairRegistry : Registry Nat R20Key R20Value Unit Unit
r20OriginalPairRegistry = insertBinding 2 DGamma.R20WholeBundleAlignmentGapPositive.r20Fiber DGamma.R20WholeBundleAlignmentGapPositive.r20LeftRegistry Refl

r20EarlyRightRegistry : Registry Nat R20Key R20Value Unit Unit
r20EarlyRightRegistry = insertBinding 2 DGamma.R20WholeBundleAlignmentGapPositive.r20Fiber DGamma.R20WholeBundleAlignmentGapPositive.r20PrefixRegistry Refl

r20SwappedPairRegistry : Registry Nat R20Key R20Value Unit Unit
r20SwappedPairRegistry = insertBinding 1 DGamma.R20WholeBundleAlignmentGapPositive.r20Fiber DGamma.R20WholeBundleAlignmentGapPositive.r20EarlyRightRegistry Refl

r20OriginalFinalRegistry : Registry Nat R20Key R20Value Unit Unit
r20OriginalFinalRegistry = replaceBinding 0 (retireFiber DGamma.R20WholeBundleAlignmentGapPositive.r20Fiber)
  DGamma.R20WholeBundleAlignmentGapPositive.r20OriginalPairRegistry

r20SwappedFinalRegistry : Registry Nat R20Key R20Value Unit Unit
r20SwappedFinalRegistry = replaceBinding 0 (retireFiber DGamma.R20WholeBundleAlignmentGapPositive.r20Fiber)
  DGamma.R20WholeBundleAlignmentGapPositive.r20SwappedPairRegistry

r20Initial : SystemState Nat R20Key R20Value Unit Unit
r20Initial = MkSystemState () DGamma.R20WholeBundleAlignmentGapPositive.r20InitialRegistry

r20PrefixFinal : SystemState Nat R20Key R20Value Unit Unit
r20PrefixFinal = MkSystemState () DGamma.R20WholeBundleAlignmentGapPositive.r20PrefixRegistry

r20LeftFinal : SystemState Nat R20Key R20Value Unit Unit
r20LeftFinal = MkSystemState () DGamma.R20WholeBundleAlignmentGapPositive.r20LeftRegistry

r20OriginalPairFinal : SystemState Nat R20Key R20Value Unit Unit
r20OriginalPairFinal = MkSystemState () DGamma.R20WholeBundleAlignmentGapPositive.r20OriginalPairRegistry

r20EarlyRightFinal : SystemState Nat R20Key R20Value Unit Unit
r20EarlyRightFinal = MkSystemState () DGamma.R20WholeBundleAlignmentGapPositive.r20EarlyRightRegistry

r20SwappedPairFinal : SystemState Nat R20Key R20Value Unit Unit
r20SwappedPairFinal = MkSystemState () DGamma.R20WholeBundleAlignmentGapPositive.r20SwappedPairRegistry

r20OriginalFinal : SystemState Nat R20Key R20Value Unit Unit
r20OriginalFinal = MkSystemState () DGamma.R20WholeBundleAlignmentGapPositive.r20OriginalFinalRegistry

r20SwappedFinal : SystemState Nat R20Key R20Value Unit Unit
r20SwappedFinal = MkSystemState () DGamma.R20WholeBundleAlignmentGapPositive.r20SwappedFinalRegistry

0 r20PrefixChecked : checkedApplyAction @{the (DecEq Nat) %search}
  @{the (DecEq R20Key) %search}
  (OInsert 0 Root DGamma.R20WholeBundleAlignmentGapPositive.r20Component)
  DGamma.R20WholeBundleAlignmentGapPositive.r20Initial =
    Just (OInsertTag, DGamma.R20WholeBundleAlignmentGapPositive.r20PrefixFinal)
r20PrefixChecked = Refl

0 r20LeftChecked : checkedApplyAction @{the (DecEq Nat) %search}
  @{the (DecEq R20Key) %search}
  (OInsert 1 Root DGamma.R20WholeBundleAlignmentGapPositive.r20Component)
  DGamma.R20WholeBundleAlignmentGapPositive.r20PrefixFinal =
    Just (OInsertTag, DGamma.R20WholeBundleAlignmentGapPositive.r20LeftFinal)
r20LeftChecked = Refl

0 r20RightChecked : checkedApplyAction @{the (DecEq Nat) %search}
  @{the (DecEq R20Key) %search}
  (OInsert 2 Root DGamma.R20WholeBundleAlignmentGapPositive.r20Component)
  DGamma.R20WholeBundleAlignmentGapPositive.r20LeftFinal =
    Just (OInsertTag,
      DGamma.R20WholeBundleAlignmentGapPositive.r20OriginalPairFinal)
r20RightChecked = Refl

0 r20EarlyRightChecked : checkedApplyAction @{the (DecEq Nat) %search}
  @{the (DecEq R20Key) %search}
  (OInsert 2 Root DGamma.R20WholeBundleAlignmentGapPositive.r20Component)
  DGamma.R20WholeBundleAlignmentGapPositive.r20PrefixFinal =
    Just (OInsertTag,
      DGamma.R20WholeBundleAlignmentGapPositive.r20EarlyRightFinal)
r20EarlyRightChecked = Refl

0 r20MovedLeftChecked : checkedApplyAction @{the (DecEq Nat) %search}
  @{the (DecEq R20Key) %search}
  (OInsert 1 Root DGamma.R20WholeBundleAlignmentGapPositive.r20Component)
  DGamma.R20WholeBundleAlignmentGapPositive.r20EarlyRightFinal =
    Just (OInsertTag,
      DGamma.R20WholeBundleAlignmentGapPositive.r20SwappedPairFinal)
r20MovedLeftChecked = Refl

0 r20OriginalRetireChecked : checkedApplyAction @{the (DecEq Nat) %search}
  @{the (DecEq R20Key) %search} (ORetire 0)
  DGamma.R20WholeBundleAlignmentGapPositive.r20OriginalPairFinal =
    Just (ORetireTag, DGamma.R20WholeBundleAlignmentGapPositive.r20OriginalFinal)
r20OriginalRetireChecked = Refl

0 r20SwappedRetireChecked : checkedApplyAction @{the (DecEq Nat) %search}
  @{the (DecEq R20Key) %search} (ORetire 0)
  DGamma.R20WholeBundleAlignmentGapPositive.r20SwappedPairFinal =
    Just (ORetireTag, DGamma.R20WholeBundleAlignmentGapPositive.r20SwappedFinal)
r20SwappedRetireChecked = Refl

public export
r20NameEq : DecEq Nat
r20NameEq = %search

public export
r20KeyEq : DecEq R20Key
r20KeyEq = %search

r20PrefixTransition : Transition
  DGamma.R20WholeBundleAlignmentGapPositive.r20Initial
  DGamma.R20WholeBundleAlignmentGapPositive.r20PrefixFinal
r20PrefixTransition = Fired DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq
  (OInsert 0 Root DGamma.R20WholeBundleAlignmentGapPositive.r20Component) OInsertTag DGamma.R20WholeBundleAlignmentGapPositive.r20PrefixChecked

r20LeftTransition : Transition
  DGamma.R20WholeBundleAlignmentGapPositive.r20PrefixFinal
  DGamma.R20WholeBundleAlignmentGapPositive.r20LeftFinal
r20LeftTransition = Fired DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq
  (OInsert 1 Root DGamma.R20WholeBundleAlignmentGapPositive.r20Component) OInsertTag DGamma.R20WholeBundleAlignmentGapPositive.r20LeftChecked

r20RightTransition : Transition
  DGamma.R20WholeBundleAlignmentGapPositive.r20LeftFinal
  DGamma.R20WholeBundleAlignmentGapPositive.r20OriginalPairFinal
r20RightTransition = Fired DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq
  (OInsert 2 Root DGamma.R20WholeBundleAlignmentGapPositive.r20Component) OInsertTag DGamma.R20WholeBundleAlignmentGapPositive.r20RightChecked

r20EarlyRightTransition : Transition
  DGamma.R20WholeBundleAlignmentGapPositive.r20PrefixFinal
  DGamma.R20WholeBundleAlignmentGapPositive.r20EarlyRightFinal
r20EarlyRightTransition = Fired DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq
  (OInsert 2 Root DGamma.R20WholeBundleAlignmentGapPositive.r20Component) OInsertTag DGamma.R20WholeBundleAlignmentGapPositive.r20EarlyRightChecked

r20MovedLeftTransition : Transition
  DGamma.R20WholeBundleAlignmentGapPositive.r20EarlyRightFinal
  DGamma.R20WholeBundleAlignmentGapPositive.r20SwappedPairFinal
r20MovedLeftTransition = Fired DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq
  (OInsert 1 Root DGamma.R20WholeBundleAlignmentGapPositive.r20Component) OInsertTag DGamma.R20WholeBundleAlignmentGapPositive.r20MovedLeftChecked

r20OriginalRetireTransition : Transition
  DGamma.R20WholeBundleAlignmentGapPositive.r20OriginalPairFinal
  DGamma.R20WholeBundleAlignmentGapPositive.r20OriginalFinal
r20OriginalRetireTransition = Fired DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq
  (ORetire 0) ORetireTag DGamma.R20WholeBundleAlignmentGapPositive.r20OriginalRetireChecked

r20SwappedRetireTransition : Transition
  DGamma.R20WholeBundleAlignmentGapPositive.r20SwappedPairFinal
  DGamma.R20WholeBundleAlignmentGapPositive.r20SwappedFinal
r20SwappedRetireTransition = Fired DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq
  (ORetire 0) ORetireTag DGamma.R20WholeBundleAlignmentGapPositive.r20SwappedRetireChecked

0 r20PairAligned : AlignedTransitions Nat R20Key Unit Unit R20Value DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq
  DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq (MoreTransitions DGamma.R20WholeBundleAlignmentGapPositive.r20LeftTransition
    (MoreTransitions DGamma.R20WholeBundleAlignmentGapPositive.r20RightTransition NoTransitions))
r20PairAligned = AlignedStep (OInsert 1 Root DGamma.R20WholeBundleAlignmentGapPositive.r20Component) OInsertTag
  DGamma.R20WholeBundleAlignmentGapPositive.r20LeftChecked (MoreTransitions DGamma.R20WholeBundleAlignmentGapPositive.r20RightTransition NoTransitions)
  (AlignedStep (OInsert 2 Root DGamma.R20WholeBundleAlignmentGapPositive.r20Component) OInsertTag DGamma.R20WholeBundleAlignmentGapPositive.r20RightChecked
    NoTransitions AlignedEnd)

0 r20EarlyRightAligned : AlignedTransitions Nat R20Key Unit Unit R20Value
  DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq (MoreTransitions DGamma.R20WholeBundleAlignmentGapPositive.r20EarlyRightTransition NoTransitions)
r20EarlyRightAligned = AlignedStep (OInsert 2 Root DGamma.R20WholeBundleAlignmentGapPositive.r20Component) OInsertTag
  DGamma.R20WholeBundleAlignmentGapPositive.r20EarlyRightChecked NoTransitions AlignedEnd

0 r20PairDiscipline : RegistrationDiscipline DGamma.R20WholeBundleAlignmentGapPositive.r20Protocol DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq
  (MoreTransitions DGamma.R20WholeBundleAlignmentGapPositive.r20LeftTransition
    (MoreTransitions DGamma.R20WholeBundleAlignmentGapPositive.r20RightTransition NoTransitions))
r20PairDiscipline = RegistrationDisciplineStep DGamma.R20WholeBundleAlignmentGapPositive.r20LeftTransition
  (MoreTransitions DGamma.R20WholeBundleAlignmentGapPositive.r20RightTransition NoTransitions) (Z ** Refl)
  (RegistrationDisciplineStep DGamma.R20WholeBundleAlignmentGapPositive.r20RightTransition NoTransitions (Z ** Refl)
    RegistrationDisciplineEnd)

0 r20PairScan : GenerationTraceScan DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq Z []
  (MoreTransitions DGamma.R20WholeBundleAlignmentGapPositive.r20LeftTransition
    (MoreTransitions DGamma.R20WholeBundleAlignmentGapPositive.r20RightTransition NoTransitions))
  (S (S Z))
  (advanceGenerationEnvironment @{DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq} (S Z)
    (transitionAction DGamma.R20WholeBundleAlignmentGapPositive.r20RightTransition)
    (advanceGenerationEnvironment @{DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq} Z
      (transitionAction DGamma.R20WholeBundleAlignmentGapPositive.r20LeftTransition) []))
r20PairScan = GenerationTraceScanStep DGamma.R20WholeBundleAlignmentGapPositive.r20LeftTransition
  (MoreTransitions DGamma.R20WholeBundleAlignmentGapPositive.r20RightTransition NoTransitions)
  (GenerationTraceScanStep DGamma.R20WholeBundleAlignmentGapPositive.r20RightTransition NoTransitions
    GenerationTraceScanEnd)

0 r20InsertedDistinct :
  (leftChild, rightChild : Nat) ->
  (leftParent, rightParent : Parent Nat) ->
  (leftComponent, rightComponent : Component R20Key R20Value Unit Unit) ->
  transitionAction DGamma.R20WholeBundleAlignmentGapPositive.r20LeftTransition =
    OInsert leftChild leftParent leftComponent ->
  transitionAction DGamma.R20WholeBundleAlignmentGapPositive.r20RightTransition =
    OInsert rightChild rightParent rightComponent ->
  Not (leftChild = rightChild)
r20InsertedDistinct leftChild rightChild leftParent rightParent leftComponent
  rightComponent leftSame rightSame = case leftSame of
    Refl => case rightSame of
      Refl => \same => case same of Refl impossible

0 r20NoChildCrossLicense :
  (leftChild, leftParentName, rightChild, rightParentName : Nat) ->
  (leftComponent, rightComponent : Component R20Key R20Value Unit Unit) ->
  transitionAction DGamma.R20WholeBundleAlignmentGapPositive.r20LeftTransition =
    OInsert leftChild (ChildOf leftParentName) leftComponent ->
  transitionAction DGamma.R20WholeBundleAlignmentGapPositive.r20RightTransition =
    OInsert rightChild (ChildOf rightParentName) rightComponent ->
  (Not (leftChild = rightParentName), Not (rightChild = leftParentName))
r20NoChildCrossLicense leftChild leftParentName rightChild rightParentName
  leftComponent rightComponent leftSame rightSame = case leftSame of
    Refl impossible

||| Genuine checked local root/root swap.  The source pair starts after the
||| authenticated prefix insert; the target pair has the opposite registry-list
||| order and is therefore not definitionally the source endpoint.
0 r20Diamond : LocalRelationalDiamond Nat R20Key Unit Unit R20Value DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq
  DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq DGamma.R20WholeBundleAlignmentGapPositive.r20LeftTransition DGamma.R20WholeBundleAlignmentGapPositive.r20RightTransition
r20Diamond =
  let safety : OrchestrationSwapSafety Nat R20Key Unit Unit R20Value DGamma.R20WholeBundleAlignmentGapPositive.r20Protocol
        DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq DGamma.R20WholeBundleAlignmentGapPositive.r20LeftTransition DGamma.R20WholeBundleAlignmentGapPositive.r20RightTransition
      safety = MkOrchestrationSwapSafety DGamma.R20WholeBundleAlignmentGapPositive.r20EarlyRightFinal
        DGamma.R20WholeBundleAlignmentGapPositive.r20EarlyRightTransition Refl Refl DGamma.R20WholeBundleAlignmentGapPositive.r20PairDiscipline Z [] (S (S Z))
        (advanceGenerationEnvironment @{DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq} (S Z)
          (transitionAction DGamma.R20WholeBundleAlignmentGapPositive.r20RightTransition)
          (advanceGenerationEnvironment @{DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq} Z
            (transitionAction DGamma.R20WholeBundleAlignmentGapPositive.r20LeftTransition) []))
        DGamma.R20WholeBundleAlignmentGapPositive.r20PairScan DGamma.R20WholeBundleAlignmentGapPositive.r20InsertedDistinct DGamma.R20WholeBundleAlignmentGapPositive.r20NoChildCrossLicense
  in orchestrationOrchestrationDiamondSpike DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq DGamma.R20WholeBundleAlignmentGapPositive.r20Protocol
    DGamma.R20WholeBundleAlignmentGapPositive.r20LeftTransition DGamma.R20WholeBundleAlignmentGapPositive.r20RightTransition DGamma.R20WholeBundleAlignmentGapPositive.r20PairAligned
    (PaperInsertStep Refl) (PaperInsertStep Refl)
    (\same => case same of Refl impossible) safety DGamma.R20WholeBundleAlignmentGapPositive.r20EarlyRightAligned


0 r20OriginalPairWellFormed :
  registryWellFormed
    @{DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq}
    @{DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq}
    DGamma.R20WholeBundleAlignmentGapPositive.r20OriginalPairFinal = True
r20OriginalPairWellFormed = Refl

||| The authorized cross-state suffix head itself still succeeds.  The stop is
||| later: the exact moved transitions selected by the abstract diamond cannot
||| be aligned to the outer dictionaries needed by the whole bundle.
0 r20CrossRetire : CheckedCrossStateRetireReplay Nat R20Key Unit Unit R20Value
  DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq
  DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq 0
  DGamma.R20WholeBundleAlignmentGapPositive.r20OriginalPairFinal
  DGamma.R20WholeBundleAlignmentGapPositive.r20OriginalFinal
  (swappedFinal DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
  DGamma.R20WholeBundleAlignmentGapPositive.r20OriginalRetireChecked
r20CrossRetire = checkedRetireReplayAcrossLocalSwap
  DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq
  DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq 0
  DGamma.R20WholeBundleAlignmentGapPositive.r20LeftTransition
  DGamma.R20WholeBundleAlignmentGapPositive.r20RightTransition
  DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond
  DGamma.R20WholeBundleAlignmentGapPositive.r20OriginalFinal
  DGamma.R20WholeBundleAlignmentGapPositive.r20OriginalRetireChecked
  DGamma.R20WholeBundleAlignmentGapPositive.r20OriginalPairWellFormed

0 r20CandidateSwappedTrace : Transitions
  DGamma.R20WholeBundleAlignmentGapPositive.r20Initial
  (replayedAfter DGamma.R20WholeBundleAlignmentGapPositive.r20CrossRetire)
r20CandidateSwappedTrace = MoreTransitions
  DGamma.R20WholeBundleAlignmentGapPositive.r20PrefixTransition
  (MoreTransitions
    (movedRight DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
    (MoreTransitions
      (movedLeft DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
      (MoreTransitions
        (replayedTransition
          DGamma.R20WholeBundleAlignmentGapPositive.r20CrossRetire)
        NoTransitions)))

||| Checked diagnostic: any completed whole bundle must first provide alignment
||| for the exact abstract-diamond transitions.  The adjacent result/splice
||| inputs expose no producer for this field.  The companion expected-failure
||| module pins the dictionary mismatch directly.
public export
0 wholeBundleRequiresExactMovedAlignment :
  ReplayInvariantBundle Nat R20Key Unit Unit R20Value
    DGamma.R20WholeBundleAlignmentGapPositive.r20Protocol
    DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq
    DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq
    DGamma.R20WholeBundleAlignmentGapPositive.r20CandidateSwappedTrace ->
  AlignedTransitions Nat R20Key Unit Unit R20Value
    DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq
    DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq
    DGamma.R20WholeBundleAlignmentGapPositive.r20CandidateSwappedTrace
wholeBundleRequiresExactMovedAlignment bundle = replayAligned bundle

||| Revision-21 boundary simulation: use the outer checked equation retained by
||| the cross-state replay producer rather than its legacy unaligned transition
||| projection.  After `movedPairAligned` lands on the O5 result, this is the
||| exact whole target trace consumed by the bundle.
0 r21RetainedRetireTransition : Transition
  (swappedFinal DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
  (replayedAfter DGamma.R20WholeBundleAlignmentGapPositive.r20CrossRetire)
r21RetainedRetireTransition = Fired
  DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq
  DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq
  (ORetire 0) ORetireTag
  (replayedChecked DGamma.R20WholeBundleAlignmentGapPositive.r20CrossRetire)

0 r21RetainedSwappedTrace : Transitions
  DGamma.R20WholeBundleAlignmentGapPositive.r20Initial
  (replayedAfter DGamma.R20WholeBundleAlignmentGapPositive.r20CrossRetire)
r21RetainedSwappedTrace = MoreTransitions
  DGamma.R20WholeBundleAlignmentGapPositive.r20PrefixTransition
  (MoreTransitions
    (movedRight DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
    (MoreTransitions
      (movedLeft DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
      (MoreTransitions
        DGamma.R20WholeBundleAlignmentGapPositive.r21RetainedRetireTransition
        NoTransitions)))

0 r21AppendAligned :
  {leftFirst, leftFinal, rightFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} ->
  {right : Transitions leftFinal rightFinal} ->
  AlignedTransitions name key world error value nameEq keyEq left ->
  AlignedTransitions name key world error value nameEq keyEq right ->
  AlignedTransitions name key world error value nameEq keyEq
    (appendTransitions left right)
r21AppendAligned {left = NoTransitions} AlignedEnd rightAligned = rightAligned
r21AppendAligned
  (AlignedStep action tag checked rest alignedRest) rightAligned =
    AlignedStep action tag checked (appendTransitions rest right)
      (r21AppendAligned alignedRest rightAligned)

||| The first whole-bundle field now closes from the exact proposed O5 output.
||| This argument is not loose replay capital: its type is exactly the erased
||| `movedPairAligned` field indexed by this concrete producer result.
public export
0 r21WholeReplayAlignedAfterRetainedO5 :
  (0 retainedO5Output : AlignedTransitions Nat R20Key Unit Unit R20Value
    DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq
    DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq
    (MoreTransitions
      (movedRight DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
      (MoreTransitions
        (movedLeft DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
        NoTransitions))) ->
  AlignedTransitions Nat R20Key Unit Unit R20Value
    DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq
    DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq
    DGamma.R20WholeBundleAlignmentGapPositive.r21RetainedSwappedTrace
r21WholeReplayAlignedAfterRetainedO5 retainedO5Output =
  AlignedStep
    (OInsert 0 Root DGamma.R20WholeBundleAlignmentGapPositive.r20Component)
    OInsertTag DGamma.R20WholeBundleAlignmentGapPositive.r20PrefixChecked
    (MoreTransitions
      (movedRight DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
      (MoreTransitions
        (movedLeft DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
        (MoreTransitions
          DGamma.R20WholeBundleAlignmentGapPositive.r21RetainedRetireTransition
          NoTransitions)))
    (r21AppendAligned retainedO5Output
      (AlignedStep (ORetire 0) ORetireTag
        (replayedChecked DGamma.R20WholeBundleAlignmentGapPositive.r20CrossRetire)
        NoTransitions AlignedEnd))

0 r21RootStepDisciplineFromAction :
  (action : Action Nat R20Key R20Value Unit Unit) ->
  (actor : Nat) ->
  (before : SystemState Nat R20Key R20Value Unit Unit) ->
  (rest : Transitions afterState finalState) ->
  action = OInsert actor Root DGamma.R20WholeBundleAlignmentGapPositive.r20Component ->
  RegistrationStepDiscipline
    DGamma.R20WholeBundleAlignmentGapPositive.r20Protocol
    DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq action before rest
r21RootStepDisciplineFromAction
  (OInsert actor Root DGamma.R20WholeBundleAlignmentGapPositive.r20Component)
  actor before rest Refl = (Z ** Refl)

0 r21MovedRightRootDiscipline : RegistrationStepDiscipline
  DGamma.R20WholeBundleAlignmentGapPositive.r20Protocol
  DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq
  (transitionAction
    (movedRight DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond))
  DGamma.R20WholeBundleAlignmentGapPositive.r20PrefixFinal
  (MoreTransitions
    (movedLeft DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
    (MoreTransitions
      DGamma.R20WholeBundleAlignmentGapPositive.r21RetainedRetireTransition
      NoTransitions))
r21MovedRightRootDiscipline = r21RootStepDisciplineFromAction
  (transitionAction
    (movedRight DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond))
  2 DGamma.R20WholeBundleAlignmentGapPositive.r20PrefixFinal
  (MoreTransitions
    (movedLeft DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
    (MoreTransitions
      DGamma.R20WholeBundleAlignmentGapPositive.r21RetainedRetireTransition
      NoTransitions))
  (movedRightAction DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)

0 r21MovedLeftRootDiscipline : RegistrationStepDiscipline
  DGamma.R20WholeBundleAlignmentGapPositive.r20Protocol
  DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq
  (transitionAction
    (movedLeft DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond))
  (swappedMiddle DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
  (MoreTransitions
    DGamma.R20WholeBundleAlignmentGapPositive.r21RetainedRetireTransition
    NoTransitions)
r21MovedLeftRootDiscipline = r21RootStepDisciplineFromAction
  (transitionAction
    (movedLeft DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond))
  1 (swappedMiddle DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
  (MoreTransitions
    DGamma.R20WholeBundleAlignmentGapPositive.r21RetainedRetireTransition
    NoTransitions)
  (movedLeftAction DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)

||| The next bundle field also closes independently of dictionary identity.
public export
0 r21WholeReplayDiscipline : RegistrationDiscipline
  DGamma.R20WholeBundleAlignmentGapPositive.r20Protocol
  DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq
  DGamma.R20WholeBundleAlignmentGapPositive.r21RetainedSwappedTrace
r21WholeReplayDiscipline = RegistrationDisciplineStep
  DGamma.R20WholeBundleAlignmentGapPositive.r20PrefixTransition
  (MoreTransitions
    (movedRight DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
    (MoreTransitions
      (movedLeft DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
      (MoreTransitions
        DGamma.R20WholeBundleAlignmentGapPositive.r21RetainedRetireTransition
        NoTransitions)))
  (Z ** Refl)
  (RegistrationDisciplineStep
    (movedRight DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
    (MoreTransitions
      (movedLeft DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
      (MoreTransitions
        DGamma.R20WholeBundleAlignmentGapPositive.r21RetainedRetireTransition
        NoTransitions))
    DGamma.R20WholeBundleAlignmentGapPositive.r21MovedRightRootDiscipline
    (RegistrationDisciplineStep
      (movedLeft DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
      (MoreTransitions
        DGamma.R20WholeBundleAlignmentGapPositive.r21RetainedRetireTransition
        NoTransitions)
      DGamma.R20WholeBundleAlignmentGapPositive.r21MovedLeftRootDiscipline
      (RegistrationDisciplineStep
        DGamma.R20WholeBundleAlignmentGapPositive.r21RetainedRetireTransition
        NoTransitions () RegistrationDisciplineEnd)))

0 r21WholeReplayInitialWellFormed :
  registryWellFormed
    @{DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq}
    @{DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq}
    DGamma.R20WholeBundleAlignmentGapPositive.r20Initial = True
r21WholeReplayInitialWellFormed = Refl

0 r21WholeReplayInitialEmpty :
  bindings (registry DGamma.R20WholeBundleAlignmentGapPositive.r20Initial) = []
r21WholeReplayInitialEmpty = Refl

0 r21WholeReplayFinalWellFormed :
  registryWellFormed
    @{DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq}
    @{DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq}
    (replayedAfter DGamma.R20WholeBundleAlignmentGapPositive.r20CrossRetire) = True
r21WholeReplayFinalWellFormed = replayedWellFormed
  (perStepEndpoint DGamma.R20WholeBundleAlignmentGapPositive.r20CrossRetire)


||| Exact whole-bundle prefix reached after the proposed O5 field is retained.
||| The fields mirror `ReplayInvariantBundle` in declaration order through
||| `replayFinalWellFormed`; no later invariant is accepted.
public export
record R21WholeBundleThroughFinalWellFormed
  (0 retainedO5Output : AlignedTransitions Nat R20Key Unit Unit R20Value
    DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq
    DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq
    (MoreTransitions
      (movedRight DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
      (MoreTransitions
        (movedLeft DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
        NoTransitions))) where
  constructor MkR21WholeBundleThroughFinalWellFormed
  0 throughAligned : AlignedTransitions Nat R20Key Unit Unit R20Value
    DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq
    DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq
    DGamma.R20WholeBundleAlignmentGapPositive.r21RetainedSwappedTrace
  0 throughDiscipline : RegistrationDiscipline
    DGamma.R20WholeBundleAlignmentGapPositive.r20Protocol
    DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq
    DGamma.R20WholeBundleAlignmentGapPositive.r21RetainedSwappedTrace
  0 throughInitialWellFormed : registryWellFormed
    @{DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq}
    @{DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq}
    DGamma.R20WholeBundleAlignmentGapPositive.r20Initial = True
  0 throughInitialEmpty : bindings
    (registry DGamma.R20WholeBundleAlignmentGapPositive.r20Initial) = []
  0 throughFinalWellFormed : registryWellFormed
    @{DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq}
    @{DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq}
    (replayedAfter DGamma.R20WholeBundleAlignmentGapPositive.r20CrossRetire) = True

public export
0 r21WholeBundlePrefixAfterRetainedO5 :
  (0 retainedO5Output : AlignedTransitions Nat R20Key Unit Unit R20Value
    DGamma.R20WholeBundleAlignmentGapPositive.r20NameEq
    DGamma.R20WholeBundleAlignmentGapPositive.r20KeyEq
    (MoreTransitions
      (movedRight DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
      (MoreTransitions
        (movedLeft DGamma.R20WholeBundleAlignmentGapPositive.r20Diamond)
        NoTransitions))) ->
  R21WholeBundleThroughFinalWellFormed retainedO5Output
r21WholeBundlePrefixAfterRetainedO5 retainedO5Output =
  MkR21WholeBundleThroughFinalWellFormed
    (r21WholeReplayAlignedAfterRetainedO5 retainedO5Output)
    DGamma.R20WholeBundleAlignmentGapPositive.r21WholeReplayDiscipline
    DGamma.R20WholeBundleAlignmentGapPositive.r21WholeReplayInitialWellFormed
    DGamma.R20WholeBundleAlignmentGapPositive.r21WholeReplayInitialEmpty
    DGamma.R20WholeBundleAlignmentGapPositive.r21WholeReplayFinalWellFormed
