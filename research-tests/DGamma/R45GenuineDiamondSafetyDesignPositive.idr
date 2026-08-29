module DGamma.R45GenuineDiamondSafetyDesignPositive

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import Decidable.Equality

%default total

||| Test-local candidate for revision 21.  The four constructors retain exactly
||| the branch-local evidence already present where each genuine local diamond
||| is built.  No RegistrationProtocol is stored in this package.
public export
data CandidateRegistrationSwapSafety :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, originalFinal : SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) -> Type where
  CandidateActivationActivation :
    {left : Transition first middle} ->
    {right : Transition middle originalFinal} ->
    PaperActivationStep left ->
    PaperActivationStep right ->
    CandidateRegistrationSwapSafety left right
  CandidateActivationOrchestration :
    {left : Transition first middle} ->
    {right : Transition middle originalFinal} ->
    PaperActivationStep left ->
    PaperOrchestrationStep right ->
    ((child, parent : name) ->
      (component : Component key value world error) ->
      transitionAction right = OInsert child (ChildOf parent) component ->
      Not (transitionActor left = parent)) ->
    CandidateRegistrationSwapSafety left right
  CandidateOrchestrationActivation :
    {left : Transition first middle} ->
    {right : Transition middle originalFinal} ->
    PaperOrchestrationStep left ->
    PaperActivationStep right ->
    ((child : name) -> (parent : Parent name) ->
      (component : Component key value world error) ->
      transitionAction left = OInsert child parent component ->
      Not (transitionActor right = child)) ->
    ((child, parent : name) ->
      (component : Component key value world error) ->
      transitionAction left = OInsert child (ChildOf parent) component ->
      Not (transitionActor right = parent)) ->
    CandidateRegistrationSwapSafety left right
  CandidateOrchestrationOrchestration :
    {left : Transition first middle} ->
    {right : Transition middle originalFinal} ->
    PaperOrchestrationStep left ->
    PaperOrchestrationStep right ->
    ((leftChild, rightChild : name) ->
      (leftParent, rightParent : Parent name) ->
      (leftComponent, rightComponent : Component key value world error) ->
      transitionAction left = OInsert leftChild leftParent leftComponent ->
      transitionAction right = OInsert rightChild rightParent rightComponent ->
      Not (leftChild = rightChild)) ->
    ((leftChild, leftParent, rightChild, rightParent : name) ->
      (leftComponent, rightComponent : Component key value world error) ->
      transitionAction left =
        OInsert leftChild (ChildOf leftParent) leftComponent ->
      transitionAction right =
        OInsert rightChild (ChildOf rightParent) rightComponent ->
      (Not (leftChild = rightParent), Not (rightChild = leftParent))) ->
    CandidateRegistrationSwapSafety left right

||| Negative-direction semantic check for cure (a): the exact field-2
||| counterexample cannot be certified. In the A/O branch its retained
||| parentSafe proof is contradicted by the concrete parent activation; every
||| other classifier contradicts one of the concrete transition actions.
public export
0 candidateSafetyRejectsBareCounterexample :
  CandidateRegistrationSwapSafety
    DGamma.R45BareDiamondDisciplineCounterexamplePositive.r45Begin
    DGamma.R45BareDiamondDisciplineCounterexamplePositive.r45ChildInsert -> Void
candidateSafetyRejectsBareCounterexample
  (CandidateActivationActivation leftPaper rightPaper) =
    r45ActivationOrchestrationImpossible rightPaper (PaperInsertStep Refl)
candidateSafetyRejectsBareCounterexample
  (CandidateActivationOrchestration leftPaper rightPaper parentSafe) =
    parentSafe 1 0 r45Child Refl Refl
candidateSafetyRejectsBareCounterexample
  (CandidateOrchestrationActivation leftPaper rightPaper childSafe parentSafe) =
    r45ActivationOrchestrationImpossible (PaperBeginStep Refl Refl) leftPaper
candidateSafetyRejectsBareCounterexample
  (CandidateOrchestrationOrchestration leftPaper rightPaper insertedDistinct
    licensesDoNotCross) =
      r45ActivationOrchestrationImpossible (PaperBeginStep Refl Refl) leftPaper

||| Candidate richer record for cure (a). In an implementation this package is
||| a single erased field of LocalRelationalDiamond rather than a detached
||| wrapper. The wrapper is used only to check producer coverage without touching
||| the frozen research declaration during this design shift.
public export
record CandidateSafetyRetainedDiamond
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {first, middle, originalFinal : SystemState name key value world error}
  (left : Transition first middle)
  (right : Transition middle originalFinal) where
  constructor MkCandidateSafetyRetainedDiamond
  retainedBase : LocalRelationalDiamond name key world error value nameEq keyEq
    left right
  0 retainedRegistrationSafety : CandidateRegistrationSwapSafety left right

||| Construction-site probe A/A: both branch classifiers are already in scope.
public export
0 retainActivationActivationSafety :
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  PaperActivationStep left ->
  PaperActivationStep right ->
  CandidateSafetyRetainedDiamond name key world error value nameEq keyEq
    left right
retainActivationActivationSafety diamond leftPaper rightPaper =
  MkCandidateSafetyRetainedDiamond diamond
    (CandidateActivationActivation leftPaper rightPaper)

||| Construction-site probe A/O: this is the exact parentSafe premise already
||| required by activationOrchestrationDiamondSpike.
public export
0 retainActivationOrchestrationSafety :
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  PaperActivationStep left ->
  PaperOrchestrationStep right ->
  ((child, parent : name) ->
    (component : Component key value world error) ->
    transitionAction right = OInsert child (ChildOf parent) component ->
    Not (transitionActor left = parent)) ->
  CandidateSafetyRetainedDiamond name key world error value nameEq keyEq
    left right
retainActivationOrchestrationSafety diamond leftPaper rightPaper parentSafe =
  MkCandidateSafetyRetainedDiamond diamond
    (CandidateActivationOrchestration leftPaper rightPaper parentSafe)

||| Construction-site probe O/A: these are the exact childSafe and parentSafe
||| premises already required by orchestrationActivationDiamondSpike.
public export
0 retainOrchestrationActivationSafety :
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  PaperOrchestrationStep left ->
  PaperActivationStep right ->
  ((child : name) -> (parent : Parent name) ->
    (component : Component key value world error) ->
    transitionAction left = OInsert child parent component ->
    Not (transitionActor right = child)) ->
  ((child, parent : name) ->
    (component : Component key value world error) ->
    transitionAction left = OInsert child (ChildOf parent) component ->
    Not (transitionActor right = parent)) ->
  CandidateSafetyRetainedDiamond name key world error value nameEq keyEq
    left right
retainOrchestrationActivationSafety diamond leftPaper rightPaper childSafe
  parentSafe = MkCandidateSafetyRetainedDiamond diamond
    (CandidateOrchestrationActivation leftPaper rightPaper childSafe parentSafe)

||| Construction-site probe O/O: OrchestrationSwapSafety already owns both
||| insertion freshness and cross-license exclusions. The retained candidate is
||| protocol-independent even though the larger producer safety record is not.
public export
0 retainOrchestrationOrchestrationSafety :
  {first, middle, originalFinal : SystemState name key value world error} ->
  {left : Transition first middle} ->
  {right : Transition middle originalFinal} ->
  (protocol : RegistrationProtocol key value world error) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  PaperOrchestrationStep left ->
  PaperOrchestrationStep right ->
  OrchestrationSwapSafety name key world error value protocol nameEq keyEq
    left right ->
  CandidateSafetyRetainedDiamond name key world error value nameEq keyEq
    left right
retainOrchestrationOrchestrationSafety protocol diamond leftPaper rightPaper
  safety = MkCandidateSafetyRetainedDiamond diamond
    (CandidateOrchestrationOrchestration leftPaper rightPaper
      (insertedChildrenDistinct safety) (generatedLicensesDoNotCross safety))

||| Cure-(b) test type. `export record` keeps its constructor private outside
||| this module, as desired for an opaque genuine producer.
export
record CandidateOpaqueGenuineDiamond
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {first, middle, originalFinal : SystemState name key value world error}
  (left : Transition first middle)
  (right : Transition middle originalFinal) where
  constructor MkCandidateOpaqueGenuineDiamond
  sealedBase : LocalRelationalDiamond name key world error value nameEq keyEq
    left right
  0 sealedSafety : CandidateRegistrationSwapSafety left right

public export
0 sealCandidateGenuineDiamond :
  CandidateSafetyRetainedDiamond name key world error value nameEq keyEq
    left right ->
  CandidateOpaqueGenuineDiamond name key world error value nameEq keyEq
    left right
sealCandidateGenuineDiamond
  (MkCandidateSafetyRetainedDiamond diamond safety) =
    MkCandidateOpaqueGenuineDiamond diamond safety

public export
0 revealOpaqueGenuineBase :
  CandidateOpaqueGenuineDiamond name key world error value nameEq keyEq
    left right ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
revealOpaqueGenuineBase (MkCandidateOpaqueGenuineDiamond diamond safety) = diamond

||| Positive half of the cure-(b) anti-oscillation probe. An opaque wrapper can
||| be created, but the byte-frozen adjacent function accepts it only after this
||| projection back to the unsafe bare type. Consequently the function body has
||| no route back to the sealed safety field.
public export
0 frozenAdjacentConsumesOnlyProjectedBare :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
    SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (tracePrefix : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) ->
  (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) ->
  (decomposition : appendTransitions tracePrefix
    (MoreTransitions left (MoreTransitions right suffix)) = original) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq
    keyEq original) ->
  (sealed : CandidateOpaqueGenuineDiamond name key world error value nameEq keyEq
    left right) ->
  (0 pairExternalOrder : SameExternalOrchestration nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions (movedRight (revealOpaqueGenuineBase sealed))
      (MoreTransitions (movedLeft (revealOpaqueGenuineBase sealed))
        NoTransitions))) ->
  AdjacentSwapResult name key world error value protocol nameEq keyEq original
    tracePrefix left right suffix (revealOpaqueGenuineBase sealed)
frozenAdjacentConsumesOnlyProjectedBare nameEq keyEq protocol original tracePrefix
  left right suffix decomposition premises sealed pairExternalOrder =
    adjacentSwapSuffixSpike nameEq keyEq protocol original tracePrefix left right
      suffix decomposition premises (revealOpaqueGenuineBase sealed)
      pairExternalOrder
