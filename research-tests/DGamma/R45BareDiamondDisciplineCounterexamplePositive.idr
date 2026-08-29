module DGamma.R45BareDiamondDisciplineCounterexamplePositive

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Metatheory
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality
import Data.List.Elem
import Data.Maybe
import Data.Nat

%default total
%unbound_implicits off

public export
data R45Key : Type where

public export
implementation DecEq R45Key where
  decEq key impossible

public export
R45Value : R45Key -> Type
R45Value key impossible

public export
r45NameEq : DecEq Nat
r45NameEq = %search

public export
r45KeyEq : DecEq R45Key
r45KeyEq = %search

public export
r45Spec : CoeffectSpec R45Key
r45Spec = MkCoeffectSpec [] UniqueNil

public export
r45Child : Component R45Key R45Value Unit String
r45Child = MkComponent r45Spec r45Spec []

public export
r45YieldingStep : StepEffect R45Key R45Value Unit String [] r45Spec
r45YieldingStep = MkStepEffect (Just 0)
  (\NoDepValues, before => Right (before, id))
  (\NoDepValues, before, after, undo, returned, canonical =>
    replace
      {p = \outcome => case outcome of
        Left _ => Unit
        Right (next, inverse) => inverse (normalizeLocal r45Spec next) = before}
      returned canonical)

public export
r45Parent : Component R45Key R45Value Unit String
r45Parent = MkComponent r45Spec r45Spec [r45YieldingStep]

public export
r45Protocol : RegistrationProtocol R45Key R45Value Unit String
r45Protocol = MkRegistrationProtocol catalog rank yieldRanks precedenceRanks
  where
  catalog : Nat -> Maybe (Component R45Key R45Value Unit String)
  catalog Z = Just r45Child
  catalog (S later) = Nothing

  rank : Component R45Key R45Value Unit String -> Maybe Nat
  rank (MkComponent deps provisions []) = Just 1
  rank (MkComponent deps provisions (step :: rest)) = Just 0

  0 yieldRanks :
    (parent, child : Component R45Key R45Value Unit String) ->
    (step : StepEffect R45Key R45Value Unit String
      (dependencies (componentDependencies parent))
      (componentProvisions parent)) ->
    (tag, parentRank, childRank : Nat) ->
    Elem step (componentProgram parent) ->
    rank parent = Just parentRank ->
    rank child = Just childRank ->
    registrationYieldTag step = Just tag ->
    catalog tag = Just child ->
    LT parentRank childRank
  yieldRanks (MkComponent deps provisions []) child step tag parentRank
    childRank source parentRanked childRanked stepTag cataloged =
      case source of Here impossible; There later impossible
  yieldRanks (MkComponent deps provisions (first :: rest)) child step Z
    parentRank childRank source parentRanked childRanked stepTag cataloged =
      case cataloged of
        Refl => case parentRanked of
          Refl => case childRanked of
            Refl => LTESucc LTEZero
  yieldRanks (MkComponent deps provisions (first :: rest)) child step (S tag)
    parentRank childRank source parentRanked childRanked stepTag cataloged =
      case cataloged of Refl impossible

  0 precedenceRanks :
    (provider, consumer : Component R45Key R45Value Unit String) ->
    (providerRank, consumerRank : Nat) ->
    rank provider = Just providerRank ->
    rank consumer = Just consumerRank ->
    (key : R45Key) ->
    Elem key (dependencies (componentProvisions provider)) ->
    Elem key (dependencies (componentDependencies consumer)) ->
    LT providerRank consumerRank
  precedenceRanks provider consumer providerRank consumerRank providerRanked
    consumerRanked key provides depends impossible

public export
r45ParentFresh : Fiber Nat R45Key R45Value Unit String
r45ParentFresh = freshFiber r45Parent Root

public export
r45ParentBegun : Fiber Nat R45Key R45Value Unit String
r45ParentBegun = setFiberLifecycle r45ParentFresh
  (Reloading [r45YieldingStep] id EmptyView)

public export
r45ChildFresh : Fiber Nat R45Key R45Value Unit String
r45ChildFresh = freshFiber r45Child (ChildOf 0)

public export
r45ChildRetired : Fiber Nat R45Key R45Value Unit String
r45ChildRetired = retireFiber r45ChildFresh

public export
r45InitialRegistry : Registry Nat R45Key R45Value Unit String
r45InitialRegistry = emptyContext

public export
r45AfterParentRegistry : Registry Nat R45Key R45Value Unit String
r45AfterParentRegistry = insertBinding 0 r45ParentFresh r45InitialRegistry Refl

public export
r45AfterBeginRegistry : Registry Nat R45Key R45Value Unit String
r45AfterBeginRegistry = replaceBinding 0 r45ParentBegun r45AfterParentRegistry

public export
r45SourcePairFinalRegistry : Registry Nat R45Key R45Value Unit String
r45SourcePairFinalRegistry = insertBinding 1 r45ChildFresh r45AfterBeginRegistry Refl

public export
r45AfterEarlyChildRegistry : Registry Nat R45Key R45Value Unit String
r45AfterEarlyChildRegistry = insertBinding 1 r45ChildFresh r45AfterParentRegistry Refl

public export
r45TargetPairFinalRegistry : Registry Nat R45Key R45Value Unit String
r45TargetPairFinalRegistry = replaceBinding 0 r45ParentBegun
  r45AfterEarlyChildRegistry

public export
r45SourceFinalRegistry : Registry Nat R45Key R45Value Unit String
r45SourceFinalRegistry = replaceBinding 1 r45ChildRetired
  r45SourcePairFinalRegistry

public export
r45TargetFinalRegistry : Registry Nat R45Key R45Value Unit String
r45TargetFinalRegistry = replaceBinding 1 r45ChildRetired
  r45TargetPairFinalRegistry

public export
r45Initial : SystemState Nat R45Key R45Value Unit String
r45Initial = MkSystemState () r45InitialRegistry

public export
r45AfterParent : SystemState Nat R45Key R45Value Unit String
r45AfterParent = MkSystemState () r45AfterParentRegistry

public export
r45AfterBegin : SystemState Nat R45Key R45Value Unit String
r45AfterBegin = MkSystemState () r45AfterBeginRegistry

public export
r45SourcePairFinal : SystemState Nat R45Key R45Value Unit String
r45SourcePairFinal = MkSystemState () r45SourcePairFinalRegistry

public export
r45AfterEarlyChild : SystemState Nat R45Key R45Value Unit String
r45AfterEarlyChild = MkSystemState () r45AfterEarlyChildRegistry

public export
r45TargetPairFinal : SystemState Nat R45Key R45Value Unit String
r45TargetPairFinal = MkSystemState () r45TargetPairFinalRegistry

public export
r45SourceFinal : SystemState Nat R45Key R45Value Unit String
r45SourceFinal = MkSystemState () r45SourceFinalRegistry

public export
r45TargetFinal : SystemState Nat R45Key R45Value Unit String
r45TargetFinal = MkSystemState () r45TargetFinalRegistry

0 r45ParentInsertRaw : applyAction @{r45NameEq} @{r45KeyEq}
  (OInsert 0 Root r45Parent) r45Initial = Just (OInsertTag, r45AfterParent)
r45ParentInsertRaw = Refl

0 r45BeginRaw : applyAction @{r45NameEq} @{r45KeyEq} (LBegin 0)
  r45AfterParent = Just (LBeginTag, r45AfterBegin)
r45BeginRaw = Refl

0 r45ChildInsertRaw : applyAction @{r45NameEq} @{r45KeyEq}
  (OInsert 1 (ChildOf 0) r45Child) r45AfterBegin =
    Just (OInsertTag, r45SourcePairFinal)
r45ChildInsertRaw = Refl

0 r45EarlyChildInsertRaw : applyAction @{r45NameEq} @{r45KeyEq}
  (OInsert 1 (ChildOf 0) r45Child) r45AfterParent =
    Just (OInsertTag, r45AfterEarlyChild)
r45EarlyChildInsertRaw = Refl

0 r45MovedBeginRaw : applyAction @{r45NameEq} @{r45KeyEq} (LBegin 0)
  r45AfterEarlyChild = Just (LBeginTag, r45TargetPairFinal)
r45MovedBeginRaw = Refl

0 r45SourceRetireRaw : applyAction @{r45NameEq} @{r45KeyEq} (ORetire 1)
  r45SourcePairFinal = Just (ORetireTag, r45SourceFinal)
r45SourceRetireRaw = Refl

0 r45TargetRetireRaw : applyAction @{r45NameEq} @{r45KeyEq} (ORetire 1)
  r45TargetPairFinal = Just (ORetireTag, r45TargetFinal)
r45TargetRetireRaw = Refl

0 r45InitialWellFormed : registryWellFormed @{r45NameEq} @{r45KeyEq}
  r45Initial = True
r45InitialWellFormed = Refl

0 r45AfterParentWellFormed : registryWellFormed @{r45NameEq} @{r45KeyEq}
  r45AfterParent = True
r45AfterParentWellFormed = preservationTheoremProof r45NameEq r45KeyEq
  (OInsert 0 Root r45Parent) r45Initial r45AfterParent OInsertTag
  r45InitialWellFormed r45ParentInsertRaw

0 r45AfterBeginWellFormed : registryWellFormed @{r45NameEq} @{r45KeyEq}
  r45AfterBegin = True
r45AfterBeginWellFormed = preservationTheoremProof r45NameEq r45KeyEq
  (LBegin 0) r45AfterParent r45AfterBegin LBeginTag
  r45AfterParentWellFormed r45BeginRaw

0 r45SourcePairFinalWellFormed : registryWellFormed @{r45NameEq} @{r45KeyEq}
  r45SourcePairFinal = True
r45SourcePairFinalWellFormed = preservationTheoremProof r45NameEq r45KeyEq
  (OInsert 1 (ChildOf 0) r45Child) r45AfterBegin r45SourcePairFinal OInsertTag
  r45AfterBeginWellFormed r45ChildInsertRaw

public export
0 r45ParentInsertChecked : checkedApplyAction @{r45NameEq} @{r45KeyEq}
  (OInsert 0 Root r45Parent) r45Initial = Just (OInsertTag, r45AfterParent)
r45ParentInsertChecked = rewrite r45ParentInsertRaw in Refl

public export
0 r45BeginChecked : checkedApplyAction @{r45NameEq} @{r45KeyEq} (LBegin 0)
  r45AfterParent = Just (LBeginTag, r45AfterBegin)
r45BeginChecked = rewrite r45BeginRaw in Refl

public export
0 r45ChildInsertChecked : checkedApplyAction @{r45NameEq} @{r45KeyEq}
  (OInsert 1 (ChildOf 0) r45Child) r45AfterBegin =
    Just (OInsertTag, r45SourcePairFinal)
r45ChildInsertChecked = rewrite r45ChildInsertRaw in Refl

public export
0 r45EarlyChildInsertChecked : checkedApplyAction @{r45NameEq} @{r45KeyEq}
  (OInsert 1 (ChildOf 0) r45Child) r45AfterParent =
    Just (OInsertTag, r45AfterEarlyChild)
r45EarlyChildInsertChecked = rewrite r45EarlyChildInsertRaw in Refl

public export
0 r45MovedBeginChecked : checkedApplyAction @{r45NameEq} @{r45KeyEq} (LBegin 0)
  r45AfterEarlyChild = Just (LBeginTag, r45TargetPairFinal)
r45MovedBeginChecked = rewrite r45MovedBeginRaw in Refl

public export
0 r45SourceRetireChecked : checkedApplyAction @{r45NameEq} @{r45KeyEq}
  (ORetire 1) r45SourcePairFinal = Just (ORetireTag, r45SourceFinal)
r45SourceRetireChecked = rewrite r45SourceRetireRaw in Refl

public export
0 r45TargetRetireChecked : checkedApplyAction @{r45NameEq} @{r45KeyEq}
  (ORetire 1) r45TargetPairFinal = Just (ORetireTag, r45TargetFinal)
r45TargetRetireChecked = rewrite r45TargetRetireRaw in Refl

public export
r45ParentInsert : Transition r45Initial r45AfterParent
r45ParentInsert = Fired r45NameEq r45KeyEq (OInsert 0 Root r45Parent)
  OInsertTag r45ParentInsertChecked

public export
r45Begin : Transition r45AfterParent r45AfterBegin
r45Begin = Fired r45NameEq r45KeyEq (LBegin 0) LBeginTag r45BeginChecked

public export
r45ChildInsert : Transition r45AfterBegin r45SourcePairFinal
r45ChildInsert = Fired r45NameEq r45KeyEq
  (OInsert 1 (ChildOf 0) r45Child) OInsertTag r45ChildInsertChecked

public export
r45EarlyChildInsert : Transition r45AfterParent r45AfterEarlyChild
r45EarlyChildInsert = Fired r45NameEq r45KeyEq
  (OInsert 1 (ChildOf 0) r45Child) OInsertTag r45EarlyChildInsertChecked

public export
r45MovedBegin : Transition r45AfterEarlyChild r45TargetPairFinal
r45MovedBegin = Fired r45NameEq r45KeyEq (LBegin 0) LBeginTag
  r45MovedBeginChecked

public export
r45SourceRetire : Transition r45SourcePairFinal r45SourceFinal
r45SourceRetire = Fired r45NameEq r45KeyEq (ORetire 1) ORetireTag
  r45SourceRetireChecked

public export
r45TargetRetire : Transition r45TargetPairFinal r45TargetFinal
r45TargetRetire = Fired r45NameEq r45KeyEq (ORetire 1) ORetireTag
  r45TargetRetireChecked

public export
r45SourceTrace : Transitions r45Initial r45SourceFinal
r45SourceTrace = MoreTransitions r45ParentInsert
  (MoreTransitions r45Begin
    (MoreTransitions r45ChildInsert
      (MoreTransitions r45SourceRetire NoTransitions)))

public export
r45TargetTrace : Transitions r45Initial r45TargetFinal
r45TargetTrace = MoreTransitions r45ParentInsert
  (MoreTransitions r45EarlyChildInsert
    (MoreTransitions r45MovedBegin
      (MoreTransitions r45TargetRetire NoTransitions)))

public export
0 r45SourceYield : ParentRegistrationYield r45Protocol r45NameEq 0 r45Child
  r45AfterBegin
r45SourceYield = MkParentRegistrationYield r45ParentBegun Refl r45YieldingStep
  [] id EmptyView Refl Here 0 1 Refl Refl 0 Refl Refl

public export
0 r45SourceDiscipline : RegistrationDiscipline r45Protocol r45NameEq
  r45SourceTrace
r45SourceDiscipline =
  RegistrationDisciplineStep r45ParentInsert _ (0 ** Refl)
    (RegistrationDisciplineStep r45Begin _ ()
      (RegistrationDisciplineStep r45ChildInsert _
        (r45SourceYield,
          ChildRetiredBeforeParent
            (ChildRetiresNow r45SourceRetire NoTransitions Refl))
        (RegistrationDisciplineStep r45SourceRetire NoTransitions ()
          RegistrationDisciplineEnd)))

public export
0 r45TargetDisciplineImpossible :
  RegistrationDiscipline r45Protocol r45NameEq r45TargetTrace -> Void
r45TargetDisciplineImpossible
  (RegistrationDisciplineStep _ _ rootRank
    (RegistrationDisciplineStep _ _ (yield, retirement)
      (RegistrationDisciplineStep _ _ beginUnit
        (RegistrationDisciplineStep _ NoTransitions retireUnit
          RegistrationDisciplineEnd)))) =
    case yield of
      MkParentRegistrationYield parentFiber found sourceStep continuation
        accumulator view lifecycle sourceInProgram parentRegistrationRank
        childRegistrationRank parentRanked childRanked tag stepTag cataloged =>
          case found of
            Refl => case lifecycle of Refl impossible

public export
0 r45MovedPairAligned : AlignedTransitions Nat R45Key Unit String R45Value
  r45NameEq r45KeyEq
  (MoreTransitions r45EarlyChildInsert (MoreTransitions r45MovedBegin NoTransitions))
r45MovedPairAligned = AlignedStep (OInsert 1 (ChildOf 0) r45Child) OInsertTag
  r45EarlyChildInsertChecked (MoreTransitions r45MovedBegin NoTransitions)
  (AlignedStep (LBegin 0) LBeginTag r45MovedBeginChecked NoTransitions AlignedEnd)

public export
0 r45ActivationOrchestrationImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  {transition : Transition before afterState} ->
  PaperActivationStep transition -> PaperOrchestrationStep transition -> Void
r45ActivationOrchestrationImpossible (PaperBeginStep activationAction tag)
  (PaperInsertStep orchestrationAction) =
    case trans (sym activationAction) orchestrationAction of Refl impossible
r45ActivationOrchestrationImpossible (PaperBeginStep activationAction tag)
  (PaperRetireStep orchestrationAction) =
    case trans (sym activationAction) orchestrationAction of Refl impossible
r45ActivationOrchestrationImpossible (PaperBeginStep activationAction tag)
  (PaperRemoveStep orchestrationAction) =
    case trans (sym activationAction) orchestrationAction of Refl impossible
r45ActivationOrchestrationImpossible (PaperIterStep activationAction tag)
  (PaperInsertStep orchestrationAction) =
    case trans (sym activationAction) orchestrationAction of Refl impossible
r45ActivationOrchestrationImpossible (PaperIterStep activationAction tag)
  (PaperRetireStep orchestrationAction) =
    case trans (sym activationAction) orchestrationAction of Refl impossible
r45ActivationOrchestrationImpossible (PaperIterStep activationAction tag)
  (PaperRemoveStep orchestrationAction) =
    case trans (sym activationAction) orchestrationAction of Refl impossible
r45ActivationOrchestrationImpossible (PaperFinishStep activationAction tag)
  (PaperInsertStep orchestrationAction) =
    case trans (sym activationAction) orchestrationAction of Refl impossible
r45ActivationOrchestrationImpossible (PaperFinishStep activationAction tag)
  (PaperRetireStep orchestrationAction) =
    case trans (sym activationAction) orchestrationAction of Refl impossible
r45ActivationOrchestrationImpossible (PaperFinishStep activationAction tag)
  (PaperRemoveStep orchestrationAction) =
    case trans (sym activationAction) orchestrationAction of Refl impossible

||| Historical pin for the exact pre-revision-21 public bare record.  Keeping
||| this test-local retired shape demonstrates that the old operational and
||| endpoint fields are all inhabited while target RegistrationDiscipline is
||| false.  It deliberately has no live authority.
public export
record RetiredBareLocalRelationalDiamond
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {first, middle, originalFinal : SystemState name key value world error}
  (left : Transition first middle)
  (right : Transition middle originalFinal) where
  constructor MkRetiredBareLocalRelationalDiamond
  retiredSwappedMiddle : SystemState name key value world error
  retiredSwappedFinal : SystemState name key value world error
  retiredMovedRight : Transition first retiredSwappedMiddle
  retiredMovedLeft : Transition retiredSwappedMiddle retiredSwappedFinal
  0 retiredMovedPairAligned : AlignedTransitions name key world error value
    nameEq keyEq (MoreTransitions retiredMovedRight
      (MoreTransitions retiredMovedLeft NoTransitions))
  0 retiredMovedRightAction : transitionAction retiredMovedRight =
    transitionAction right
  0 retiredMovedRightTag : transitionTag retiredMovedRight = transitionTag right
  0 retiredMovedLeftAction : transitionAction retiredMovedLeft =
    transitionAction left
  0 retiredMovedLeftTag : transitionTag retiredMovedLeft = transitionTag left
  0 retiredMovedRightActivationBranch :
    PaperActivationStep right -> PaperActivationStep retiredMovedRight
  0 retiredMovedLeftActivationBranch :
    PaperActivationStep left -> PaperActivationStep retiredMovedLeft
  0 retiredMovedRightOrchestrationBranch :
    PaperOrchestrationStep right -> PaperOrchestrationStep retiredMovedRight
  0 retiredMovedLeftOrchestrationBranch :
    PaperOrchestrationStep left -> PaperOrchestrationStep retiredMovedLeft
  0 retiredSwappedEffects : EffectStateRelated keyEq
    (projectEffectState @{nameEq} originalFinal)
    (projectEffectState @{nameEq} retiredSwappedFinal)
  0 retiredSwappedControls : ControlEquivalent name key world error value nameEq
    originalFinal retiredSwappedFinal
  0 retiredSwappedWellFormed : registryWellFormed @{nameEq} @{keyEq}
    retiredSwappedFinal = True

public export
0 r45BareDiamond : RetiredBareLocalRelationalDiamond Nat R45Key Unit String
  R45Value r45NameEq r45KeyEq r45Begin r45ChildInsert
r45BareDiamond =
  let 0 earlyWellFormed : (registryWellFormed @{r45NameEq} @{r45KeyEq}
        r45AfterEarlyChild = True)
      earlyWellFormed = preservationTheoremProof r45NameEq r45KeyEq
        (OInsert 1 (ChildOf 0) r45Child) r45AfterParent r45AfterEarlyChild
        OInsertTag r45AfterParentWellFormed r45EarlyChildInsertRaw
      0 targetWellFormed : (registryWellFormed @{r45NameEq} @{r45KeyEq}
        r45TargetPairFinal = True)
      targetWellFormed = preservationTheoremProof r45NameEq r45KeyEq
        (LBegin 0) r45AfterEarlyChild r45TargetPairFinal LBeginTag
        earlyWellFormed r45MovedBeginRaw
      0 effects : EffectStateRelated r45KeyEq
        (projectEffectState @{r45NameEq} r45SourcePairFinal)
        (projectEffectState @{r45NameEq} r45TargetPairFinal)
      effects = MkEffectStateRelated Refl tables
        where
        0 tables : (actor : Nat) ->
          bindings (effectTables
            (projectEffectState @{r45NameEq} r45SourcePairFinal) actor) =
          bindings (effectTables
            (projectEffectState @{r45NameEq} r45TargetPairFinal) actor)
        tables Z = Refl
        tables (S Z) = Refl
        tables (S (S later)) = Refl
      0 controls : ControlEquivalent Nat R45Key Unit String R45Value r45NameEq
        r45SourcePairFinal r45TargetPairFinal
      controls = MkControlEquivalent control
        where
        0 control : (actor : Nat) -> FiberControlMaybeRelated
          {name = Nat} {key = R45Key} {value = R45Value}
          {world = Unit} {error = String}
          (lookupFiber @{r45NameEq} actor (registry r45SourcePairFinal))
          (lookupFiber @{r45NameEq} actor (registry r45TargetPairFinal))
        control Z = fiberControlMaybeReflexive _
        control (S Z) = fiberControlMaybeReflexive _
        control (S (S later)) = fiberControlMaybeReflexive _
  in MkRetiredBareLocalRelationalDiamond r45AfterEarlyChild r45TargetPairFinal
      r45EarlyChildInsert r45MovedBegin r45MovedPairAligned
      Refl Refl Refl Refl
      (\activation => void (r45ActivationOrchestrationImpossible activation
        (PaperInsertStep Refl)))
      (\activation => PaperBeginStep Refl Refl)
      (\orchestration => PaperInsertStep Refl)
      (\orchestration => void (r45ActivationOrchestrationImpossible
        (PaperBeginStep Refl Refl) orchestration))
      effects controls targetWellFormed
