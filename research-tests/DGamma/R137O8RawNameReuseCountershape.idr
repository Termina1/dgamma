module DGamma.R137O8RawNameReuseCountershape

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4Support
import DGamma.CP5ConfluenceDeletionChainSpike
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

public export
data R137Name = Anchor | ActorA | ActorB

public export
implementation DecEq R137Name where
  decEq Anchor Anchor = Yes Refl
  decEq Anchor ActorA = No (\same => case same of Refl impossible)
  decEq Anchor ActorB = No (\same => case same of Refl impossible)
  decEq ActorA Anchor = No (\same => case same of Refl impossible)
  decEq ActorA ActorA = Yes Refl
  decEq ActorA ActorB = No (\same => case same of Refl impossible)
  decEq ActorB Anchor = No (\same => case same of Refl impossible)
  decEq ActorB ActorA = No (\same => case same of Refl impossible)
  decEq ActorB ActorB = Yes Refl

public export
data R137Key = SourceKey | LinkKey

public export
implementation DecEq R137Key where
  decEq SourceKey SourceKey = Yes Refl
  decEq SourceKey LinkKey = No (\same => case same of Refl impossible)
  decEq LinkKey SourceKey = No (\same => case same of Refl impossible)
  decEq LinkKey LinkKey = Yes Refl

public export
R137Value : R137Key -> Type
R137Value SourceKey = Unit
R137Value LinkKey = Unit

r137NotInEmpty : {key : Type} -> {value : key} -> Not (Elem value [])
r137NotInEmpty member impossible

public export
r137SourceSpec : CoeffectSpec R137Key
r137SourceSpec = MkCoeffectSpec [SourceKey]
  (UniqueCons r137NotInEmpty UniqueNil)

public export
r137LinkSpec : CoeffectSpec R137Key
r137LinkSpec = MkCoeffectSpec [LinkKey]
  (UniqueCons r137NotInEmpty UniqueNil)

r137SourceContext : CoeffectContext R137Key R137Value
r137SourceContext = MkCoeffectContext [Bind SourceKey ()]
  (UniqueCons r137NotInEmpty UniqueNil)

r137LinkContext : CoeffectContext R137Key R137Value
r137LinkContext = MkCoeffectContext [Bind LinkKey ()]
  (UniqueCons r137NotInEmpty UniqueNil)

r137SourceOwned : OwnedTable R137Key R137Value r137SourceSpec
r137SourceOwned = MkOwnedTable r137SourceContext (\key, member => member)

r137LinkOwned : OwnedTable R137Key R137Value r137LinkSpec
r137LinkOwned = MkOwnedTable r137LinkContext (\key, member => member)

r137RestoreSource : OwnedTable R137Key R137Value r137SourceSpec ->
  LocalState R137Key R137Value Unit r137SourceSpec ->
  LocalState R137Key R137Value Unit r137SourceSpec
r137RestoreSource previous later = MkLocalState () previous

r137RestoreLink : OwnedTable R137Key R137Value r137LinkSpec ->
  LocalState R137Key R137Value Unit r137LinkSpec ->
  LocalState R137Key R137Value Unit r137LinkSpec
r137RestoreLink previous later = MkLocalState () previous

r137RunSource : DepValues R137Key R137Value [] ->
  LocalState R137Key R137Value Unit r137SourceSpec ->
  Either Unit
    (LocalState R137Key R137Value Unit r137SourceSpec,
     LocalState R137Key R137Value Unit r137SourceSpec ->
       LocalState R137Key R137Value Unit r137SourceSpec)
r137RunSource NoDepValues (MkLocalState () previous) =
  Right (MkLocalState () r137SourceOwned, r137RestoreSource previous)

0 r137WitnessSource : {auto keyEq : DecEq R137Key} ->
  (capability : DepValues R137Key R137Value []) ->
  (before, afterState : LocalState R137Key R137Value Unit r137SourceSpec) ->
  (undo : LocalState R137Key R137Value Unit r137SourceSpec ->
    LocalState R137Key R137Value Unit r137SourceSpec) ->
  r137RunSource capability before = Right (afterState, undo) ->
  normalizeLocal r137SourceSpec before = before ->
  undo (normalizeLocal r137SourceSpec afterState) = before
r137WitnessSource NoDepValues before afterState undo returned canonical =
  replace
    {p = \outcome => case outcome of
      Left error => Unit
      Right (next, inverse) =>
        inverse (normalizeLocal r137SourceSpec next) = before}
    returned (case before of MkLocalState () previous => Refl)

r137RunLinkNoDeps : DepValues R137Key R137Value [] ->
  LocalState R137Key R137Value Unit r137LinkSpec ->
  Either Unit
    (LocalState R137Key R137Value Unit r137LinkSpec,
     LocalState R137Key R137Value Unit r137LinkSpec ->
       LocalState R137Key R137Value Unit r137LinkSpec)
r137RunLinkNoDeps NoDepValues (MkLocalState () previous) =
  Right (MkLocalState () r137LinkOwned, r137RestoreLink previous)

0 r137WitnessLinkNoDeps : {auto keyEq : DecEq R137Key} ->
  (capability : DepValues R137Key R137Value []) ->
  (before, afterState : LocalState R137Key R137Value Unit r137LinkSpec) ->
  (undo : LocalState R137Key R137Value Unit r137LinkSpec ->
    LocalState R137Key R137Value Unit r137LinkSpec) ->
  r137RunLinkNoDeps capability before = Right (afterState, undo) ->
  normalizeLocal r137LinkSpec before = before ->
  undo (normalizeLocal r137LinkSpec afterState) = before
r137WitnessLinkNoDeps NoDepValues before afterState undo returned canonical =
  replace
    {p = \outcome => case outcome of
      Left error => Unit
      Right (next, inverse) =>
        inverse (normalizeLocal r137LinkSpec next) = before}
    returned (case before of MkLocalState () previous => Refl)

r137RunLinkFromSource : DepValues R137Key R137Value [SourceKey] ->
  LocalState R137Key R137Value Unit r137LinkSpec ->
  Either Unit
    (LocalState R137Key R137Value Unit r137LinkSpec,
     LocalState R137Key R137Value Unit r137LinkSpec ->
       LocalState R137Key R137Value Unit r137LinkSpec)
r137RunLinkFromSource (OneDepValue value NoDepValues)
  (MkLocalState () previous) =
    Right (MkLocalState () r137LinkOwned, r137RestoreLink previous)

0 r137WitnessLinkFromSource : {auto keyEq : DecEq R137Key} ->
  (capability : DepValues R137Key R137Value [SourceKey]) ->
  (before, afterState : LocalState R137Key R137Value Unit r137LinkSpec) ->
  (undo : LocalState R137Key R137Value Unit r137LinkSpec ->
    LocalState R137Key R137Value Unit r137LinkSpec) ->
  r137RunLinkFromSource capability before = Right (afterState, undo) ->
  normalizeLocal r137LinkSpec before = before ->
  undo (normalizeLocal r137LinkSpec afterState) = before
r137WitnessLinkFromSource (OneDepValue value NoDepValues) before afterState undo
  returned canonical =
    replace
      {p = \outcome => case outcome of
        Left error => Unit
        Right (next, inverse) =>
          inverse (normalizeLocal r137LinkSpec next) = before}
      returned (case before of MkLocalState () previous => Refl)

public export
r137SourceStep : StepEffect R137Key R137Value Unit Unit [] r137SourceSpec
r137SourceStep = MkStepEffect Nothing r137RunSource r137WitnessSource

public export
r137LinkNoDepsStep : StepEffect R137Key R137Value Unit Unit [] r137LinkSpec
r137LinkNoDepsStep = MkStepEffect Nothing r137RunLinkNoDeps r137WitnessLinkNoDeps

public export
r137LinkFromSourceStep :
  StepEffect R137Key R137Value Unit Unit [SourceKey] r137LinkSpec
r137LinkFromSourceStep = MkStepEffect Nothing r137RunLinkFromSource
  r137WitnessLinkFromSource

public export
r137FailStep : StepEffect R137Key R137Value Unit Unit [LinkKey] emptySpec
r137FailStep = MkStepEffect Nothing
  (\(OneDepValue value NoDepValues), before => Left ())
  (\(OneDepValue value NoDepValues), before, afterState, undo, returned,
      canonical => case returned of _ impossible)

public export
r137AnchorComponent : Component R137Key R137Value Unit Unit
r137AnchorComponent = MkComponent emptySpec r137SourceSpec [r137SourceStep]

public export
r137FirstAComponent : Component R137Key R137Value Unit Unit
r137FirstAComponent = MkComponent r137SourceSpec r137LinkSpec
  [r137LinkFromSourceStep]

public export
r137ConsumerComponent : Component R137Key R137Value Unit Unit
r137ConsumerComponent = MkComponent r137LinkSpec emptySpec [r137FailStep]

public export
r137SecondBComponent : Component R137Key R137Value Unit Unit
r137SecondBComponent = MkComponent emptySpec r137LinkSpec [r137LinkNoDepsStep]

public export
r137AnchorFresh : Fiber R137Name R137Key R137Value Unit Unit
r137AnchorFresh = freshFiber r137AnchorComponent Root

public export
r137AnchorBegun : Fiber R137Name R137Key R137Value Unit Unit
r137AnchorBegun = setFiberLifecycle r137AnchorFresh
  (Reloading [r137SourceStep] id EmptyView)

r137AnchorPriorTable : OwnedTable R137Key R137Value r137SourceSpec
r137AnchorPriorTable = restrictOwnedPreservingOrder r137SourceSpec
  (ownedValues (fiberTable r137AnchorBegun))

r137AnchorAccumulator :
  LocalState R137Key R137Value Unit r137SourceSpec ->
  LocalState R137Key R137Value Unit r137SourceSpec
r137AnchorAccumulator = pushLocalUndo r137SourceSpec id
  (r137RestoreSource r137AnchorPriorTable)

public export
r137AnchorActive : Fiber R137Name R137Key R137Value Unit Unit
r137AnchorActive = setFiberRuntime r137AnchorBegun r137SourceOwned
  (Active r137AnchorAccumulator EmptyView)

public export
r137AnchorRetired : Fiber R137Name R137Key R137Value Unit Unit
r137AnchorRetired = retireFiber r137AnchorActive

public export
r137FirstAFresh : Fiber R137Name R137Key R137Value Unit Unit
r137FirstAFresh = freshFiber r137FirstAComponent Root

public export
r137FirstAView : View R137Name [SourceKey]
r137FirstAView = ProviderView Anchor EmptyView

public export
r137FirstABegun : Fiber R137Name R137Key R137Value Unit Unit
r137FirstABegun = setFiberLifecycle r137FirstAFresh
  (Reloading [r137LinkFromSourceStep] id r137FirstAView)

r137FirstAPriorTable : OwnedTable R137Key R137Value r137LinkSpec
r137FirstAPriorTable = restrictOwnedPreservingOrder r137LinkSpec
  (ownedValues (fiberTable r137FirstABegun))

r137FirstAAccumulator :
  LocalState R137Key R137Value Unit r137LinkSpec ->
  LocalState R137Key R137Value Unit r137LinkSpec
r137FirstAAccumulator = pushLocalUndo r137LinkSpec id
  (r137RestoreLink r137FirstAPriorTable)

public export
r137FirstAActive : Fiber R137Name R137Key R137Value Unit Unit
r137FirstAActive = setFiberRuntime r137FirstABegun r137LinkOwned
  (Active r137FirstAAccumulator r137FirstAView)

r137FirstAActiveRetired : Fiber R137Name R137Key R137Value Unit Unit
r137FirstAActiveRetired = retireFiber r137FirstAActive

public export
r137FirstAUnloading : Fiber R137Name R137Key R137Value Unit Unit
r137FirstAUnloading = setFiberLifecycle r137FirstAActiveRetired
  (Unloading r137FirstAAccumulator r137FirstAView Nothing)

r137FirstARestoredTable : OwnedTable R137Key R137Value r137LinkSpec
r137FirstARestoredTable = restrictOwnedPreservingOrder r137LinkSpec
  (ownedValues r137FirstAPriorTable)

public export
r137FirstAInactive : Fiber R137Name R137Key R137Value Unit Unit
r137FirstAInactive = setFiberRuntime r137FirstAUnloading r137FirstARestoredTable
  (Inactive Nothing)

public export
r137FirstARetired : Fiber R137Name R137Key R137Value Unit Unit
r137FirstARetired = r137FirstAInactive

public export
r137ConsumerFresh : Fiber R137Name R137Key R137Value Unit Unit
r137ConsumerFresh = freshFiber r137ConsumerComponent Root

public export
r137FirstBView : View R137Name [LinkKey]
r137FirstBView = ProviderView ActorA EmptyView

public export
r137FirstBBegun : Fiber R137Name R137Key R137Value Unit Unit
r137FirstBBegun = setFiberLifecycle r137ConsumerFresh
  (Reloading [r137FailStep] id r137FirstBView)

public export
r137FirstBUnloading : Fiber R137Name R137Key R137Value Unit Unit
r137FirstBUnloading = setFiberLifecycle r137FirstBBegun
  (Unloading id r137FirstBView (Just ()))

r137FirstBNormalizedTable : OwnedTable R137Key R137Value emptySpec
r137FirstBNormalizedTable = restrictOwnedPreservingOrder emptySpec
  (ownedValues (fiberTable r137FirstBUnloading))

public export
r137FirstBInactive : Fiber R137Name R137Key R137Value Unit Unit
r137FirstBInactive = setFiberRuntime r137FirstBUnloading r137FirstBNormalizedTable
  (Inactive (Just ()))

public export
r137FirstBRetired : Fiber R137Name R137Key R137Value Unit Unit
r137FirstBRetired = retireFiber r137FirstBInactive

public export
r137SecondBFresh : Fiber R137Name R137Key R137Value Unit Unit
r137SecondBFresh = freshFiber r137SecondBComponent Root

public export
r137SecondBBegun : Fiber R137Name R137Key R137Value Unit Unit
r137SecondBBegun = setFiberLifecycle r137SecondBFresh
  (Reloading [r137LinkNoDepsStep] id EmptyView)

r137SecondBPriorTable : OwnedTable R137Key R137Value r137LinkSpec
r137SecondBPriorTable = restrictOwnedPreservingOrder r137LinkSpec
  (ownedValues (fiberTable r137SecondBBegun))

r137SecondBAccumulator :
  LocalState R137Key R137Value Unit r137LinkSpec ->
  LocalState R137Key R137Value Unit r137LinkSpec
r137SecondBAccumulator = pushLocalUndo r137LinkSpec id
  (r137RestoreLink r137SecondBPriorTable)

public export
r137SecondBActive : Fiber R137Name R137Key R137Value Unit Unit
r137SecondBActive = setFiberRuntime r137SecondBBegun r137LinkOwned
  (Active r137SecondBAccumulator EmptyView)

public export
r137SecondAView : View R137Name [LinkKey]
r137SecondAView = ProviderView ActorB EmptyView

public export
r137SecondABegun : Fiber R137Name R137Key R137Value Unit Unit
r137SecondABegun = setFiberLifecycle r137ConsumerFresh
  (Reloading [r137FailStep] id r137SecondAView)

public export
r137SecondAUnloading : Fiber R137Name R137Key R137Value Unit Unit
r137SecondAUnloading = setFiberLifecycle r137SecondABegun
  (Unloading id r137SecondAView (Just ()))

r137SecondANormalizedTable : OwnedTable R137Key R137Value emptySpec
r137SecondANormalizedTable = restrictOwnedPreservingOrder emptySpec
  (ownedValues (fiberTable r137SecondAUnloading))

public export
r137SecondAInactive : Fiber R137Name R137Key R137Value Unit Unit
r137SecondAInactive = setFiberRuntime r137SecondAUnloading r137SecondANormalizedTable
  (Inactive (Just ()))

0 r137AnchorNotNil : Not (Elem Anchor [])
r137AnchorNotNil member impossible

0 r137ActorANotAnchor : Not (Elem ActorA [Anchor])
r137ActorANotAnchor Here impossible
r137ActorANotAnchor (There member) impossible

0 r137ActorBNotAAnchor : Not (Elem ActorB [ActorA, Anchor])
r137ActorBNotAAnchor Here impossible
r137ActorBNotAAnchor (There Here) impossible
r137ActorBNotAAnchor (There (There member)) impossible

0 r137ActorBNotAnchor : Not (Elem ActorB [Anchor])
r137ActorBNotAnchor Here impossible
r137ActorBNotAnchor (There member) impossible

0 r137ActorANotBAnchor : Not (Elem ActorA [ActorB, Anchor])
r137ActorANotBAnchor Here impossible
r137ActorANotBAnchor (There Here) impossible
r137ActorANotBAnchor (There (There member)) impossible

0 r137UniqueAnchor : UniqueKeys [Anchor]
r137UniqueAnchor = UniqueCons r137AnchorNotNil UniqueNil

0 r137UniqueAAnchor : UniqueKeys [ActorA, Anchor]
r137UniqueAAnchor = UniqueCons r137ActorANotAnchor r137UniqueAnchor

0 r137UniqueBAAnchor : UniqueKeys [ActorB, ActorA, Anchor]
r137UniqueBAAnchor = UniqueCons r137ActorBNotAAnchor r137UniqueAAnchor

0 r137UniqueBAnchor : UniqueKeys [ActorB, Anchor]
r137UniqueBAnchor = UniqueCons r137ActorBNotAnchor r137UniqueAnchor

0 r137UniqueABAnchor : UniqueKeys [ActorA, ActorB, Anchor]
r137UniqueABAnchor = UniqueCons r137ActorANotBAnchor r137UniqueBAnchor

public export
r137R0 : Registry R137Name R137Key R137Value Unit Unit
r137R0 = MkCoeffectContext [] UniqueNil

public export
r137R1 : Registry R137Name R137Key R137Value Unit Unit
r137R1 = insertBinding Anchor r137AnchorFresh r137R0 Refl

public export
r137R2 : Registry R137Name R137Key R137Value Unit Unit
r137R2 = MkCoeffectContext [Bind Anchor r137AnchorBegun]
  (uniqueBindings r137R1)

public export
r137R3 : Registry R137Name R137Key R137Value Unit Unit
r137R3 = MkCoeffectContext [Bind Anchor r137AnchorActive]
  (uniqueBindings r137R1)

public export
r137R4 : Registry R137Name R137Key R137Value Unit Unit
r137R4 = insertBinding ActorA r137FirstAFresh r137R3 Refl

public export
r137R5 : Registry R137Name R137Key R137Value Unit Unit
r137R5 = MkCoeffectContext
  [Bind ActorA r137FirstABegun, Bind Anchor r137AnchorActive]
  (uniqueBindings r137R4)

public export
r137R6 : Registry R137Name R137Key R137Value Unit Unit
r137R6 = MkCoeffectContext
  [Bind ActorA r137FirstAActive, Bind Anchor r137AnchorActive]
  (uniqueBindings r137R4)

public export
r137R7 : Registry R137Name R137Key R137Value Unit Unit
r137R7 = insertBinding ActorB r137ConsumerFresh r137R6 Refl

public export
r137R8 : Registry R137Name R137Key R137Value Unit Unit
r137R8 = MkCoeffectContext
  [Bind ActorB r137FirstBBegun, Bind ActorA r137FirstAActive,
   Bind Anchor r137AnchorActive] (uniqueBindings r137R7)

public export
r137R9 : Registry R137Name R137Key R137Value Unit Unit
r137R9 = MkCoeffectContext
  [Bind ActorB r137FirstBUnloading, Bind ActorA r137FirstAActive,
   Bind Anchor r137AnchorActive] (uniqueBindings r137R7)

public export
r137R10 : Registry R137Name R137Key R137Value Unit Unit
r137R10 = MkCoeffectContext
  [Bind ActorB r137FirstBInactive, Bind ActorA r137FirstAActive,
   Bind Anchor r137AnchorActive] (uniqueBindings r137R7)

public export
r137R11 : Registry R137Name R137Key R137Value Unit Unit
r137R11 = MkCoeffectContext
  [Bind ActorB r137FirstBRetired, Bind ActorA r137FirstAActive,
   Bind Anchor r137AnchorActive] (uniqueBindings r137R7)

public export
r137R12 : Registry R137Name R137Key R137Value Unit Unit
r137R12 = deleteBinding ActorB r137R11

public export
r137R13 : Registry R137Name R137Key R137Value Unit Unit
r137R13 = MkCoeffectContext
  [Bind ActorA r137FirstAActive, Bind Anchor r137AnchorRetired]
  (uniqueBindings r137R12)

public export
r137R14 : Registry R137Name R137Key R137Value Unit Unit
r137R14 = MkCoeffectContext
  [Bind ActorA r137FirstAActiveRetired, Bind Anchor r137AnchorRetired]
  (uniqueBindings r137R12)

public export
r137R15 : Registry R137Name R137Key R137Value Unit Unit
r137R15 = MkCoeffectContext
  [Bind ActorA r137FirstAUnloading, Bind Anchor r137AnchorRetired]
  (uniqueBindings r137R12)

public export
r137R16 : Registry R137Name R137Key R137Value Unit Unit
r137R16 = MkCoeffectContext
  [Bind ActorA r137FirstARetired, Bind Anchor r137AnchorRetired]
  (uniqueBindings r137R12)

public export
r137R17 : Registry R137Name R137Key R137Value Unit Unit
r137R17 = deleteBinding ActorA r137R16

public export
r137R18 : Registry R137Name R137Key R137Value Unit Unit
r137R18 = insertBinding ActorB r137SecondBFresh r137R17 Refl

public export
r137R19 : Registry R137Name R137Key R137Value Unit Unit
r137R19 = MkCoeffectContext
  [Bind ActorB r137SecondBBegun, Bind Anchor r137AnchorRetired]
  (uniqueBindings r137R18)

public export
r137R20 : Registry R137Name R137Key R137Value Unit Unit
r137R20 = MkCoeffectContext
  [Bind ActorB r137SecondBActive, Bind Anchor r137AnchorRetired]
  (uniqueBindings r137R18)

public export
r137R21 : Registry R137Name R137Key R137Value Unit Unit
r137R21 = insertBinding ActorA r137ConsumerFresh r137R20 Refl

public export
r137R22 : Registry R137Name R137Key R137Value Unit Unit
r137R22 = MkCoeffectContext
  [Bind ActorA r137SecondABegun, Bind ActorB r137SecondBActive,
   Bind Anchor r137AnchorRetired] (uniqueBindings r137R21)

public export
r137R23 : Registry R137Name R137Key R137Value Unit Unit
r137R23 = MkCoeffectContext
  [Bind ActorA r137SecondAUnloading, Bind ActorB r137SecondBActive,
   Bind Anchor r137AnchorRetired] (uniqueBindings r137R21)

public export
r137R24 : Registry R137Name R137Key R137Value Unit Unit
r137R24 = MkCoeffectContext
  [Bind ActorA r137SecondAInactive, Bind ActorB r137SecondBActive,
   Bind Anchor r137AnchorRetired] (uniqueBindings r137R21)

public export
r137S0, r137S1, r137S2, r137S3, r137S4, r137S5, r137S6, r137S7,
  r137S8, r137S9, r137S10, r137S11, r137S12, r137S13, r137S14,
  r137S15, r137S16, r137S17, r137S18, r137S19, r137S20, r137S21,
  r137S22, r137S23, r137S24 :
  SystemState R137Name R137Key R137Value Unit Unit
r137S0 = MkSystemState () r137R0
r137S1 = MkSystemState () r137R1
r137S2 = MkSystemState () r137R2
r137S3 = MkSystemState () r137R3
r137S4 = MkSystemState () r137R4
r137S5 = MkSystemState () r137R5
r137S6 = MkSystemState () r137R6
r137S7 = MkSystemState () r137R7
r137S8 = MkSystemState () r137R8
r137S9 = MkSystemState () r137R9
r137S10 = MkSystemState () r137R10
r137S11 = MkSystemState () r137R11
r137S12 = MkSystemState () r137R12
r137S13 = MkSystemState () r137R13
r137S14 = MkSystemState () r137R14
r137S15 = MkSystemState () r137R15
r137S16 = MkSystemState () r137R16
r137S17 = MkSystemState () r137R17
r137S18 = MkSystemState () r137R18
r137S19 = MkSystemState () r137R19
r137S20 = MkSystemState () r137R20
r137S21 = MkSystemState () r137R21
r137S22 = MkSystemState () r137R22
r137S23 = MkSystemState () r137R23
r137S24 = MkSystemState () r137R24

public export
r137NameEq : DecEq R137Name
r137NameEq = %search

public export
r137KeyEq : DecEq R137Key
r137KeyEq = %search

public export
0 r137E0 : applyAction @{r137NameEq} @{r137KeyEq}
  (OInsert Anchor Root r137AnchorComponent) r137S0 = Just (OInsertTag, r137S1)
r137E0 = Refl

public export
0 r137E1 : applyAction @{r137NameEq} @{r137KeyEq} (LBegin Anchor) r137S1 =
  Just (LBeginTag, r137S2)
r137E1 = Refl

public export
0 r137E2 : applyAction @{r137NameEq} @{r137KeyEq} (LAdvance Anchor) r137S2 =
  Just (LFinishTag, r137S3)
r137E2 = Refl

public export
0 r137E3 : applyAction @{r137NameEq} @{r137KeyEq}
  (OInsert ActorA Root r137FirstAComponent) r137S3 = Just (OInsertTag, r137S4)
r137E3 = Refl

0 r137ProviderSourceR3 : providerOf @{r137NameEq} @{r137KeyEq}
  {value = R137Value} {world = Unit} {error = Unit} SourceKey r137R3 = Just Anchor
r137ProviderSourceR3 = Refl

public export
0 r137E4 : applyAction @{r137NameEq} @{r137KeyEq} (LBegin ActorA) r137S4 =
  Just (LBeginTag, r137S5)
r137E4 = Refl

public export
0 r137E5 : applyAction @{r137NameEq} @{r137KeyEq} (LAdvance ActorA) r137S5 =
  Just (LFinishTag, r137S6)
r137E5 = Refl

public export
0 r137E6 : applyAction @{r137NameEq} @{r137KeyEq}
  (OInsert ActorB Root r137ConsumerComponent) r137S6 = Just (OInsertTag, r137S7)
r137E6 = Refl

public export
0 r137E7 : applyAction @{r137NameEq} @{r137KeyEq} (LBegin ActorB) r137S7 =
  Just (LBeginTag, r137S8)
r137E7 = Refl

public export
0 r137E8 : applyAction @{r137NameEq} @{r137KeyEq} (LAdvance ActorB) r137S8 =
  Just (LRaiseTag, r137S9)
r137E8 = Refl

public export
0 r137E9 : applyAction @{r137NameEq} @{r137KeyEq} (LUnload ActorB) r137S9 =
  Just (LUnloadTag, r137S10)
r137E9 = Refl

public export
0 r137E10 : applyAction @{r137NameEq} @{r137KeyEq} (ORetire ActorB) r137S10 =
  Just (ORetireTag, r137S11)
r137E10 = Refl

public export
0 r137E11 : applyAction @{r137NameEq} @{r137KeyEq} (ORemove ActorB) r137S11 =
  Just (ORemoveTag, r137S12)
r137E11 = Refl

public export
0 r137E12 : applyAction @{r137NameEq} @{r137KeyEq} (ORetire Anchor) r137S12 =
  Just (ORetireTag, r137S13)
r137E12 = Refl

public export
0 r137E13 : applyAction @{r137NameEq} @{r137KeyEq} (ORetire ActorA) r137S13 =
  Just (ORetireTag, r137S14)
r137E13 = Refl

public export
0 r137E14 : applyAction @{r137NameEq} @{r137KeyEq} (LLeave ActorA) r137S14 =
  Just (LLeaveTag, r137S15)
r137E14 = Refl

public export
0 r137E15 : applyAction @{r137NameEq} @{r137KeyEq} (LUnload ActorA) r137S15 =
  Just (LUnloadTag, r137S16)
r137E15 = Refl

public export
0 r137E16 : applyAction @{r137NameEq} @{r137KeyEq} (ORemove ActorA) r137S16 =
  Just (ORemoveTag, r137S17)
r137E16 = Refl

public export
0 r137E17 : applyAction @{r137NameEq} @{r137KeyEq}
  (OInsert ActorB Root r137SecondBComponent) r137S17 = Just (OInsertTag, r137S18)
r137E17 = Refl

public export
0 r137E18 : applyAction @{r137NameEq} @{r137KeyEq} (LBegin ActorB) r137S18 =
  Just (LBeginTag, r137S19)
r137E18 = Refl

public export
0 r137E19 : applyAction @{r137NameEq} @{r137KeyEq} (LAdvance ActorB) r137S19 =
  Just (LFinishTag, r137S20)
r137E19 = Refl

public export
0 r137E20 : applyAction @{r137NameEq} @{r137KeyEq}
  (OInsert ActorA Root r137ConsumerComponent) r137S20 = Just (OInsertTag, r137S21)
r137E20 = Refl

public export
0 r137E21 : applyAction @{r137NameEq} @{r137KeyEq} (LBegin ActorA) r137S21 =
  Just (LBeginTag, r137S22)
r137E21 = Refl

public export
0 r137E22 : applyAction @{r137NameEq} @{r137KeyEq} (LAdvance ActorA) r137S22 =
  Just (LRaiseTag, r137S23)
r137E22 = Refl

public export
0 r137E23 : applyAction @{r137NameEq} @{r137KeyEq} (LUnload ActorA) r137S23 =
  Just (LUnloadTag, r137S24)
r137E23 = Refl

public export
0 r137W0 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S0 = True
r137W0 = Refl
public export
0 r137W1 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S1 = True
r137W1 = Refl
public export
0 r137W2 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S2 = True
r137W2 = Refl
public export
0 r137W3 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S3 = True
r137W3 = Refl
public export
0 r137W4 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S4 = True
r137W4 = Refl
public export
0 r137W5 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S5 = True
r137W5 = Refl
public export
0 r137W6 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S6 = True
r137W6 = Refl
public export
0 r137W7 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S7 = True
r137W7 = Refl
public export
0 r137W8 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S8 = True
r137W8 = Refl
public export
0 r137W9 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S9 = True
r137W9 = Refl
public export
0 r137W10 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S10 = True
r137W10 = Refl
public export
0 r137W11 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S11 = True
r137W11 = Refl
public export
0 r137W12 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S12 = True
r137W12 = Refl
public export
0 r137W13 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S13 = True
r137W13 = Refl
public export
0 r137W14 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S14 = True
r137W14 = Refl
public export
0 r137W15 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S15 = True
r137W15 = Refl
public export
0 r137W16 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S16 = True
r137W16 = Refl
public export
0 r137W17 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S17 = True
r137W17 = Refl
public export
0 r137W18 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S18 = True
r137W18 = Refl
public export
0 r137W19 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S19 = True
r137W19 = Refl
public export
0 r137W20 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S20 = True
r137W20 = Refl
public export
0 r137W21 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S21 = True
r137W21 = Refl
public export
0 r137W22 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S22 = True
r137W22 = Refl
public export
0 r137W23 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S23 = True
r137W23 = Refl
public export
0 r137W24 : registryWellFormed @{r137NameEq} @{r137KeyEq} r137S24 = True
r137W24 = Refl

public export
0 r137InstalledBAt8 : installedAt @{r137NameEq} ActorB r137S8 = True
r137InstalledBAt8 = Refl

public export
0 r137InstalledBAt9 : installedAt @{r137NameEq} ActorB r137S9 = True
r137InstalledBAt9 = Refl

public export
0 r137InstalledAAt22 : installedAt @{r137NameEq} ActorA r137S22 = True
r137InstalledAAt22 = Refl

public export
0 r137InstalledAAt23 : installedAt @{r137NameEq} ActorA r137S23 = True
r137InstalledAAt23 = Refl

public export
0 r137FirstAFoundAt8 :
  lookupFiber @{r137NameEq} ActorA (registry r137S8) = Just r137FirstAActive
r137FirstAFoundAt8 = Refl

public export
0 r137FirstBFoundAt8 :
  lookupFiber @{r137NameEq} ActorB (registry r137S8) = Just r137FirstBBegun
r137FirstBFoundAt8 = Refl

public export
0 r137SecondBFoundAt22 :
  lookupFiber @{r137NameEq} ActorB (registry r137S22) = Just r137SecondBActive
r137SecondBFoundAt22 = Refl

public export
0 r137SecondAFoundAt22 :
  lookupFiber @{r137NameEq} ActorA (registry r137S22) = Just r137SecondABegun
r137SecondAFoundAt22 = Refl

r137FirstRank : R137Name -> Nat
r137FirstRank Anchor = 0
r137FirstRank ActorA = 1
r137FirstRank ActorB = 2

r137SecondRank : R137Name -> Nat
r137SecondRank Anchor = 0
r137SecondRank ActorB = 1
r137SecondRank ActorA = 2

r137EdgeRaises : (R137Name -> Nat) ->
  SystemState R137Name R137Key R137Value Unit Unit ->
  R137Name -> R137Name -> Bool
r137EdgeRaises rank state provider consumer =
  not (precedesAt @{r137NameEq} @{r137KeyEq} provider consumer state) ||
  rank provider < rank consumer

r137RankedRegistry : (R137Name -> Nat) ->
  SystemState R137Name R137Key R137Value Unit Unit -> Bool
r137RankedRegistry rank state =
  all (\provider => all (\consumer =>
    r137EdgeRaises rank state provider consumer)
    [Anchor, ActorA, ActorB]) [Anchor, ActorA, ActorB]

public export
r137EveryRegistryRankedAcyclic : Bool
r137EveryRegistryRankedAcyclic =
  all (r137RankedRegistry r137FirstRank)
    [r137S0, r137S1, r137S2, r137S3, r137S4, r137S5, r137S6,
     r137S7, r137S8, r137S9, r137S10, r137S11, r137S12, r137S13,
     r137S14, r137S15, r137S16, r137S17] &&
  all (r137RankedRegistry r137SecondRank)
    [r137S18, r137S19, r137S20, r137S21, r137S22, r137S23, r137S24]

public export
0 r137EveryRegistryRankedAcyclicTrue : r137EveryRegistryRankedAcyclic = True
r137EveryRegistryRankedAcyclicTrue = Refl

public export
0 r137FirstGenerationEdge : PrecedenceEdge r137NameEq ActorA ActorB r137S8
r137FirstGenerationEdge = MkPrecedenceEdge LinkKey r137FirstAActive
  r137FirstBBegun r137FirstAFoundAt8 r137FirstBFoundAt8 Here Here

public export
0 r137SecondGenerationEdge : PrecedenceEdge r137NameEq ActorB ActorA r137S22
r137SecondGenerationEdge = MkPrecedenceEdge LinkKey r137SecondBActive
  r137SecondABegun r137SecondBFoundAt22 r137SecondAFoundAt22 Here Here

public export
0 r137InstalledAAt5 : installedAt @{r137NameEq} ActorA r137S5 = True
r137InstalledAAt5 = Refl
public export
0 r137InstalledAAt6 : installedAt @{r137NameEq} ActorA r137S6 = True
r137InstalledAAt6 = Refl
public export
0 r137InstalledAAt7 : installedAt @{r137NameEq} ActorA r137S7 = True
r137InstalledAAt7 = Refl
public export
0 r137InstalledAAt8 : installedAt @{r137NameEq} ActorA r137S8 = True
r137InstalledAAt8 = Refl
public export
0 r137InstalledAAt9 : installedAt @{r137NameEq} ActorA r137S9 = True
r137InstalledAAt9 = Refl
public export
0 r137InstalledAAt10 : installedAt @{r137NameEq} ActorA r137S10 = True
r137InstalledAAt10 = Refl
public export
0 r137InstalledAAt11 : installedAt @{r137NameEq} ActorA r137S11 = True
r137InstalledAAt11 = Refl
public export
0 r137InstalledAAt12 : installedAt @{r137NameEq} ActorA r137S12 = True
r137InstalledAAt12 = Refl
public export
0 r137InstalledAAt13 : installedAt @{r137NameEq} ActorA r137S13 = True
r137InstalledAAt13 = Refl
public export
0 r137InstalledAAt14 : installedAt @{r137NameEq} ActorA r137S14 = True
r137InstalledAAt14 = Refl
public export
0 r137InstalledAAt15 : installedAt @{r137NameEq} ActorA r137S15 = True
r137InstalledAAt15 = Refl
