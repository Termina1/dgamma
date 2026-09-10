module DGamma.CP5O19AttachedPairsSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Seven production forms at the EXACT native source transition. Bundle
||| evidence is indexed by its original core, never relabelled to a replay cut.
||| No guard, diamond, swapped trace, row or desired result is stored here.
public export
data O19AttachedEdge :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (actor : name) ->
  {coreFirst, coreLast : SystemState name key value world error} ->
  (core : Transitions coreFirst coreLast) ->
  {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> Type where
  AttachedLifecycle :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} ->
    {coreFirst, coreLast, before, afterState : SystemState name key value world error} ->
    {core : Transitions coreFirst coreLast} -> {step : Transition before afterState} ->
    (0 lifecycle : isLifecycleAction (transitionAction step) = True) ->
    (0 owned : transitionActor step = actor) ->
    O19AttachedEdge name key world error value nameEq actor core step
  AttachedChildInsert :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} ->
    {coreFirst, coreLast, before, afterState : SystemState name key value world error} ->
    {core : Transitions coreFirst coreLast} -> {step : Transition before afterState} ->
    (child : name) -> (component : Component key value world error) ->
    (0 inserted : transitionAction step = OInsert child (ChildOf actor) component) ->
    O19AttachedEdge name key world error value nameEq actor core step
  AttachedChildRetire :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} ->
    {coreFirst, coreLast, before, afterState : SystemState name key value world error} ->
    {core : Transitions coreFirst coreLast} -> {step : Transition before afterState} ->
    (controlled : name) -> (fiber : Fiber name key value world error) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} controlled (registry before) = Just fiber) ->
    (0 parent : fiberParent fiber = ChildOf actor) ->
    (0 controlledAction : transitionAction step = ORetire controlled) ->
    O19AttachedEdge name key world error value nameEq actor core step
  AttachedChildRemove :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} ->
    {coreFirst, coreLast, before, afterState : SystemState name key value world error} ->
    {core : Transitions coreFirst coreLast} -> {step : Transition before afterState} ->
    (controlled : name) -> (fiber : Fiber name key value world error) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} controlled (registry before) = Just fiber) ->
    (0 parent : fiberParent fiber = ChildOf actor) ->
    (0 controlledAction : transitionAction step = ORemove controlled) ->
    O19AttachedEdge name key world error value nameEq actor core step
  AttachedRootInsert :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} ->
    {coreFirst, coreLast, before, afterState : SystemState name key value world error} ->
    {core : Transitions coreFirst coreLast} -> {step : Transition before afterState} ->
    (root : name) -> (component : Component key value world error) ->
    (0 priorRoots : List name) ->
    (0 inserted : transitionAction step = OInsert root Root component) ->
    (0 forced : AttachedReason nameEq actor core priorRoots component) ->
    O19AttachedEdge name key world error value nameEq actor core step
  AttachedRootRetire :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} ->
    {coreFirst, coreLast, before, afterState : SystemState name key value world error} ->
    {core : Transitions coreFirst coreLast} -> {step : Transition before afterState} ->
    (controlled : name) -> (fiber : Fiber name key value world error) ->
    (0 priorRoots : List name) -> (0 bundled : Elem controlled priorRoots) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} controlled (registry before) = Just fiber) ->
    (0 parent : fiberParent fiber = Root) ->
    (0 controlledAction : transitionAction step = ORetire controlled) ->
    O19AttachedEdge name key world error value nameEq actor core step
  AttachedRootRemove :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} ->
    {coreFirst, coreLast, before, afterState : SystemState name key value world error} ->
    {core : Transitions coreFirst coreLast} -> {step : Transition before afterState} ->
    (controlled : name) -> (fiber : Fiber name key value world error) ->
    (0 priorRoots : List name) -> (0 bundled : Elem controlled priorRoots) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} controlled (registry before) = Just fiber) ->
    (0 parent : fiberParent fiber = Root) ->
    (0 controlledAction : transitionAction step = ORemove controlled) ->
    O19AttachedEdge name key world error value nameEq actor core step

||| Exact source-spine coverage, retaining the source state of EVERY control.
||| Erased classifications accompany executable native transition data.
public export
data O19AttachedScan :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (actor : name) ->
  {coreFirst, coreLast : SystemState name key value world error} ->
  (core : Transitions coreFirst coreLast) ->
  {first, last : SystemState name key value world error} ->
  Transitions first last -> Type where
  AttachedScanEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} ->
    {coreFirst, coreLast, state : SystemState name key value world error} ->
    {core : Transitions coreFirst coreLast} ->
    O19AttachedScan name key world error value nameEq actor core (NoTransitions {state})
  AttachedScanStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} ->
    {coreFirst, coreLast, first, middle, last : SystemState name key value world error} ->
    {core : Transitions coreFirst coreLast} ->
    (step : Transition first middle) -> (rest : Transitions middle last) ->
    (0 observed : O19AttachedEdge name key world error value nameEq actor core step) ->
    (0 tail : O19AttachedScan name key world error value nameEq actor core rest) ->
    O19AttachedScan name key world error value nameEq actor core (MoreTransitions step rest)

||| Total core observer. The context core index remains fixed through the scan;
||| all five native grammar constructors are visited without source relabelling.
export
0 o19AttachedCoreScan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  {coreFirst, coreLast, first, last : SystemState name key value world error} ->
  (core : Transitions coreFirst coreLast) -> (trace : Transitions first last) ->
  ActorLifecycleCore nameEq actor trace ->
  O19AttachedScan name key world error value nameEq actor core trace
o19AttachedCoreScan nameEq actor core _ CoreLifecycleEnd = AttachedScanEnd
o19AttachedCoreScan nameEq actor core _ (CoreLifecycleStep step rest lifecycle owned tail) =
  AttachedScanStep step rest (AttachedLifecycle lifecycle owned)
    (o19AttachedCoreScan nameEq actor core rest tail)
o19AttachedCoreScan nameEq actor core _ (CoreYieldedRegistrationStep {child} {component} step rest inserted tail) =
  AttachedScanStep step rest (AttachedChildInsert child component inserted)
    (o19AttachedCoreScan nameEq actor core rest tail)
o19AttachedCoreScan nameEq actor core _ (CoreChildRetireStep step rest child fiber found parent controlled tail) =
  AttachedScanStep step rest (AttachedChildRetire child fiber found parent controlled)
    (o19AttachedCoreScan nameEq actor core rest tail)
o19AttachedCoreScan nameEq actor core _ (CoreChildRemoveStep step rest child fiber found parent controlled tail) =
  AttachedScanStep step rest (AttachedChildRemove child fiber found parent controlled)
    (o19AttachedCoreScan nameEq actor core rest tail)

||| Total bundle observer preserves the EXACT core forcing reason and evolving
||| prior-root membership, in addition to native source lookup/parent facts.
export
0 o19AttachedBundleScan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  {coreFirst, coreLast, first, last : SystemState name key value world error} ->
  (core : Transitions coreFirst coreLast) -> (priorRoots : List name) ->
  (trace : Transitions first last) -> OrderedForcedRootBundle nameEq actor core priorRoots trace ->
  O19AttachedScan name key world error value nameEq actor core trace
o19AttachedBundleScan nameEq actor core priorRoots _ ForcedBundleEnd = AttachedScanEnd
o19AttachedBundleScan nameEq actor core priorRoots _ (ForcedBundleInsert root component step rest inserted forced tail) =
  AttachedScanStep step rest (AttachedRootInsert root component priorRoots inserted forced)
    (o19AttachedBundleScan nameEq actor core (root :: priorRoots) rest tail)
o19AttachedBundleScan nameEq actor core priorRoots _ (ForcedBundleRetire root fiber step rest bundled found parent controlled tail) =
  AttachedScanStep step rest (AttachedRootRetire root fiber priorRoots bundled found parent controlled)
    (o19AttachedBundleScan nameEq actor core priorRoots rest tail)
o19AttachedBundleScan nameEq actor core priorRoots _ (ForcedBundleRemove root fiber step rest bundled found parent controlled tail) =
  AttachedScanStep step rest (AttachedRootRemove root fiber priorRoots bundled found parent controlled)
    (o19AttachedBundleScan nameEq actor core priorRoots rest tail)

||| Compose scans along the actual dependent append, keeping the SAME original
||| core index. No equality between independently replayed states is needed.
export
0 o19AttachedScanAppend :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {actor : name} ->
  {coreFirst, coreLast, first, middle, last : SystemState name key value world error} ->
  {core : Transitions coreFirst coreLast} ->
  (leading : Transitions first middle) -> (trailing : Transitions middle last) ->
  O19AttachedScan name key world error value nameEq actor core leading ->
  O19AttachedScan name key world error value nameEq actor core trailing ->
  O19AttachedScan name key world error value nameEq actor core (appendTransitions leading trailing)
o19AttachedScanAppend _ trailing AttachedScanEnd rest = rest
o19AttachedScanAppend _ trailing (AttachedScanStep step tail observed scanned) rest =
  AttachedScanStep step (appendTransitions tail trailing) observed
    (o19AttachedScanAppend tail trailing scanned rest)

||| Both production body shapes retain the actual original core. A bundled
||| scan is indexed by the literal native core/bundle append, not a copied word.
public export
data O19AttachedBody :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (actor : name) ->
  {first, last : SystemState name key value world error} ->
  Transitions first last -> Type where
  ObservedCoreBody :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} ->
    {first, last : SystemState name key value world error} ->
    (core : Transitions first last) ->
    (0 scanned : O19AttachedScan name key world error value nameEq actor core core) ->
    O19AttachedBody name key world error value nameEq actor core
  ObservedBundledBody :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} ->
    {first, coreLast, last : SystemState name key value world error} ->
    (core : Transitions first coreLast) -> (bundle : Transitions coreLast last) ->
    (0 scanned : O19AttachedScan name key world error value nameEq actor core (appendTransitions core bundle)) ->
    O19AttachedBody name key world error value nameEq actor (appendTransitions core bundle)

||| TOTAL observer of the complete production grammar: no LegacyActorOnly,
||| zero-gap, empty-bundle, replay-domain or final-result premise is required.
export
0 o19ObserveAttachedBody :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  {first, last : SystemState name key value world error} ->
  (body : Transitions first last) -> ActorLifecycleOnly nameEq actor body ->
  O19AttachedBody name key world error value nameEq actor body
o19ObserveAttachedBody nameEq actor _ (ActorWithoutForcedRoots core shape) =
  ObservedCoreBody core (o19AttachedCoreScan nameEq actor core core shape)
o19ObserveAttachedBody nameEq actor _ (ActorWithForcedRoots core shape bundle ordered) =
  ObservedBundledBody core bundle
    (o19AttachedScanAppend core bundle (o19AttachedCoreScan nameEq actor core core shape)
      (o19AttachedBundleScan nameEq actor core [] bundle ordered))

||| Select the exact native edge, not an equal action at a different source
||| cut. Thus lookup/parent evidence still refers to the selected edge's before.
export
0 o19AttachedScanOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {actor : name} ->
  {coreFirst, coreLast, first, last, before, afterState : SystemState name key value world error} ->
  {core : Transitions coreFirst coreLast} -> {trace : Transitions first last} ->
  (step : Transition before afterState) ->
  O19AttachedScan name key world error value nameEq actor core trace ->
  OccursIn step trace -> O19AttachedEdge name key world error value nameEq actor core step
o19AttachedScanOccurrence step (AttachedScanStep _ _ observed tail) OccursHere = observed
o19AttachedScanOccurrence step (AttachedScanStep _ _ observed tail) (OccursLater there) =
  o19AttachedScanOccurrence step tail there

||| Source-state-indexed body occurrence observation retains its ACTUAL core
||| witness. Existentials expose original data; they do not assert replay facts.
export
0 o19AttachedBodyOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {actor : name} ->
  {first, last, before, afterState : SystemState name key value world error} ->
  {trace : Transitions first last} -> (step : Transition before afterState) ->
  O19AttachedBody name key world error value nameEq actor trace ->
  OccursIn step trace ->
  (coreLast : SystemState name key value world error **
    (core : Transitions first coreLast ** O19AttachedEdge name key world error value nameEq actor core step))
o19AttachedBodyOccurrence step (ObservedCoreBody {last} core scanned) occurrence =
  (last ** (core ** o19AttachedScanOccurrence step scanned occurrence))
o19AttachedBodyOccurrence step (ObservedBundledBody {coreLast} core bundle scanned) occurrence =
  (coreLast ** (core ** o19AttachedScanOccurrence step scanned occurrence))

||| Cartesian PRODUCT of the seven native source classes: all 49 combinations
||| are represented, without assuming any pair commutes. Each side retains its
||| original core and exact native occurrence; source cuts need not be adjacent.
public export
record O19AttachedSourcePair
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (leftActor, rightActor : name)
  {leftFirst, leftLast, rightFirst, rightLast, leftBefore, leftAfter,
   rightBefore, rightAfter : SystemState name key value world error}
  (leftBody : Transitions leftFirst leftLast) (rightBody : Transitions rightFirst rightLast)
  (left : Transition leftBefore leftAfter) (right : Transition rightBefore rightAfter) where
  constructor MkO19AttachedSourcePair
  leftCoreLast : SystemState name key value world error
  rightCoreLast : SystemState name key value world error
  leftOriginalCore : Transitions leftFirst leftCoreLast
  rightOriginalCore : Transitions rightFirst rightCoreLast
  0 leftSourceMember : OccursIn left leftBody
  0 rightSourceMember : OccursIn right rightBody
  0 leftSourceClass : O19AttachedEdge name key world error value nameEq leftActor leftOriginalCore left
  0 rightSourceClass : O19AttachedEdge name key world error value nameEq rightActor rightOriginalCore right

||| Unconditional TOTAL pair observer for the admitted production bodies.
||| No shape restriction, guessed lookup, guard, swapped result or global
||| commuting assumption enters the source observation.
export
0 o19ObserveAttachedPair :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (leftActor, rightActor : name) ->
  {leftFirst, leftLast, rightFirst, rightLast, leftBefore, leftAfter,
   rightBefore, rightAfter : SystemState name key value world error} ->
  (leftBody : Transitions leftFirst leftLast) -> (rightBody : Transitions rightFirst rightLast) ->
  ActorLifecycleOnly nameEq leftActor leftBody -> ActorLifecycleOnly nameEq rightActor rightBody ->
  (left : Transition leftBefore leftAfter) -> (right : Transition rightBefore rightAfter) ->
  OccursIn left leftBody -> OccursIn right rightBody ->
  O19AttachedSourcePair name key world error value nameEq leftActor rightActor leftBody rightBody left right
o19ObserveAttachedPair nameEq leftActor rightActor leftBody rightBody leftShape rightShape left right leftIn rightIn =
  case o19AttachedBodyOccurrence left (o19ObserveAttachedBody nameEq leftActor leftBody leftShape) leftIn of
    (leftEnd ** (leftCore ** leftClass)) =>
      case o19AttachedBodyOccurrence right (o19ObserveAttachedBody nameEq rightActor rightBody rightShape) rightIn of
        (rightEnd ** (rightCore ** rightClass)) =>
          MkO19AttachedSourcePair leftEnd rightEnd leftCore rightCore leftIn rightIn leftClass rightClass

||| Executable seven-way source tag; the product of two tags names every
||| A10/A12 matrix entry explicitly, including all root/control orientations.
public export
data O19AttachedForm = ActorLifecycleForm | ChildInsertForm | ChildRetireForm |
  ChildRemoveForm | ForcedRootInsertForm | BundledRootRetireForm | BundledRootRemoveForm

||| Erased equations/metadata are not inspected to compute a source form.
public export
o19AttachedForm :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {actor : name} ->
  {coreFirst, coreLast, before, afterState : SystemState name key value world error} ->
  {core : Transitions coreFirst coreLast} -> {step : Transition before afterState} ->
  O19AttachedEdge name key world error value nameEq actor core step -> O19AttachedForm
o19AttachedForm (AttachedLifecycle lifecycle owned) = ActorLifecycleForm
o19AttachedForm (AttachedChildInsert child component inserted) = ChildInsertForm
o19AttachedForm (AttachedChildRetire child fiber found parent controlled) = ChildRetireForm
o19AttachedForm (AttachedChildRemove child fiber found parent controlled) = ChildRemoveForm
o19AttachedForm (AttachedRootInsert root component priorRoots inserted forced) = ForcedRootInsertForm
o19AttachedForm (AttachedRootRetire root fiber priorRoots bundled found parent controlled) = BundledRootRetireForm
o19AttachedForm (AttachedRootRemove root fiber priorRoots bundled found parent controlled) = BundledRootRemoveForm

||| Root inputs at both heads MUST have the same exact action. Neither may be
||| silently skipped. This is the external-order premise of frozen suffix replay.
export
0 o19AttachedRootHeadsSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {leftFirst, leftMiddle, leftLast, rightFirst, rightMiddle, rightLast : SystemState name key value world error} ->
  (left : Transition leftFirst leftMiddle) -> (right : Transition rightFirst rightMiddle) ->
  (leftRest : Transitions leftMiddle leftLast) -> (rightRest : Transitions rightMiddle rightLast) ->
  RootOrchestrationStep nameEq left -> RootOrchestrationStep nameEq right ->
  SameExternalOrchestration nameEq (MoreTransitions left leftRest) (MoreTransitions right rightRest) ->
  transitionAction left = transitionAction right
o19AttachedRootHeadsSame left right leftRest rightRest leftRoot rightRoot
  (SkipLeftInternal _ _ excluded tail) = void (excluded leftRoot)
o19AttachedRootHeadsSame left right leftRest rightRest leftRoot rightRoot
  (SkipRightInternal _ _ excluded tail) = void (excluded rightRoot)
o19AttachedRootHeadsSame left right leftRest rightRest leftRoot rightRoot
  (MatchExternalInput action _ _ _ _ _ _ leftExact rightExact tail) = trans leftExact (sym rightExact)

||| Every distinct-root-action crossing is an ACTUAL obstruction to the frozen
||| pairExternalOrder premise, regardless of local effect commutation. This
||| does not assert that such a pair is sanctioned by whole-block safety.
export
0 o19AttachedRootOrderObstruction :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {first, middle, last, movedFirst, movedMiddle, movedLast : SystemState name key value world error} ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  (movedRight : Transition movedFirst movedMiddle) -> (movedLeft : Transition movedMiddle movedLast) ->
  RootOrchestrationStep nameEq left -> RootOrchestrationStep nameEq movedRight ->
  (transitionAction movedRight = transitionAction right) ->
  Not (transitionAction left = transitionAction right) ->
  Not (SameExternalOrchestration nameEq (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions movedRight (MoreTransitions movedLeft NoTransitions)))
o19AttachedRootOrderObstruction left right movedRight movedLeft leftRoot movedRoot movedAction distinct relation =
  distinct (trans (o19AttachedRootHeadsSame left movedRight
    (MoreTransitions right NoTransitions) (MoreTransitions movedLeft NoTransitions) leftRoot movedRoot relation) movedAction)

||| Native root orchestration excludes lifecycle, including both root controls.
export
0 o19AttachedRootNonLifecycle :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {before, afterState : SystemState name key value world error} ->
  {step : Transition before afterState} -> RootOrchestrationStep nameEq step ->
  isLifecycleAction (transitionAction step) = False
o19AttachedRootNonLifecycle (RootInsertStep exact) = trans (cong isLifecycleAction exact) Refl
o19AttachedRootNonLifecycle (RootRetireStep fiber found parent exact) = trans (cong isLifecycleAction exact) Refl
o19AttachedRootNonLifecycle (RootRemoveStep fiber found parent exact) = trans (cong isLifecycleAction exact) Refl

||| TOTAL ORIGINAL-source external/internal classification. The child-control
||| branches compare native lookups at the SAME before state. This is why an
||| action-only relabelling of the R206 word observation could not prove it.
export
0 o19AttachedExternalKind :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {actor : name} ->
  {coreFirst, coreLast, before, afterState : SystemState name key value world error} ->
  {core : Transitions coreFirst coreLast} -> {step : Transition before afterState} ->
  O19AttachedEdge name key world error value nameEq actor core step ->
  Either (Not (RootOrchestrationStep nameEq step)) (RootOrchestrationStep nameEq step)
o19AttachedExternalKind (AttachedLifecycle lifecycle owned) =
  Left (\root => void (uninhabited (trans (sym lifecycle) (o19AttachedRootNonLifecycle root))))
o19AttachedExternalKind (AttachedChildInsert child component inserted) = Left (\root => case root of
  RootInsertStep exact => case trans (sym inserted) exact of Refl impossible
  RootRetireStep fiber found parent exact => case trans (sym inserted) exact of Refl impossible
  RootRemoveStep fiber found parent exact => case trans (sym inserted) exact of Refl impossible)
o19AttachedExternalKind (AttachedChildRetire child fiber found parent controlled) = Left (\root => case root of
  RootInsertStep exact => case trans (sym controlled) exact of Refl impossible
  RootRetireStep rootFiber rootFound rootParent exact =>
    case cong actionOwner (trans (sym controlled) exact) of
      Refl => case justInjective (trans (sym found) rootFound) of
        Refl => case trans (sym parent) rootParent of Refl impossible
  RootRemoveStep rootFiber rootFound rootParent exact => case trans (sym controlled) exact of Refl impossible)
o19AttachedExternalKind (AttachedChildRemove child fiber found parent controlled) = Left (\root => case root of
  RootInsertStep exact => case trans (sym controlled) exact of Refl impossible
  RootRetireStep rootFiber rootFound rootParent exact => case trans (sym controlled) exact of Refl impossible
  RootRemoveStep rootFiber rootFound rootParent exact =>
    case cong actionOwner (trans (sym controlled) exact) of
      Refl => case justInjective (trans (sym found) rootFound) of
        Refl => case trans (sym parent) rootParent of Refl impossible)
o19AttachedExternalKind (AttachedRootInsert root component priorRoots inserted forced) = Right (RootInsertStep inserted)
o19AttachedExternalKind (AttachedRootRetire root fiber priorRoots bundled found parent controlled) =
  Right (RootRetireStep fiber found parent controlled)
o19AttachedExternalKind (AttachedRootRemove root fiber priorRoots bundled found parent controlled) =
  Right (RootRemoveStep fiber found parent controlled)

||| All six non-lifecycle production forms are genuine paper orchestration.
||| The negative lifecycle premise only selects the corresponding source class.
export
0 o19AttachedOrchestration :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {actor : name} ->
  {coreFirst, coreLast, before, afterState : SystemState name key value world error} ->
  {core : Transitions coreFirst coreLast} -> {step : Transition before afterState} ->
  O19AttachedEdge name key world error value nameEq actor core step ->
  Not (isLifecycleAction (transitionAction step) = True) -> PaperOrchestrationStep step
o19AttachedOrchestration (AttachedLifecycle lifecycle owned) excluded = void (excluded lifecycle)
o19AttachedOrchestration (AttachedChildInsert child component inserted) excluded = PaperInsertStep inserted
o19AttachedOrchestration (AttachedChildRetire child fiber found parent controlled) excluded = PaperRetireStep controlled
o19AttachedOrchestration (AttachedChildRemove child fiber found parent controlled) excluded = PaperRemoveStep controlled
o19AttachedOrchestration (AttachedRootInsert root component priorRoots inserted forced) excluded = PaperInsertStep inserted
o19AttachedOrchestration (AttachedRootRetire root fiber priorRoots bundled found parent controlled) excluded = PaperRetireStep controlled
o19AttachedOrchestration (AttachedRootRemove root fiber priorRoots bundled found parent controlled) excluded = PaperRemoveStep controlled

||| Expanded A/O local theorem: all six attached orchestration forms consume
||| the SAME frozen diamond surface. Owner/licensing/independence premises are
||| explicit primitive obligations, not yet consequences of block safety.
export
0 o19AttachedActivationOrchestrationDiamond :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {actor : name} -> {coreFirst, coreLast, first, middle, last : SystemState name key value world error} ->
  {core : Transitions coreFirst coreLast} ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  PaperActivationStep left -> O19AttachedEdge name key world error value nameEq actor core right ->
  Not (isLifecycleAction (transitionAction right) = True) ->
  Not (transitionActor left = transitionActor right) ->
  ((child, parent : name) -> (component : Component key value world error) ->
    transitionAction right = OInsert child (ChildOf parent) component -> Not (transitionActor left = parent)) ->
  registryWellFormed @{nameEq} @{keyEq} first = True ->
  TraceIndependent name key world error value keyEq (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
o19AttachedActivationOrchestrationDiamond nameEq keyEq left right aligned activation observed notLifecycle distinct licensing wellFormed independent =
  activationOrchestrationDiamondSpike nameEq keyEq left right aligned activation
    (o19AttachedOrchestration observed notLifecycle) distinct licensing wellFormed independent

||| Expanded O/A local theorem, including both child controls and all bundle
||| forms. The early activation and its source agreement remain REAL premises;
||| source labels alone never transport a guard to the pre-orchestration cut.
export
0 o19AttachedOrchestrationActivationDiamond :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {actor : name} -> {coreFirst, coreLast, first, middle, last, earlyLast : SystemState name key value world error} ->
  {core : Transitions coreFirst coreLast} ->
  (left : Transition first middle) -> (right : Transition middle last) -> (earlyRight : Transition first earlyLast) ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions earlyRight NoTransitions) ->
  transitionAction earlyRight = transitionAction right -> transitionTag earlyRight = transitionTag right ->
  O19AttachedEdge name key world error value nameEq actor core left ->
  Not (isLifecycleAction (transitionAction left) = True) -> PaperActivationStep right ->
  Not (transitionActor left = transitionActor right) ->
  ((child : name) -> (parent : Parent name) -> (component : Component key value world error) ->
    transitionAction left = OInsert child parent component -> Not (transitionActor right = child)) ->
  ((child, parent : name) -> (component : Component key value world error) ->
    transitionAction left = OInsert child (ChildOf parent) component -> Not (transitionActor right = parent)) ->
  registryWellFormed @{nameEq} @{keyEq} first = True ->
  TraceIndependent name key world error value keyEq (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
o19AttachedOrchestrationActivationDiamond nameEq keyEq left right earlyRight aligned earlyAligned sameAction sameTag observed notLifecycle activation distinct childSafe parentSafe wellFormed independent =
  orchestrationActivationDiamondSpike nameEq keyEq left right earlyRight aligned earlyAligned sameAction sameTag
    (o19AttachedOrchestration observed notLifecycle) activation distinct childSafe parentSafe wellFormed independent

||| Expanded O/O local theorem covers all 36 insertion/control products. The
||| frozen safety package still owns actual early applicability, generation
||| scan, freshness and licensing; none is smuggled into source observation.
||| Local diamonds alone do NOT supply the root external-order premise.
export
0 o19AttachedOrchestrationDiamond :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {leftActor, rightActor : name} ->
  {leftCoreFirst, leftCoreLast, rightCoreFirst, rightCoreLast, first, middle, last : SystemState name key value world error} ->
  {leftCore : Transitions leftCoreFirst leftCoreLast} -> {rightCore : Transitions rightCoreFirst rightCoreLast} ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  O19AttachedEdge name key world error value nameEq leftActor leftCore left ->
  O19AttachedEdge name key world error value nameEq rightActor rightCore right ->
  Not (isLifecycleAction (transitionAction left) = True) -> Not (isLifecycleAction (transitionAction right) = True) ->
  Not (transitionActor left = transitionActor right) ->
  (safety : OrchestrationSwapSafety name key world error value protocol nameEq keyEq left right) ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions (earlyRight safety) NoTransitions) ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
o19AttachedOrchestrationDiamond nameEq keyEq protocol left right aligned leftClass rightClass leftNotLife rightNotLife distinct safety earlyAligned =
  orchestrationOrchestrationDiamondSpike nameEq keyEq protocol left right aligned
    (o19AttachedOrchestration leftClass leftNotLife) (o19AttachedOrchestration rightClass rightNotLife)
    distinct safety earlyAligned
