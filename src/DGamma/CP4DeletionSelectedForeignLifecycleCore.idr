module DGamma.CP4DeletionSelectedForeignLifecycleCore

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedForeignControlCore
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

0 lookupBindingFromEqualBindings :
  (keyEq : DecEq key) -> (wanted : key) ->
  (left, right : CoeffectContext key value) ->
  bindings left = bindings right ->
  lookupBinding @{keyEq} wanted left = lookupBinding @{keyEq} wanted right
lookupBindingFromEqualBindings keyEq wanted
  (MkCoeffectContext leftEntries leftUnique)
  (MkCoeffectContext rightEntries rightUnique) same =
    cong (lookupEntries @{keyEq} wanted) same

0 memberKeyFromEqualBindings :
  (keyEq : DecEq key) -> (wanted : key) ->
  (left, right : CoeffectContext key value) ->
  bindings left = bindings right ->
  memberKey @{keyEq} wanted left = memberKey @{keyEq} wanted right
memberKeyFromEqualBindings keyEq wanted left right same =
  cong isJust (lookupBindingFromEqualBindings keyEq wanted left right same)

0 lifecycleActiveSame : LifecycleControlRelated left right ->
  isActive left = isActive right
lifecycleActiveSame (InactiveControls outcome) = Refl
lifecycleActiveSame (ReloadingControls remaining accumulator view) = Refl
lifecycleActiveSame (ActiveControls accumulator view) = Refl
lifecycleActiveSame (UnloadingControls accumulator view outcome) = Refl

0 lifecycleInstalledSame : LifecycleControlRelated left right ->
  installed left = installed right
lifecycleInstalledSame (InactiveControls outcome) = Refl
lifecycleInstalledSame (ReloadingControls remaining accumulator view) = Refl
lifecycleInstalledSame (ActiveControls accumulator view) = Refl
lifecycleInstalledSame (UnloadingControls accumulator view outcome) = Refl

0 providerCandidate : DecEq key => key ->
  Fiber name key value world error -> Bool
providerCandidate wanted fiber =
  isActive (fiberLifecycle fiber) &&
  memberKey wanted (ownedValues (fiberTable fiber))

0 providerCandidateExplicit :
  (keyEq : DecEq key) -> (wanted : key) ->
  (fiber : Fiber name key value world error) ->
  providerCandidate @{keyEq} wanted fiber =
    isActive (fiberLifecycle fiber) &&
      memberKey @{keyEq} wanted (ownedValues (fiberTable fiber))
providerCandidateExplicit keyEq wanted fiber = Refl

0 foreignProviderCandidateSame :
  (keyEq : DecEq key) -> (wanted : key) ->
  {left, right : Fiber name key value world error} ->
  FiberControlRelated left right ->
  bindings (ownedValues (fiberTable left)) =
    bindings (ownedValues (fiberTable right)) ->
  providerCandidate @{keyEq} wanted left =
    providerCandidate @{keyEq} wanted right
foreignProviderCandidateSame keyEq wanted
  (FibersControlRelated leftParent rightParent leftRetired rightRetired
    leftTable rightTable leftLifecycle rightLifecycle parentSame retiredSame
    lifecycleSame) tablesSame =
      rewrite lifecycleActiveSame lifecycleSame in
      cong (isActive rightLifecycle &&)
        (memberKeyFromEqualBindings keyEq wanted (ownedValues leftTable)
          (ownedValues rightTable) tablesSame)

||| Runtime/control source relation needed by a retained foreign lifecycle step.
||| Foreign cells retain full controls and exact ordered table bindings.  At the
||| selected cell the survivor is known uninstalled/inactive, while the plan
||| cell is proved unable to provide any key declared by the foreign owner.
public export
data ForeignLifecycleSourceCellRelated :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected, current : name) -> (deps : List key) ->
  Fiber name key value world error -> Fiber name key value world error -> Type where
  SelectedLifecycleSourceCell :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected, current : name} -> {deps : List key} ->
    {left, right : Fiber name key value world error} ->
    current = selected ->
    FiberStaticRelated name key world error value left right ->
    installed (fiberLifecycle right) = False ->
    isActive (fiberLifecycle right) = False ->
    ((provider, self : name) ->
      reliedHead @{nameEq} provider self (Bind current right) = False) ->
    ((wanted : key) -> Elem wanted deps ->
      providerCandidate @{keyEq} wanted left = False) ->
    ForeignLifecycleSourceCellRelated name key world error value nameEq keyEq selected
      current deps left right
  ForeignLifecycleSourceCell :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected, current : name} -> {deps : List key} ->
    {left, right : Fiber name key value world error} ->
    Not (current = selected) ->
    FiberControlRelated left right ->
    bindings (ownedValues (fiberTable left)) =
      bindings (ownedValues (fiberTable right)) ->
    ((provider, self : name) ->
      reliedHead @{nameEq} provider self (Bind current left) =
        reliedHead @{nameEq} provider self (Bind current right)) ->
    ForeignLifecycleSourceCellRelated name key world error value nameEq keyEq selected
      current deps left right

public export
data ForeignLifecycleOrderedSourcesRelated :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) -> (deps : List key) ->
  List (Binding name (FiberAt name key value world error)) ->
  List (Binding name (FiberAt name key value world error)) -> Type where
  ForeignLifecycleSourcesNil :
    ForeignLifecycleOrderedSourcesRelated name key world error value nameEq keyEq selected
      deps [] []
  ForeignLifecycleSourcesCons :
    (current : name) ->
    ForeignLifecycleSourceCellRelated name key world error value nameEq keyEq selected
      current deps leftFiber rightFiber ->
    ForeignLifecycleOrderedSourcesRelated name key world error value nameEq keyEq selected
      deps leftRest rightRest ->
    ForeignLifecycleOrderedSourcesRelated name key world error value nameEq keyEq selected
      deps (Bind current leftFiber :: leftRest)
      (Bind current rightFiber :: rightRest)

||| Saturated guard frame consumed by rule-specific checked replay.  The ordered
||| source proof retains all data needed to derive these equalities from the
||| selected quotient; keeping the frame explicit separates the public
||| no-dependent-closing argument from evaluator branch reconstruction.
public export
record ForeignLifecycleGuardFrame
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (selected, actor : name) (deps : List key)
  (leftOwner, rightOwner : Fiber name key value world error)
  (left, right : Registry name key value world error) where
  constructor MkForeignLifecycleGuardFrame
  0 lifecycleGuardSources : ForeignLifecycleOrderedSourcesRelated name key
    world error value nameEq keyEq selected deps (bindings left) (bindings right)
  0 lifecycleOwnerControls : FiberControlRelated leftOwner rightOwner
  0 lifecycleRelianceFalse :
    relied @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} actor left = False ->
    relied @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} actor right = False

||| L-Begin installs identical declared continuations, identity accumulators,
||| and the target view proved equal by the guard frame.
public export
0 beginLifecycleControlRelated :
  {key, world, error, name : Type} -> {value : key -> Type} ->
  {deps : List key} -> {provision : CoeffectSpec key} ->
  (program : List (StepEffect key value world error deps provision)) ->
  (view : View name deps) ->
  LifecycleControlRelated
    (Reloading program (\input => input) view)
    (Reloading program (\input => input) view)
beginLifecycleControlRelated program view =
  ReloadingControls Refl (\input => localStateRuntimeReflexive input) Refl

||| The empty/nonempty finishing branch changes only Reloading to Active and
||| retains the already-related accumulator and committed view.
public export
0 finishLifecycleControlRelated :
  {key, world, error, name : Type} -> {value : key -> Type} ->
  {deps : List key} -> {provision : CoeffectSpec key} ->
  {leftRemaining, rightRemaining : List
    (StepEffect key value world error deps provision)} ->
  {leftAccumulator, rightAccumulator :
    LocalState key value world provision -> LocalState key value world provision} ->
  {leftView, rightView : View name deps} ->
  LifecycleControlRelated
    (Reloading leftRemaining leftAccumulator leftView)
    (Reloading rightRemaining rightAccumulator rightView) ->
  LifecycleControlRelated
    (Active {error = error} leftAccumulator leftView)
    (Active {error = error} rightAccumulator rightView)
finishLifecycleControlRelated {error}
  (ReloadingControls remainingSame accumulatorsSame viewsSame) =
    ActiveControls {error = error} accumulatorsSame viewsSame

||| Explicit L-Divert and effectful landing-divert retain the source
||| accumulator/view and install the same clean Unloading outcome.
public export
0 divertLifecycleControlRelated :
  LifecycleControlRelated
    (Reloading leftRemaining leftAccumulator leftView)
    (Reloading rightRemaining rightAccumulator rightView) ->
  LifecycleControlRelated (Unloading leftAccumulator leftView Nothing)
    (Unloading rightAccumulator rightView Nothing)
divertLifecycleControlRelated
  (ReloadingControls remainingSame accumulatorsSame viewsSame) =
    UnloadingControls accumulatorsSame viewsSame Refl

||| L-Leave is the Active analogue of diversion.
public export
0 leaveLifecycleControlRelated :
  LifecycleControlRelated (Active leftAccumulator leftView)
    (Active rightAccumulator rightView) ->
  LifecycleControlRelated (Unloading leftAccumulator leftView Nothing)
    (Unloading rightAccumulator rightView Nothing)
leaveLifecycleControlRelated (ActiveControls accumulatorsSame viewsSame) =
  UnloadingControls accumulatorsSame viewsSame Refl

||| L-Raise stores equal failure outcomes without pushing a yielded inverse.
public export
0 raiseLifecycleControlRelated :
  LifecycleControlRelated
    (Reloading leftRemaining leftAccumulator leftView)
    (Reloading rightRemaining rightAccumulator rightView) ->
  leftError = rightError ->
  LifecycleControlRelated
    (Unloading leftAccumulator leftView (Just leftError))
    (Unloading rightAccumulator rightView (Just rightError))
raiseLifecycleControlRelated
  (ReloadingControls remainingSame accumulatorsSame viewsSame) errorSame =
    UnloadingControls accumulatorsSame viewsSame (cong Just errorSame)

||| Successful L-Advance accumulator composition is supplied by the public
||| `pushLocalUndoRuntimeRelated` keystone.  Rule-specific replay instantiates
||| it from `IteratorYieldAgreement` before selecting Reloading/Active/Unloading.

||| L-Unload discards both related accumulators and resets the owner to the same
||| Inactive outcome; its restored tables remain entirely on the effect side.
public export
0 unloadLifecycleControlRelated :
  {key, world, error, name : Type} -> {value : key -> Type} ->
  {deps : List key} -> {provision : CoeffectSpec key} ->
  {leftAccumulator, rightAccumulator :
    LocalState key value world provision -> LocalState key value world provision} ->
  {leftView, rightView : View name deps} ->
  {leftOutcome, rightOutcome : Maybe error} ->
  LifecycleControlRelated
    (Unloading {key = key} {value = value} {world = world} {error = error}
      {name = name} {deps = deps} {provision = provision}
      leftAccumulator leftView leftOutcome)
    (Unloading {key = key} {value = value} {world = world} {error = error}
      {name = name} {deps = deps} {provision = provision}
      rightAccumulator rightView rightOutcome) ->
  LifecycleControlRelated
    (Inactive {key = key} {value = value} {world = world} {error = error}
      {name = name} {deps = deps} {provision = provision} leftOutcome)
    (Inactive {key = key} {value = value} {world = world} {error = error}
      {name = name} {deps = deps} {provision = provision} rightOutcome)
unloadLifecycleControlRelated
  (UnloadingControls accumulatorsSame viewsSame outcomesSame) =
    InactiveControls outcomesSame
