module DGamma.CP5O20ControlRebaseSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O20EpisodeSynchronizationSpike
import DGamma.CP5O20AllNameSynchronizationSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Primitive referenced-name transport, requiring agreement only on this
||| concrete finite list. No equality of functions or bijection records is used.
export
0 o20RebaseMappedNames :
  {name : Type} -> (before, after : NameBijection name) -> (names : List name) ->
  (0 agree : (selected : name) -> Elem selected names ->
    renameForward before selected = renameForward after selected) ->
  map (renameForward after) names = map (renameForward before) names
o20RebaseMappedNames before after [] agree = Refl
o20RebaseMappedNames before after (head :: rest) agree =
  rewrite sym (agree head Here) in
    cong (renameForward before head ::)
      (o20RebaseMappedNames before after rest (\selected, member => agree selected (There member)))

||| Parent re-renaming needs only the actually referenced parent name. Root
||| has no parent reference; no global current-name agreement is assumed.
export
0 o20RebaseParentReferences :
  {name : Type} -> (before, after : NameBijection name) ->
  (left, right : Parent name) ->
  (0 agreeParent : (selected : name) -> left = ChildOf selected ->
    renameForward before selected = renameForward after selected) ->
  ParentRelatedBy before left right -> ParentRelatedBy after left right
o20RebaseParentReferences before after Root Root agreeParent RootsRelated = RootsRelated
o20RebaseParentReferences before after (ChildOf parent) (ChildOf target) agreeParent (ChildrenRelated renamed) =
  ChildrenRelated (trans (sym (agreeParent parent Refl)) renamed)

||| Executable finite provider references carried by the actual control phase.
||| Inactive has none; Reloading/Active/Unloading retain their concrete view.
public export
o20LifecycleControlNames :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {deps : List key} -> {provision : CoeffectSpec key} ->
  Lifecycle key value world error name deps provision -> List name
o20LifecycleControlNames (Inactive outcome) = []
o20LifecycleControlNames (Reloading remaining accumulator view) = viewProviders view
o20LifecycleControlNames (Active accumulator view) = viewProviders view
o20LifecycleControlNames (Unloading accumulator view outcome) = viewProviders view

||| Rebase all four concrete control phases using only their actual provider
||| references. Programs, accumulators and outcomes are preserved unchanged.
export
0 o20RebaseLifecycleReferences :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {deps : List key} -> {provision : CoeffectSpec key} ->
  (before, after : NameBijection name) ->
  (left, right : Lifecycle key value world error name deps provision) ->
  (0 agreeProviders : (selected : name) -> Elem selected (o20LifecycleControlNames left) ->
    renameForward before selected = renameForward after selected) ->
  LifecycleRelatedBy before left right -> LifecycleRelatedBy after left right
o20RebaseLifecycleReferences before after (Inactive leftOutcome) (Inactive rightOutcome)
  agreeProviders (RenamedInactive outcomes) = RenamedInactive outcomes
o20RebaseLifecycleReferences before after (Reloading leftRemaining leftAccumulator leftView)
  (Reloading rightRemaining rightAccumulator rightView) agreeProviders (RenamedReloading remaining accumulators views) =
    RenamedReloading remaining accumulators
      (trans (o20RebaseMappedNames before after (viewProviders leftView) agreeProviders) views)
o20RebaseLifecycleReferences {error} before after (Active leftAccumulator leftView)
  (Active rightAccumulator rightView) agreeProviders (RenamedActive accumulators views) =
    RenamedActive {error = error} accumulators
      (trans (o20RebaseMappedNames before after (viewProviders leftView) agreeProviders) views)
o20RebaseLifecycleReferences before after (Unloading leftAccumulator leftView leftOutcome)
  (Unloading rightAccumulator rightView rightOutcome) agreeProviders (RenamedUnloading accumulators views outcomes) =
    RenamedUnloading accumulators
      (trans (o20RebaseMappedNames before after (viewProviders leftView) agreeProviders) views) outcomes

||| Full fiber control rebase, with separate NAMED primitive parent/provider
||| agreements. Neither agreement is silently inferred from current-name data.
export
0 o20RebaseFiberReferences :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (before, after : NameBijection name) ->
  (left, right : Fiber name key value world error) ->
  (0 agreeParent : (selected : name) -> fiberParent left = ChildOf selected ->
    renameForward before selected = renameForward after selected) ->
  (0 agreeProviders : (selected : name) -> Elem selected (o20LifecycleControlNames (fiberLifecycle left)) ->
    renameForward before selected = renameForward after selected) ->
  FiberRelatedBy before left right -> FiberRelatedBy after left right
o20RebaseFiberReferences before after _ _ agreeParent agreeProviders
  (RenamedFibers leftParent rightParent leftRetired rightRetired leftTable rightTable
    leftLifecycle rightLifecycle parents retired lifecycle) =
    RenamedFibers leftParent rightParent leftRetired rightRetired leftTable rightTable
      leftLifecycle rightLifecycle
      (o20RebaseParentReferences before after leftParent rightParent agreeParent parents)
      retired (o20RebaseLifecycleReferences before after leftLifecycle rightLifecycle agreeProviders lifecycle)

||| The old preimage of a new image equals the source name whenever the two
||| maps agree at THAT preimage. Bijection laws produce the exact equation.
export
0 o20RebasePreimageCurrent :
  {name : Type} -> (before, after : NameBijection name) -> (selected : name) ->
  (0 agreeCurrent :
    renameForward before (renameBackward before (renameForward after selected)) =
    renameForward after (renameBackward before (renameForward after selected))) ->
  renameBackward before (renameForward after selected) = selected
o20RebasePreimageCurrent before after selected agreeCurrent =
  trans (sym (renameLeftInverse after (renameBackward before (renameForward after selected))))
    (trans (cong (renameBackward after)
      (trans (sym agreeCurrent) (renameRightInverse before (renameForward after selected))))
      (renameLeftInverse after selected))

||| The old all-name relation transports actual absence without a domain oracle.
export
0 o20RebaseAbsentControlRight :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {renaming : NameBijection name} -> (right : Maybe (Fiber name key value world error)) ->
  MaybeFiberRelatedBy renaming Nothing right -> right = Nothing
o20RebaseAbsentControlRight _ RenamedAbsent = Refl

||| Observe the old preimage in the ACTUAL source registry. Its absent branch
||| uses the old cut; its present branch contradicts source absence using B6.
||| Agreement is needed only for present source entries, not all raw names.
export
0 o20RebaseAbsentObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (before, after : NameBijection name) ->
  (left, right : SystemState name key value world error) ->
  O20AllNameCut name key world error value nameEq before left right ->
  (0 agreeCurrent : (point : name) -> (fiber : Fiber name key value world error) ->
    lookupFiber {name} {key} {value} {world} {error} @{nameEq} point (registry left) = Just fiber ->
    renameForward before point = renameForward after point) ->
  (selected : name) -> (observed : Maybe (Fiber name key value world error)) ->
  (0 preimageFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq}
    (renameBackward before (renameForward after selected)) (registry left) = observed) ->
  (0 absent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry left) = Nothing) ->
  lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward after selected) (registry right) = Nothing
o20RebaseAbsentObserved {name} {key} {world} {error} {value} nameEq before after left right old agreeCurrent selected Nothing preimageFound absent =
  trans (sym (cong (\point => lookupFiber {name} {key} {value} {world} {error} @{nameEq} point (registry right))
    (renameRightInverse before (renameForward after selected))))
    (o20RebaseAbsentControlRight
      (lookupFiber {name} {key} {value} {world} {error} @{nameEq}
        (renameForward before (renameBackward before (renameForward after selected))) (registry right))
      (replace {p = \observed => MaybeFiberRelatedBy before observed
        (lookupFiber {name} {key} {value} {world} {error} @{nameEq}
          (renameForward before (renameBackward before (renameForward after selected))) (registry right))}
        preimageFound (allNameControls old (renameBackward before (renameForward after selected)))))
o20RebaseAbsentObserved {name} {key} {world} {error} {value} nameEq before after left right old agreeCurrent selected (Just fiber) preimageFound absent =
  void (nothingIsNotJust (trans (sym absent)
    (trans (sym (cong (\point => lookupFiber {name} {key} {value} {world} {error} @{nameEq} point (registry left))
      (o20RebasePreimageCurrent before after selected
        (agreeCurrent (renameBackward before (renameForward after selected)) fiber preimageFound)))) preimageFound)))

||| Discharge the observed-preimage equation by the actual lookup. No absent
||| target callback or second/backward domain-agreement premise is required.
export
0 o20RebaseAbsentDomain :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (before, after : NameBijection name) ->
  (left, right : SystemState name key value world error) ->
  O20AllNameCut name key world error value nameEq before left right ->
  (0 agreeCurrent : (point : name) -> (fiber : Fiber name key value world error) ->
    lookupFiber {name} {key} {value} {world} {error} @{nameEq} point (registry left) = Just fiber ->
    renameForward before point = renameForward after point) ->
  (selected : name) ->
  (0 absent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry left) = Nothing) ->
  lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward after selected) (registry right) = Nothing
o20RebaseAbsentDomain {name} {key} {world} {error} {value} nameEq before after left right old agreeCurrent selected absent =
  o20RebaseAbsentObserved nameEq before after left right old agreeCurrent selected
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq}
      (renameBackward before (renameForward after selected)) (registry left)) Refl absent

||| Consumer shape for an actually present source fiber. The old relation
||| owns the matching target fiber; no separately observed target is guessed.
export
0 o20RebasePresentMaybeReferences :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (before, after : NameBijection name) ->
  (left : Fiber name key value world error) ->
  (right : Maybe (Fiber name key value world error)) ->
  (0 agreeParent : (selected : name) -> fiberParent left = ChildOf selected ->
    renameForward before selected = renameForward after selected) ->
  (0 agreeProviders : (selected : name) -> Elem selected (o20LifecycleControlNames (fiberLifecycle left)) ->
    renameForward before selected = renameForward after selected) ->
  MaybeFiberRelatedBy before (Just left) right -> MaybeFiberRelatedBy after (Just left) right
o20RebasePresentMaybeReferences before after left _ agreeParent agreeProviders
  (RenamedPresent {right} related) =
    RenamedPresent (o20RebaseFiberReferences before after left right agreeParent agreeProviders related)

||| Actual observed-source partition. Current, parent and provider agreements
||| are three explicitly named primitive premises, never stored endpoint goals.
export
0 o20RebaseControlObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (before, after : NameBijection name) ->
  (left, right : SystemState name key value world error) ->
  O20AllNameCut name key world error value nameEq before left right ->
  (0 agreeCurrent : (point : name) -> (fiber : Fiber name key value world error) ->
    lookupFiber {name} {key} {value} {world} {error} @{nameEq} point (registry left) = Just fiber ->
    renameForward before point = renameForward after point) ->
  (0 agreeParent : (point : name) -> (fiber : Fiber name key value world error) ->
    lookupFiber {name} {key} {value} {world} {error} @{nameEq} point (registry left) = Just fiber ->
    (parent : name) -> fiberParent fiber = ChildOf parent ->
    renameForward before parent = renameForward after parent) ->
  (0 agreeProviders : (point : name) -> (fiber : Fiber name key value world error) ->
    lookupFiber {name} {key} {value} {world} {error} @{nameEq} point (registry left) = Just fiber ->
    (provider : name) -> Elem provider (o20LifecycleControlNames (fiberLifecycle fiber)) ->
    renameForward before provider = renameForward after provider) ->
  (selected : name) -> (observed : Maybe (Fiber name key value world error)) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry left) = observed) ->
  MaybeFiberRelatedBy after
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry left))
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward after selected) (registry right))
o20RebaseControlObserved nameEq before after left right old agreeCurrent agreeParent agreeProviders selected Nothing found =
  rewrite found in rewrite o20RebaseAbsentDomain nameEq before after left right old agreeCurrent selected found in RenamedAbsent
o20RebaseControlObserved {name} {key} {world} {error} {value} nameEq before after left right old agreeCurrent agreeParent agreeProviders selected (Just fiber) found =
  rewrite found in rewrite sym (agreeCurrent selected fiber found) in
    o20RebasePresentMaybeReferences before after fiber
      (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward before selected) (registry right))
      (agreeParent selected fiber found) (agreeProviders selected fiber found)
      (replace {p = \observed => MaybeFiberRelatedBy before observed
        (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward before selected) (registry right))}
        found (allNameControls old selected))
