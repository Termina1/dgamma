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
