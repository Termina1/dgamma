module DGamma.L2R4Localization

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5L2R1ExtendedZeroGap
import DGamma.L2R3Attached
import DGamma.L2R3AttachedGap
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| An actual checked root-insert occurrence at an exact physical ordinal.
||| The occurrence owns its native step and full trace decomposition; this is
||| not a tag-list assertion or an independently reconstructed system state.
public export
record RootInsertionAt
  (name, key, world, error : Type) (value : key -> Type)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState) (ordinal : Nat) where
  constructor MkRootInsertionAt
  insertedRoot : name
  insertedComponent : Component key value world error
  rootOccurrence : LocatedActionOccurrence (OInsert insertedRoot Root insertedComponent) trace
  0 rootOrdinal : locatedActionOrdinal rootOccurrence = ordinal

||| Lift the SAME native root occurrence through a checked front, transporting
||| its ordinal by count additivity (not equality of reconstructed states).
export
0 rootInsertionAfterPrefix :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (front : Transitions first middle) -> (trace : Transitions middle finalState) ->
  {ordinal : Nat} -> RootInsertionAt name key world error value trace ordinal ->
  RootInsertionAt name key world error value (appendTransitions front trace)
    (transitionCount front + ordinal)
rootInsertionAfterPrefix front trace found =
  MkRootInsertionAt (insertedRoot found) (insertedComponent found)
    (MkLocatedActionOccurrence
      (actionBeforeState (rootOccurrence found)) (actionAfterState (rootOccurrence found))
      (appendTransitions front (beforeActionOccurrence (rootOccurrence found)))
      (locatedTransition (rootOccurrence found)) (afterActionOccurrence (rootOccurrence found))
      (locatedAction (rootOccurrence found))
      (trans (appendTransitionsAssociative front (beforeActionOccurrence (rootOccurrence found))
        (MoreTransitions (locatedTransition (rootOccurrence found)) (afterActionOccurrence (rootOccurrence found))))
        (cong (appendTransitions front) (actionOccurrenceDecomposition (rootOccurrence found)))))
    (trans (extendedCountAppend front (beforeActionOccurrence (rootOccurrence found)))
      (cong (transitionCount front +) (rootOrdinal found)))

||| Extend a root occurrence's suffix without changing its native step or
||| ordinal. Associativity supplies the actual extended trace decomposition.
export
0 rootInsertionBeforeSuffix :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (trace : Transitions first middle) -> (back : Transitions middle finalState) ->
  {ordinal : Nat} -> RootInsertionAt name key world error value trace ordinal ->
  RootInsertionAt name key world error value (appendTransitions trace back) ordinal
rootInsertionBeforeSuffix trace back found =
  MkRootInsertionAt (insertedRoot found) (insertedComponent found)
    (MkLocatedActionOccurrence
      (actionBeforeState (rootOccurrence found)) (actionAfterState (rootOccurrence found))
      (beforeActionOccurrence (rootOccurrence found)) (locatedTransition (rootOccurrence found))
      (appendTransitions (afterActionOccurrence (rootOccurrence found)) back)
      (locatedAction (rootOccurrence found))
      (trans (sym (appendTransitionsAssociative (beforeActionOccurrence (rootOccurrence found))
        (MoreTransitions (locatedTransition (rootOccurrence found)) (afterActionOccurrence (rootOccurrence found))) back))
        (cong (\part => appendTransitions part back) (actionOccurrenceDecomposition (rootOccurrence found)))))
    (rootOrdinal found)

||| Select zero or successor in one root-headed trail. The successor premise
||| is the induction hypothesis, not an alternate operational edge oracle.
export
0 rootHeadOrdinal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (root : name) -> (component : Component key value world error) ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (0 inserted : transitionAction step = OInsert root Root component) ->
  (0 later : (n : Nat) -> LT n (transitionCount rest) ->
    RootInsertionAt name key world error value rest n) ->
  (ordinal : Nat) -> LT ordinal (S (transitionCount rest)) ->
  RootInsertionAt name key world error value (MoreTransitions step rest) ordinal
rootHeadOrdinal {first} {middle} root component step rest inserted later Z upper =
  MkRootInsertionAt root component
    (MkLocatedActionOccurrence first middle NoTransitions step rest inserted Refl) Refl
rootHeadOrdinal root component step rest inserted later (S n) upper =
  rootInsertionAfterPrefix (MoreTransitions step NoTransitions) rest
    (later n (fromLteSucc upper))

||| Induction on the actual ordered forced bundle: EVERY in-bounds ordinal
||| yields an actual checked root OInsert occurrence with producer-owned count
||| equation. No action-word or selected-catalog restriction is used.
export
0 orderedBundleRootAt :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {selected : name} ->
  {first, coreEnd, bundleStart, finalState : SystemState name key value world error} ->
  {core : Transitions first coreEnd} -> {priorRoots : List name} ->
  {bundle : Transitions bundleStart finalState} ->
  OrderedForcedRootBundle nameEq selected core priorRoots bundle ->
  (ordinal : Nat) -> LT ordinal (transitionCount bundle) ->
  RootInsertionAt name key world error value bundle ordinal
orderedBundleRootAt ForcedBundleEnd ordinal upper = absurd upper
orderedBundleRootAt (ForcedBundleStep root component step rest inserted forced tail) ordinal upper =
  rootHeadOrdinal root component step rest inserted (orderedBundleRootAt tail) ordinal upper

||| Lift an arbitrary local bundle position through its own core, opening,
||| prefix and suffix. All trace equations are the authenticated member/block
||| equations; only Nat count associativity changes the ordinal index.
export
0 attachedRootAtOffset :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, finalState : SystemState name key value world error} ->
  {global : Transitions first finalState} ->
  {action : Action name key value world error} -> {ordinal : Nat} ->
  (member : AttachedBundleOccurrence name key world error value nameEq keyEq global action ordinal) ->
  (local : Nat) -> LT local (transitionCount (memberBundle member)) ->
  RootInsertionAt name key world error value global (bundleOffset member + local)
attachedRootAtOffset member local upper =
  replace {p = RootInsertionAt _ _ _ _ _ _}
    (trans (plusAssociative (transitionCount (attachedBefore (containingBlock member)))
      (S (transitionCount (memberCore member))) local)
      (cong (+ local) (sym (offsetExact member))))
    (replace {p = \whole => RootInsertionAt _ _ _ _ _ whole
        (transitionCount (attachedBefore (containingBlock member)) + S (transitionCount (memberCore member) + local))}
      (attachedDecomposition (containingBlock member))
      (rootInsertionAfterPrefix (attachedBefore (containingBlock member))
        (MoreTransitions (beginTransition (attachedOpening (containingBlock member)))
          (appendTransitions (attachedBody (containingBlock member)) (attachedAfter (containingBlock member))))
        (rootInsertionAfterPrefix
          (MoreTransitions (beginTransition (attachedOpening (containingBlock member))) NoTransitions)
          (appendTransitions (attachedBody (containingBlock member)) (attachedAfter (containingBlock member)))
          (rootInsertionBeforeSuffix (attachedBody (containingBlock member)) (attachedAfter (containingBlock member))
            (replace {p = \body => RootInsertionAt _ _ _ _ _ body (transitionCount (memberCore member) + local)}
              (memberSplit member)
              (rootInsertionAfterPrefix (memberCore member) (memberBundle member)
                (orderedBundleRootAt (memberForced member) local upper)))))))
