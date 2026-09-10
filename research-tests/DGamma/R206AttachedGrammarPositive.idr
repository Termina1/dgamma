module DGamma.R206AttachedGrammarPositive

import DGamma.Core
import DGamma.Effects
import DGamma.Unified
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.Section3Example
import DGamma.CP5O19OriginalBlockClassSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5ConfluenceRankObservationSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Actual source: root parent0 and its retired inactive child1, which owns
||| ServiceA. This fixture proves a body grammar, not a full sanctioned block.
public export
r206ReleaseSource : SystemState Nat ToyKey ToyValue ToyRuntime String
r206ReleaseSource = MkSystemState (MkToyRuntime False False)
  (insertBinding @{the (DecEq Nat) %search} 1
    (retireFiber (freshFiber DGamma.CalculusChecks.providerComponent (ChildOf 0)))
    (insertBinding @{the (DecEq Nat) %search} 0
      (freshFiber DGamma.CalculusChecks.failingComponent Root) emptyContext Refl) Refl)

||| Removing the child frees its provision key; the root parent stays present.
public export
r206Released : SystemState Nat ToyKey ToyValue ToyRuntime String
r206Released = MkSystemState (MkToyRuntime False False)
  (deleteBinding @{the (DecEq Nat) %search} 1 (registry r206ReleaseSource))

||| Native checked O-Remove, not a fabricated transition or bare action label.
public export
r206ReleaseEdge : Transition r206ReleaseSource r206Released
r206ReleaseEdge = Fired (the (DecEq Nat) %search) (the (DecEq ToyKey) %search)
  (ORemove 1) ORemoveTag Refl

||| A new root2 declares precisely the newly freed ServiceA provision.
public export
r206RootInserted : SystemState Nat ToyKey ToyValue ToyRuntime String
r206RootInserted = MkSystemState (MkToyRuntime False False)
  (insertBinding @{the (DecEq Nat) %search} 2
    (freshFiber DGamma.CalculusChecks.providerComponent Root) (registry r206Released) Refl)

||| The forced insertion is an actual checked root input.
public export
r206RootInsertEdge : Transition r206Released r206RootInserted
r206RootInsertEdge = Fired (the (DecEq Nat) %search) (the (DecEq ToyKey) %search)
  (OInsert 2 Root DGamma.CalculusChecks.providerComponent) OInsertTag Refl

||| Same-bundle root retirement preserves its actual Root parent metadata.
public export
r206RootRetired : SystemState Nat ToyKey ToyValue ToyRuntime String
r206RootRetired = MkSystemState (MkToyRuntime False False)
  (replaceBinding @{the (DecEq Nat) %search} 2
    (retireFiber (freshFiber DGamma.CalculusChecks.providerComponent Root)) (registry r206RootInserted))

||| Native checked same-bundle O-Retire.
public export
r206RootRetireEdge : Transition r206RootInserted r206RootRetired
r206RootRetireEdge = Fired (the (DecEq Nat) %search) (the (DecEq ToyKey) %search)
  (ORetire 2) ORetireTag Refl

||| Native checked same-bundle O-Remove; the exact evaluator destination is
||| retained instead of assuming it equals an independently rebuilt context.
public export
r206RootRemoveEdge : Transition r206RootRetired
  (MkSystemState (MkToyRuntime False False)
    (deleteBinding @{the (DecEq Nat) %search} 2 (registry r206RootRetired)))
r206RootRemoveEdge = Fired (the (DecEq Nat) %search) (the (DecEq ToyKey) %search)
  (ORemove 2) ORemoveTag Refl

||| Nonempty attached production body: actual child Remove, forced root Insert,
||| root Retire, root Remove. Empty initial root history and KeyReleased are
||| constructed from the actual core occurrence, not assumed by the caller.
export
0 r206AttachedControlsShape : ActorLifecycleOnly (the (DecEq Nat) %search) 0
  (MoreTransitions r206ReleaseEdge (MoreTransitions r206RootInsertEdge
    (MoreTransitions r206RootRetireEdge (MoreTransitions r206RootRemoveEdge NoTransitions))))
r206AttachedControlsShape = ActorWithForcedRoots
  (MoreTransitions r206ReleaseEdge NoTransitions)
  (CoreChildRemoveStep r206ReleaseEdge NoTransitions 1
    (retireFiber (freshFiber DGamma.CalculusChecks.providerComponent (ChildOf 0)))
    Refl Refl Refl CoreLifecycleEnd)
  (MoreTransitions r206RootInsertEdge (MoreTransitions r206RootRetireEdge
    (MoreTransitions r206RootRemoveEdge NoTransitions)))
  (ForcedBundleInsert 2 DGamma.CalculusChecks.providerComponent r206RootInsertEdge
    (MoreTransitions r206RootRetireEdge (MoreTransitions r206RootRemoveEdge NoTransitions)) Refl
    (KeyReleased (MkAttachedRelease 1
      (retireFiber (freshFiber DGamma.CalculusChecks.providerComponent (ChildOf 0)))
      (MkLocatedActionOccurrence r206ReleaseSource r206Released NoTransitions
        r206ReleaseEdge NoTransitions Refl Refl)
      Refl Refl ServiceA Here Here))
    (ForcedBundleRetire 2 (freshFiber DGamma.CalculusChecks.providerComponent Root)
      r206RootRetireEdge (MoreTransitions r206RootRemoveEdge NoTransitions)
      Here Refl Refl Refl
      (ForcedBundleRemove 2 (retireFiber (freshFiber DGamma.CalculusChecks.providerComponent Root))
        r206RootRemoveEdge NoTransitions Here Refl Refl Refl ForcedBundleEnd)))

||| Apply the total expanded word theorem to ALL four actual edges. Forbidden1
||| is genuinely controlled at the head despite authentic NoGeneratedChild1.
export
0 r206AttachedWords :
  (action : Action Nat ToyKey ToyValue ToyRuntime String) ->
  Elem action (o19ActionWord
    (MoreTransitions r206ReleaseEdge (MoreTransitions r206RootInsertEdge
      (MoreTransitions r206RootRetireEdge (MoreTransitions r206RootRemoveEdge NoTransitions))))) ->
  O19ExpandedBlockWordObservation Nat ToyKey ToyRuntime String ToyValue
    (the (DecEq Nat) %search) 0 1 action
r206AttachedWords = o19ExpandedOwnedSafeWord (the (DecEq Nat) %search) 0 1
  (MoreTransitions r206ReleaseEdge (MoreTransitions r206RootInsertEdge
    (MoreTransitions r206RootRetireEdge (MoreTransitions r206RootRemoveEdge NoTransitions))))
  r206AttachedControlsShape
  (NoGeneratedChildStep _ _ (\parent, component, same => case same of Refl impossible)
    (NoGeneratedChildStep _ _ (\parent, component, same => case same of Refl impossible)
      (NoGeneratedChildStep _ _ (\parent, component, same => case same of Refl impossible)
        (NoGeneratedChildStep _ _ (\parent, component, same => case same of Refl impossible) NoGeneratedChildEnd))))
