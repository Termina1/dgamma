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
