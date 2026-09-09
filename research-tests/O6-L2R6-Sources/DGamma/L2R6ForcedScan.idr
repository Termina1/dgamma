module DGamma.L2R6ForcedScan

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R3ForcedClosure
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Declaration overlap is eligible only for a child fiber, never a root.
||| Both sides use declared provisions, independent of lifecycle/table state.
public export
childDeclaredOverlap : {name, key, world, error : Type} -> {value : key -> Type} ->
  DecEq key -> Component key value world error -> Parent name -> Component key value world error -> Bool
childDeclaredOverlap keyEq root Root child = False
childDeclaredOverlap keyEq root (ChildOf parent) child =
  provisionOverlap @{keyEq} (componentProvisions child) (componentProvisions root)

||| An absent fiber cannot release a declaration. Present fibers delegate to
||| the explicit parent classifier; no activity or retirement test is used.
public export
foundChildOverlap : {name, key, world, error : Type} -> {value : key -> Type} ->
  DecEq key -> Component key value world error -> Maybe (Fiber name key value world error) -> Bool
foundChildOverlap keyEq root Nothing = False
foundChildOverlap keyEq root (Just fiber) =
  childDeclaredOverlap keyEq root (fiberParent fiber) (fiberComponent fiber)

||| Only an actual ORemove of an installed child sharing a declared key is a
||| release. The native transition supplies the source; other tags reject.
public export
ownChildReleaseStep : {name, key, world, error : Type} -> {value : key -> Type} ->
  DecEq name -> DecEq key -> Component key value world error ->
  SystemState name key value world error -> Action name key value world error -> Bool
ownChildReleaseStep nameEq keyEq root source (OInsert actor parent component) = False
ownChildReleaseStep nameEq keyEq root source (ORetire actor) = False
ownChildReleaseStep {name} {key} {world} {error} {value} nameEq keyEq root source (ORemove child) =
  foundChildOverlap keyEq root (lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry source))
ownChildReleaseStep nameEq keyEq root source (LBegin actor) = False
ownChildReleaseStep nameEq keyEq root source (LAdvance actor) = False
ownChildReleaseStep nameEq keyEq root source (LDivert actor) = False
ownChildReleaseStep nameEq keyEq root source (LUnload actor) = False
ownChildReleaseStep nameEq keyEq root source (LLeave actor) = False

||| Compute precisely the own-child release ordinals STRICTLY before the
||| supplied root cut, from actual checked source/action pairs. The state just
||| before each Remove witnesses earlier declaration occupancy, even retired.
public export
scanReleaseOrdinals : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  DecEq name -> DecEq key -> Component key value world error -> Nat -> Nat ->
  AvailabilityTrace name key world error value trace -> List Nat
scanReleaseOrdinals nameEq keyEq root offset cut (AvailabilityEnd state) = []
scanReleaseOrdinals nameEq keyEq root offset cut (AvailabilityStep source (Fired ne ke action tag checked) rest later) =
  if offset < cut && ownChildReleaseStep nameEq keyEq root source action
     then offset :: scanReleaseOrdinals nameEq keyEq root (S offset) cut later
     else scanReleaseOrdinals nameEq keyEq root (S offset) cut later

||| A runtime ordinal with erased membership in the actual computed release
||| scan. This is a scan-membership witness, not yet a LocatedActionOccurrence
||| decoder with explicit child/key/parent projections.
public export
record ReleaseWitness (0 releases : List Nat) where
  constructor MkReleaseWitness
  releaseOrdinal : Nat
  0 releaseScanned : Elem releaseOrdinal releases
