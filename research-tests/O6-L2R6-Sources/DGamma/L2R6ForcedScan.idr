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

||| Extract a member only from an explicitly observed nonempty scan. The
||| Boolean and its equation are arguments; no computed existential is split.
public export
releaseWitnessObserved : (releases : List Nat) -> (observed : Bool) ->
  (0 equation : not (null releases) = observed) -> (0 forced : observed = True) -> ReleaseWitness releases
releaseWitnessObserved [] observed equation forced = absurd (trans equation forced)
releaseWitnessObserved (ordinal :: later) observed equation forced = MkReleaseWitness ordinal Here

||| Trace-linked key-forcing observation for an AUTHENTIC catalog member.
||| True returns an ordinal in the actual earlier-child-release scan. Explicit
||| occurrence/key decoding and scan soundness/completeness are separate debt.
public export
record KeyForcedAt
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {0 first, finalState : SystemState name key value world error}
  {0 trace : Transitions first finalState}
  (trail : AvailabilityTrace name key world error value trace)
  (entry : RootCatalogEntry name key world error value) where
  constructor MkKeyForcedAt
  0 keyRootInCatalog : Elem entry (scanRootCatalog 0 trail)
  keyForcedObserved : Bool
  0 keyForcedEquation : not (null (scanReleaseOrdinals nameEq keyEq (catalogComponent entry) 0 (catalogOrdinal entry) trail)) = keyForcedObserved
  releaseWhenForced : (0 forced : keyForcedObserved = True) ->
    ReleaseWitness (scanReleaseOrdinals nameEq keyEq (catalogComponent entry) 0 (catalogOrdinal entry) trail)

||| Single-constructor observation producer: both the Bool and conditional
||| release witness come from the same computed native trace scan.
public export
keyForcedAt : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (entry : RootCatalogEntry name key world error value) ->
  (0 member : Elem entry (scanRootCatalog 0 trail)) ->
  KeyForcedAt name key world error value nameEq keyEq trail entry
keyForcedAt nameEq keyEq trail entry member = MkKeyForcedAt member
  (not (null (scanReleaseOrdinals nameEq keyEq (catalogComponent entry) 0 (catalogOrdinal entry) trail))) Refl
  (releaseWitnessObserved (scanReleaseOrdinals nameEq keyEq (catalogComponent entry) 0 (catalogOrdinal entry) trail)
    (not (null (scanReleaseOrdinals nameEq keyEq (catalogComponent entry) 0 (catalogOrdinal entry) trail))) Refl)

||| Key-seed test at a physical ordinal in the generated native catalog.
||| Non-birth ordinals reject; an actual item's own component drives its scan.
public export
keyForcedOrdinal : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  DecEq name -> DecEq key -> AvailabilityTrace name key world error value trace -> Nat -> Bool
keyForcedOrdinal nameEq keyEq trail ordinal = any
  (\entry => catalogOrdinal entry == ordinal &&
    not (null (scanReleaseOrdinals nameEq keyEq (catalogComponent entry) 0 (catalogOrdinal entry) trail)))
  (scanRootCatalog 0 trail)

||| The generic least closure instantiated ONLY with generated birth ordinals
||| and computed actual-release key seeds. This is not defined as classifier
||| truth, and includes precisely key seeds plus strictly later actual roots.
public export
ForcedOnTrace : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  DecEq name -> DecEq key -> AvailabilityTrace name key world error value trace -> Nat -> Type
ForcedOnTrace nameEq keyEq trail = ForcedRootInput
  (\ordinal => Elem ordinal (map catalogOrdinal (scanRootCatalog 0 trail)))
  (\ordinal => keyForcedOrdinal nameEq keyEq trail ordinal = True)

||| Executable prefix-closure classifier over the AUTHENTIC ordered catalog.
||| Each root is flagged iff some catalog seed at or before its ordinal has
||| an actual earlier child release. General equivalence to ForcedOnTrace is
||| an outstanding proof, not an assumed field of this runtime definition.
public export
classifyForced : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  DecEq name -> DecEq key -> (trail : AvailabilityTrace name key world error value trace) ->
  (catalog : List (RootCatalogEntry name key world error value)) ->
  (0 exact : catalog = scanRootCatalog 0 trail) -> List (name, Bool)
classifyForced nameEq keyEq trail catalog exact = map
  (\entry => (catalogRoot entry, any
    (\seed => catalogOrdinal seed <= catalogOrdinal entry &&
      keyForcedOrdinal nameEq keyEq trail (catalogOrdinal seed)) catalog)) catalog

||| Leastness after the trace predicates are fixed. This proof does not use
||| classifier truth as a premise or redefine the seed set to match its output.
export
0 forcedOnTraceLeast : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (candidate : Nat -> Type) ->
  (0 seeds : (n : Nat) -> Elem n (map catalogOrdinal (scanRootCatalog 0 trail)) ->
    keyForcedOrdinal nameEq keyEq trail n = True -> candidate n) ->
  (0 closed : (earlier, later : Nat) -> candidate earlier ->
    Elem later (map catalogOrdinal (scanRootCatalog 0 trail)) -> LT earlier later -> candidate later) ->
  {ordinal : Nat} -> ForcedOnTrace nameEq keyEq trail ordinal -> candidate ordinal
forcedOnTraceLeast nameEq keyEq trail candidate seeds closed forced =
  forcedRootLeast candidate seeds closed forced
