module DGamma.L2R7AnchorTransport

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R6Iteration
import Data.List
import Data.List.Elem
import Data.Nat
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Physical action-ordinal map for an adjacent interchange at cut: the
||| crossed step moves RIGHT one, the selected root LEFT one; others stay.
||| A release cut must be transported through its preceding action ordinal,
||| not asserted literally equal on both traces. General semantic proof OPEN.
public export
adjacentOrdinalMap : (cut, ordinal : Nat) -> Nat
adjacentOrdinalMap cut ordinal = if ordinal == cut then S cut
  else if ordinal == S cut then cut else ordinal

||| Precise PER-ROOT release-identity/physical-cut transport CONTRACT.
||| A catalog key seed at/before the root witnesses the actual shared-key
||| own-child Remove on BOTH traces. The same occurrence is identified by the
||| admitted interchange's ordinal map, not a raw child name alone. The exact
||| anchorOf equations certify that this occurrence remains the last release.
||| General anchorTransport and other-root distance invariance remain OPEN.
public export
record AnchorTransport
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, oldFinal, newFinal : SystemState name key value world error}
  (oldTrace : Transitions initial oldFinal) (newTrace : Transitions initial newFinal) where
  constructor MkAnchorTransport
  beforeAnchorTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value oldTrace
  afterAnchorTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value newTrace
  0 transportedMove : AdmittedDistanceMove name key world error value nameEq keyEq beforeAnchorTrail afterAnchorTrail
  transportCut : Nat
  0 transportCutEquation : length (prefixWord transportedMove) = transportCut
  beforeRootEntry : RootCatalogEntry name key world error value
  afterRootEntry : RootCatalogEntry name key world error value
  0 beforeRootMember : Elem beforeRootEntry (scanRootCatalog 0 beforeAnchorTrail)
  0 afterRootMember : Elem afterRootEntry (scanRootCatalog 0 afterAnchorTrail)
  0 sameRootBirth : OInsert (catalogRoot beforeRootEntry) Root (catalogComponent beforeRootEntry) = OInsert (catalogRoot afterRootEntry) Root (catalogComponent afterRootEntry)
  0 rootOrdinalTransport : catalogOrdinal afterRootEntry = adjacentOrdinalMap transportCut (catalogOrdinal beforeRootEntry)
  beforeSeed : RootCatalogEntry name key world error value
  afterSeed : RootCatalogEntry name key world error value
  0 beforeSeedMember : Elem beforeSeed (scanRootCatalog 0 beforeAnchorTrail)
  0 afterSeedMember : Elem afterSeed (scanRootCatalog 0 afterAnchorTrail)
  0 sameSeedBirth : OInsert (catalogRoot beforeSeed) Root (catalogComponent beforeSeed) = OInsert (catalogRoot afterSeed) Root (catalogComponent afterSeed)
  0 seedOrdinalTransport : catalogOrdinal afterSeed = adjacentOrdinalMap transportCut (catalogOrdinal beforeSeed)
  0 seedBeforeRoot : LTE (catalogOrdinal beforeSeed) (catalogOrdinal beforeRootEntry)
  0 seedAfterRoot : LTE (catalogOrdinal afterSeed) (catalogOrdinal afterRootEntry)
  transportChild : name
  transportParent : name
  beforeRelease : LocatedActionOccurrence (ORemove transportChild) oldTrace
  afterRelease : LocatedActionOccurrence (ORemove transportChild) newTrace
  0 releaseOrdinalTransport : locatedActionOrdinal afterRelease = adjacentOrdinalMap transportCut (locatedActionOrdinal beforeRelease)
  0 beforeReleaseBeforeSeed : LT (locatedActionOrdinal beforeRelease) (catalogOrdinal beforeSeed)
  0 afterReleaseBeforeSeed : LT (locatedActionOrdinal afterRelease) (catalogOrdinal afterSeed)
  beforeChildFiber : Fiber name key value world error
  afterChildFiber : Fiber name key value world error
  0 beforeChildFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} transportChild (registry (actionBeforeState beforeRelease)) = Just beforeChildFiber
  0 afterChildFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} transportChild (registry (actionBeforeState afterRelease)) = Just afterChildFiber
  0 beforeOwnChild : fiberParent beforeChildFiber = ChildOf transportParent
  0 afterOwnChild : fiberParent afterChildFiber = ChildOf transportParent
  transportKey : key
  0 beforeChildKey : Elem transportKey (dependencies (componentProvisions (fiberComponent beforeChildFiber)))
  0 afterChildKey : Elem transportKey (dependencies (componentProvisions (fiberComponent afterChildFiber)))
  0 beforeSeedKey : Elem transportKey (dependencies (componentProvisions (catalogComponent beforeSeed)))
  0 afterSeedKey : Elem transportKey (dependencies (componentProvisions (catalogComponent afterSeed)))
  beforeAnchorObserved : Nat
  afterAnchorObserved : Nat
  0 beforeAnchorEquation : anchorOf nameEq keyEq beforeAnchorTrail (catalogOrdinal beforeRootEntry) = Just beforeAnchorObserved
  0 afterAnchorEquation : anchorOf nameEq keyEq afterAnchorTrail (catalogOrdinal afterRootEntry) = Just afterAnchorObserved
  0 beforeMaximumIsRelease : beforeAnchorObserved = S (locatedActionOrdinal beforeRelease)
  0 afterMaximumIsRelease : afterAnchorObserved = S (locatedActionOrdinal afterRelease)
  0 anchorCutTransport : afterAnchorObserved = S (adjacentOrdinalMap transportCut (pred beforeAnchorObserved))
