module DGamma.L2R8PrefixPhase

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3ForcedClosure
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R6FrontNormal
import DGamma.L2R6Phase
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Exact placed-prefix/selected-root invariant TYPE ONLY. Not normalization;
||| move/phase producers open. Earlier forced roots own actual PlacedBundles
||| as well as distance zero and native phases; selected root owns its phase.
||| Later roots deliberately have NO contiguous-core premise mid-round.
||| Restoring their phases after an outer round needs coreContiguityRestored.
||| Uses unchanged L2R6 forcing/anchor scans, NOT an implicit substitution of
||| the new isElem release scan; releaseScanAgrees remains open separately.
public export
record PlacedPrefixPhaseInvariant
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  {trace : Transitions initial finalState}
  (trail : AvailabilityTrace name key world error value trace)
  (selected : RootCatalogEntry name key world error value) where
  constructor MkPlacedPrefixPhaseInvariant
  0 selectedMember : Elem selected (scanRootCatalog 0 trail)
  0 selectedForced : ForcedOnTrace nameEq keyEq trail (catalogOrdinal selected)
  0 selectedPhase : ForcedRootPhase name key world error value nameEq keyEq trail selected
  0 prefixFront : FrontNormal name key world error value nameEq keyEq trail
  0 prefixNeverRetired : ForcedRootNeverRetired name key world error value nameEq keyEq trail
  0 earlierPlacedPhases : (earlier : RootCatalogEntry name key world error value) ->
    Elem earlier (scanRootCatalog 0 trail) -> LT (catalogOrdinal earlier) (catalogOrdinal selected) ->
    ForcedOnTrace nameEq keyEq trail (catalogOrdinal earlier) ->
    (phase : ForcedRootPhase name key world error value nameEq keyEq trail earlier **
      (rootDistance nameEq keyEq trail (catalogOrdinal earlier) = 0,
       PlacedBundle name key world error value nameEq keyEq trail
         (transitionCount (phasePrefix phase) + transitionCount (phaseCore phase))))
