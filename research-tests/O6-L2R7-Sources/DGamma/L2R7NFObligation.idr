module DGamma.L2R7NFObligation

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3Attached
import DGamma.L2R3AttachedGap
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R6FrontNormal
import DGamma.L2R6Phase
import DGamma.L2R7PlacedCoverage
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Precise SCOPED inter-block NF obligation TYPE, not an inhabited theorem.
||| The gap is the actual BlockBeforeAttached region, never arbitrary mixed
||| trace fragments. All root controls are still classified by the original
||| RootOrchestrationStep; no Insert-only weakening and no rootInBundle oracle.
||| OPEN produceAttachedNormalForm: front/control occurrence exclusion, origin
||| correspondence and region embedding must connect to placedRootCoverage.
||| Even after NF, residual-head coverage and universal interval separation
||| are separately needed by the zero-gap theorem. No all-premises zero here.
public export
GeneralAttachedNormalForm : {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, finalState : SystemState name key value world error} ->
  {trace : Transitions initial finalState} ->
  DecEq name -> DecEq key -> AvailabilityTrace name key world error value trace -> Type
GeneralAttachedNormalForm {name} {key} {world} {error} {value} {trace} nameEq keyEq trail =
  (earlierName, laterName : name) ->
  (earlier : LocatedOpenEpisodeBlockAttached name key world error value nameEq keyEq earlierName trace) ->
  (later : LocatedOpenEpisodeBlockAttached name key world error value nameEq keyEq laterName trace) ->
  (ordered : BlockBeforeAttached name key world error value nameEq keyEq trace earlierName laterName earlier later) ->
  (0 front : FrontNormal name key world error value nameEq keyEq trail) ->
  (0 never : ForcedRootNeverRetired name key world error value nameEq keyEq trail) ->
  (0 phases : (entry : RootCatalogEntry name key world error value) -> Elem entry (scanRootCatalog 0 trail) ->
    ForcedOnTrace nameEq keyEq trail (catalogOrdinal entry) -> ForcedRootPhase name key world error value nameEq keyEq trail entry) ->
  (0 placements : (entry : RootCatalogEntry name key world error value) -> Elem entry (scanRootCatalog 0 trail) ->
    (anchor : Nat) -> anchorOf nameEq keyEq trail (catalogOrdinal entry) = Just anchor ->
    PlacedBundle name key world error value nameEq keyEq trail anchor) ->
  AttachedNormalForm name key world error value nameEq keyEq trace (attachedBetweenBlocks ordered)
    (transitionCount (attachedBefore earlier) + S (transitionCount (attachedBody earlier)))
