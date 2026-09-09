module DGamma.L2R9PredecessorExclusion

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R6FrontNormal
import DGamma.L2R6Phase
import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Maybe
import Data.Nat
import Data.Rel
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| LOCAL head algebra for the EXACT two FrontNormal/NeverRetired guards.
||| Once both actual head conjuncts are decoded, a root control after life
||| is impossible whether its origin is forced or not. General whole-scan
||| acceptance -> located-head extraction remains OPEN, not an assumed law.
||| In attachedC the forced-control alternative must instead be authenticated
||| as belonging to an earlier placed bundle; that placement lift is OPEN.
export
0 rootControlHeadExcluded : (seen, rootInput, control, forced : Bool) ->
  (0 seenAccepted : seen = True) -> (0 rootAccepted : rootInput = True) ->
  (0 controlAccepted : control = True) ->
  (0 front : not (seen && rootInput && not forced) = True) ->
  (0 never : not (control && rootInput && forced) = True) -> Void
rootControlHeadExcluded seen rootInput control False seenAccepted rootAccepted controlAccepted front never =
  absurd (replace {p = \r => not (True && r && True) = True} rootAccepted
    (replace {p = \s => not (s && rootInput && True) = True} seenAccepted front))
rootControlHeadExcluded seen rootInput control True seenAccepted rootAccepted controlAccepted front never =
  absurd (replace {p = \r => not (True && r && True) = True} rootAccepted
    (replace {p = \c => not (c && rootInput && True) = True} controlAccepted never))
