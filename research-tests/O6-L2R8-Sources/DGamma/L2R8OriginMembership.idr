module DGamma.L2R8OriginMembership

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6Anchors
import DGamma.L2R6FrontNormal
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Maximum chooses an authentic member. The library comparison Bool is
||| observed by its OWN equation at the caller, not re-cased internally.
export
0 maxMemberObserved : (universe : List Nat) -> (left, right : Nat) ->
  (0 leftMember : Elem left universe) -> (0 rightMember : Elem right universe) ->
  (seen : Bool) -> (0 equation : (left > right) = seen) -> Elem (max left right) universe
maxMemberObserved universe left right leftMember rightMember True equation = rewrite equation in leftMember
maxMemberObserved universe left right leftMember rightMember False equation = rewrite equation in rightMember
