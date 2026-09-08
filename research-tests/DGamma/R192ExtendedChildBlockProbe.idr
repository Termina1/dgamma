module DGamma.R192ExtendedChildBlockProbe

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.CP5O20RightOpeningTransportSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R191CanonicalChildRetirementGap
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Same eleven actions and final state as R191, except actual child Retire3
||| is moved before actor1's two lifecycle edges. NEW checked trace, not an
||| assertion that merely extending the grammar moves an old physical action.
public export
r192ParentLocalState : Nat -> SystemState Nat R45Key R45Value Unit String
r192ParentLocalState (Z) = r191ChildGapState 0
r192ParentLocalState (S (Z)) = r191ChildGapState 1
r192ParentLocalState (S (S (Z))) = r191ChildGapState 2
r192ParentLocalState (S (S (S (Z)))) = r191ChildGapState 3
r192ParentLocalState (S (S (S (S (Z))))) = r191ChildGapState 4
r192ParentLocalState (S (S (S (S (S (Z)))))) = r191ChildGapState 5
r192ParentLocalState (S (S (S (S (S (S (Z))))))) = r191ChildGapState 6
r192ParentLocalState (S (S (S (S (S (S (S (Z)))))))) = MkSystemState ()
  (MkCoeffectContext [Bind 3 r45ChildRetired, Bind 2 (freshFiber r45Child Root), Bind 1 (freshFiber r45Child Root), Bind 0 (MkFiber r45Parent Root False (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec emptyContext) (Active (pushLocalUndo @{r45KeyEq} r45Spec id id) EmptyView))]
    (uniqueBindings (registry (r191ChildGapState 6))))
r192ParentLocalState (S (S (S (S (S (S (S (S (Z))))))))) = MkSystemState ()
  (MkCoeffectContext [Bind 3 r45ChildRetired, Bind 2 (freshFiber r45Child Root), Bind 1 (MkFiber r45Child Root False emptyOwned (Reloading [] id EmptyView)), Bind 0 (MkFiber r45Parent Root False (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec emptyContext) (Active (pushLocalUndo @{r45KeyEq} r45Spec id id) EmptyView))]
    (uniqueBindings (registry (r191ChildGapState 6))))
r192ParentLocalState (S (S (S (S (S (S (S (S (S (Z)))))))))) = r191ChildGapState 9
r192ParentLocalState (S (S (S (S (S (S (S (S (S (S (Z))))))))))) = r191ChildGapState 10
r192ParentLocalState (S (S (S (S (S (S (S (S (S (S (S (later)))))))))))) = r191ChildGapState 11
