module DGamma.R191CanonicalChildRetirementGap

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Explicit physical candidate cuts 0..11. Each actual evaluator equation
||| remains a separate obligation in r191ChildGapTrace; no fallback state or
||| recursively nested evaluator is used to normalize the trace witnesses.
public export
r191ChildGapState : Nat -> SystemState Nat R45Key R45Value Unit String
r191ChildGapState Z = r45Initial
r191ChildGapState (S Z) = r45AfterParent
r191ChildGapState (S (S (Z))) = MkSystemState ()
  (MkCoeffectContext [Bind 1 (freshFiber r45Child Root), Bind 0 (r45ParentFresh)]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String)
      (insertBinding @{r45NameEq} 1 (freshFiber r45Child Root) (r45AfterParentRegistry) Refl))))
r191ChildGapState (S (S (S (Z)))) = MkSystemState ()
  (MkCoeffectContext [Bind 2 (freshFiber r45Child Root), Bind 1 (freshFiber r45Child Root), Bind 0 (r45ParentFresh)]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String)
      (insertBinding @{r45NameEq} 2 (freshFiber r45Child Root) (insertBinding @{r45NameEq} 1 (freshFiber r45Child Root) (r45AfterParentRegistry) Refl) Refl))))
r191ChildGapState (S (S (S (S (Z))))) = MkSystemState ()
  (MkCoeffectContext [Bind 2 (freshFiber r45Child Root), Bind 1 (freshFiber r45Child Root), Bind 0 (r45ParentBegun)]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String)
      (insertBinding @{r45NameEq} 2 (freshFiber r45Child Root) (insertBinding @{r45NameEq} 1 (freshFiber r45Child Root) (r45AfterParentRegistry) Refl) Refl))))
r191ChildGapState (S (S (S (S (S (Z)))))) = MkSystemState ()
  (MkCoeffectContext [Bind 3 (r45ChildFresh), Bind 2 (freshFiber r45Child Root), Bind 1 (freshFiber r45Child Root), Bind 0 (r45ParentBegun)]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String)
      (insertBinding @{r45NameEq} 3 (r45ChildFresh) (replaceBinding @{r45NameEq} 0 r45ParentBegun (insertBinding @{r45NameEq} 2 (freshFiber r45Child Root) (insertBinding @{r45NameEq} 1 (freshFiber r45Child Root) (r45AfterParentRegistry) Refl) Refl)) Refl))))
r191ChildGapState (S (S (S (S (S (S (Z))))))) = MkSystemState ()
  (MkCoeffectContext [Bind 3 (r45ChildFresh), Bind 2 (freshFiber r45Child Root), Bind 1 (freshFiber r45Child Root), Bind 0 (MkFiber r45Parent Root False (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec emptyContext) (Active (pushLocalUndo @{r45KeyEq} r45Spec id id) EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String)
      (insertBinding @{r45NameEq} 3 (r45ChildFresh) (replaceBinding @{r45NameEq} 0 r45ParentBegun (insertBinding @{r45NameEq} 2 (freshFiber r45Child Root) (insertBinding @{r45NameEq} 1 (freshFiber r45Child Root) (r45AfterParentRegistry) Refl) Refl)) Refl))))
r191ChildGapState (S (S (S (S (S (S (S (Z)))))))) = MkSystemState ()
  (MkCoeffectContext [Bind 3 (r45ChildFresh), Bind 2 (freshFiber r45Child Root), Bind 1 (MkFiber r45Child Root False emptyOwned (Reloading [] id EmptyView)), Bind 0 (MkFiber r45Parent Root False (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec emptyContext) (Active (pushLocalUndo @{r45KeyEq} r45Spec id id) EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String)
      (insertBinding @{r45NameEq} 3 (r45ChildFresh) (replaceBinding @{r45NameEq} 0 r45ParentBegun (insertBinding @{r45NameEq} 2 (freshFiber r45Child Root) (insertBinding @{r45NameEq} 1 (freshFiber r45Child Root) (r45AfterParentRegistry) Refl) Refl)) Refl))))
r191ChildGapState (S (S (S (S (S (S (S (S (Z))))))))) = MkSystemState ()
  (MkCoeffectContext [Bind 3 (r45ChildFresh), Bind 2 (freshFiber r45Child Root), Bind 1 (MkFiber r45Child Root False emptyOwned (Active id EmptyView)), Bind 0 (MkFiber r45Parent Root False (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec emptyContext) (Active (pushLocalUndo @{r45KeyEq} r45Spec id id) EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String)
      (insertBinding @{r45NameEq} 3 (r45ChildFresh) (replaceBinding @{r45NameEq} 0 r45ParentBegun (insertBinding @{r45NameEq} 2 (freshFiber r45Child Root) (insertBinding @{r45NameEq} 1 (freshFiber r45Child Root) (r45AfterParentRegistry) Refl) Refl)) Refl))))
r191ChildGapState (S (S (S (S (S (S (S (S (S (Z)))))))))) = MkSystemState ()
  (MkCoeffectContext [Bind 3 (r45ChildRetired), Bind 2 (freshFiber r45Child Root), Bind 1 (MkFiber r45Child Root False emptyOwned (Active id EmptyView)), Bind 0 (MkFiber r45Parent Root False (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec emptyContext) (Active (pushLocalUndo @{r45KeyEq} r45Spec id id) EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String)
      (insertBinding @{r45NameEq} 3 (r45ChildFresh) (replaceBinding @{r45NameEq} 0 r45ParentBegun (insertBinding @{r45NameEq} 2 (freshFiber r45Child Root) (insertBinding @{r45NameEq} 1 (freshFiber r45Child Root) (r45AfterParentRegistry) Refl) Refl)) Refl))))
r191ChildGapState (S (S (S (S (S (S (S (S (S (S (Z))))))))))) = MkSystemState ()
  (MkCoeffectContext [Bind 3 (r45ChildRetired), Bind 2 (MkFiber r45Child Root False emptyOwned (Reloading [] id EmptyView)), Bind 1 (MkFiber r45Child Root False emptyOwned (Active id EmptyView)), Bind 0 (MkFiber r45Parent Root False (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec emptyContext) (Active (pushLocalUndo @{r45KeyEq} r45Spec id id) EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String)
      (insertBinding @{r45NameEq} 3 (r45ChildFresh) (replaceBinding @{r45NameEq} 0 r45ParentBegun (insertBinding @{r45NameEq} 2 (freshFiber r45Child Root) (insertBinding @{r45NameEq} 1 (freshFiber r45Child Root) (r45AfterParentRegistry) Refl) Refl)) Refl))))
r191ChildGapState (S (S (S (S (S (S (S (S (S (S (S (later)))))))))))) = MkSystemState ()
  (MkCoeffectContext [Bind 3 (r45ChildRetired), Bind 2 (MkFiber r45Child Root False emptyOwned (Active id EmptyView)), Bind 1 (MkFiber r45Child Root False emptyOwned (Active id EmptyView)), Bind 0 (MkFiber r45Parent Root False (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec emptyContext) (Active (pushLocalUndo @{r45KeyEq} r45Spec id id) EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String)
      (insertBinding @{r45NameEq} 3 (r45ChildFresh) (replaceBinding @{r45NameEq} 0 r45ParentBegun (insertBinding @{r45NameEq} 2 (freshFiber r45Child Root) (insertBinding @{r45NameEq} 1 (freshFiber r45Child Root) (r45AfterParentRegistry) Refl) Refl)) Refl))))

||| All eleven ACTUAL checked edges at the explicit physical cuts. This
||| alone is not yet accepted canonical capital; the following units must own
||| its discipline, root placement, decomposition and full endpoint premises.
public export
0 r191ChildGapTrace : Transitions (r191ChildGapState 0) (r191ChildGapState 11)
r191ChildGapTrace =
  MoreTransitions (Fired {before = r191ChildGapState 0} {afterState = r191ChildGapState 1}
    r45NameEq r45KeyEq (OInsert 0 Root r45Parent) OInsertTag Refl)
    (    MoreTransitions (Fired {before = r191ChildGapState 1} {afterState = r191ChildGapState 2}
      r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl)
      (      MoreTransitions (Fired {before = r191ChildGapState 2} {afterState = r191ChildGapState 3}
        r45NameEq r45KeyEq (OInsert 2 Root r45Child) OInsertTag Refl)
        (        MoreTransitions (Fired {before = r191ChildGapState 3} {afterState = r191ChildGapState 4}
          r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl)
          (          MoreTransitions (Fired {before = r191ChildGapState 4} {afterState = r191ChildGapState 5}
            r45NameEq r45KeyEq (OInsert 3 (ChildOf 0) r45Child) OInsertTag Refl)
            (            MoreTransitions (Fired {before = r191ChildGapState 5} {afterState = r191ChildGapState 6}
              r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl)
              (              MoreTransitions (Fired {before = r191ChildGapState 6} {afterState = r191ChildGapState 7}
                r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl)
                (                MoreTransitions (Fired {before = r191ChildGapState 7} {afterState = r191ChildGapState 8}
                  r45NameEq r45KeyEq (LAdvance 1) LFinishTag Refl)
                  (                  MoreTransitions (Fired {before = r191ChildGapState 8} {afterState = r191ChildGapState 9}
                    r45NameEq r45KeyEq (ORetire 3) ORetireTag Refl)
                    (                    MoreTransitions (Fired {before = r191ChildGapState 9} {afterState = r191ChildGapState 10}
                      r45NameEq r45KeyEq (LBegin 2) LBeginTag Refl)
                      (                      MoreTransitions (Fired {before = r191ChildGapState 10} {afterState = r191ChildGapState 11}
                        r45NameEq r45KeyEq (LAdvance 2) LFinishTag Refl)
                        (NoTransitions)))))))))))
