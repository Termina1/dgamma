module DGamma.R44IteratorForwardNestedCoverageNegative

import DGamma.Calculus
import DGamma.Metatheory

%default total

||| Negative design probe: even a proof-irrelevant Bool codomain is rejected
||| when an IteratorForwardGenerator's StageFromAdvance occurrence is split by
||| nested left-hand-side patterns. The actual and yielded families are covered
||| by single patterns, so the diagnostic is pinned to the forward family.
0 directIteratorForwardNestedCoverage :
  {head : Transition first middle} ->
  {tail : Transitions middle last} ->
  {actor : name} ->
  TraceEffectGenerator name key world error value actor
    (MoreTransitions head tail) -> Bool
directIteratorForwardNestedCoverage
  (ActualForwardGenerator _ _ _ _ _ _ _ _ _) = True
directIteratorForwardNestedCoverage
  (IteratorForwardGenerator
    (StageFromAdvance _ _ _ _ _ OccursHere _ _ _ _ _ _ _ _ _)) = True
directIteratorForwardNestedCoverage
  (IteratorForwardGenerator
    (StageFromAdvance _ _ _ _ _ (OccursLater _) _ _ _ _ _ _ _ _ _)) = True
directIteratorForwardNestedCoverage (IteratorYieldedGenerator _ _) = True
