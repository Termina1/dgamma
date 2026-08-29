module DGamma.R44IteratorYieldedNestedCoverageNegative

import DGamma.Calculus
import DGamma.Metatheory

%default total

||| Yielded analogue of the forward negative probe. The actual and forward
||| families are covered by single patterns; splitting only the yielded stage's
||| hidden occurrence still leaves uncovered IteratorYieldedGenerator families.
0 directIteratorYieldedNestedCoverage :
  {head : Transition first middle} ->
  {tail : Transitions middle last} ->
  {actor : name} ->
  TraceEffectGenerator name key world error value actor
    (MoreTransitions head tail) -> Bool
directIteratorYieldedNestedCoverage
  (ActualForwardGenerator _ _ _ _ _ _ _ _ _) = True
directIteratorYieldedNestedCoverage (IteratorForwardGenerator _) = True
directIteratorYieldedNestedCoverage
  (IteratorYieldedGenerator
    (StageFromAdvance _ _ _ _ _ OccursHere _ _ _ _ _ _ _ _ _) _) = True
directIteratorYieldedNestedCoverage
  (IteratorYieldedGenerator
    (StageFromAdvance _ _ _ _ _ (OccursLater _) _ _ _ _ _ _ _ _ _) _) = True
