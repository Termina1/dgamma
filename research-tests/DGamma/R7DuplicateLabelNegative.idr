module DGamma.R7DuplicateLabelNegative

import DGamma.Coeffects
import Data.List.Elem

%default total

0 duplicateLabelUnique : UniqueKeys [(the Nat 0, the Nat 0), (the Nat 0, the Nat 0)]
duplicateLabelUnique =
  UniqueCons
    (\present => case present of Here impossible)
    (UniqueCons (\present => case present of There later impossible) UniqueNil)
