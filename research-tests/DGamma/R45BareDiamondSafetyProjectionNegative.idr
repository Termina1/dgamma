module DGamma.R45BareDiamondSafetyProjectionNegative

import DGamma.Calculus
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R45GenuineDiamondSafetyDesignPositive
import Decidable.Equality

%default total

||| Negative half of cure (a): before the reviewed record extension, a publicly
||| constructed bare LocalRelationalDiamond has no retained registration-swap
||| safety projection. This expected failure flips only when the selected cure
||| is actually implemented.
0 bareDiamondCannotProjectRegistrationSafety :
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  CandidateRegistrationSwapSafety left right
bareDiamondCannotProjectRegistrationSafety diamond =
  retainedRegistrationSafety diamond
