module DGamma.R30AdjacentSwapResultConstructorNegative

import DGamma.CP5ConfluenceLocalDiamondSpike

%default total

||| The adjacent result exposes its producer-owned projections, but importing
||| consumers cannot synthesize the outer envelope with detached capital.
0 forgeOpaqueAdjacentResult : Void
forgeOpaqueAdjacentResult = MkAdjacentSwapResult
