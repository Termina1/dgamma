module DGamma.R19SealedReplayConstructorNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

||| The frozen spine type is exported for producer-owned projections, but an
||| importing consumer must not construct even its empty case independently.
0 forgedScopedReplaySpine :
  SealedSuffixReplaySpine name key world error value nameEq keyEq
    (the (Transitions state state) NoTransitions) NoTransitions
forgedScopedReplaySpine = SealedSuffixReplayEnd
