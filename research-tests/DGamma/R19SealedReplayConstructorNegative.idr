module DGamma.R19SealedReplayConstructorNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.R19SealedReplayCertificateScopingPositive

%default total

||| The scoping candidate exports its indexed certificate types and producer
||| functions, but importing consumers must not construct a detached recursive
||| spine or certificate.
0 forgedScopedReplaySpine :
  ScopedReplaySpine {name = name} {key = key} {world = world} {error = error}
    {value = value} (the (Transitions state state) NoTransitions) NoTransitions
forgedScopedReplaySpine = ScopedReplayEnd
