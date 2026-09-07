module DGamma.R179O19DependencyCountershape

import DGamma.Core
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4SupportQuiescence
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.Metatheory
import DGamma.Section3Example
import DGamma.Unified
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Actual checked provider/consumer prefix. A separate count theorem must
||| exclude the empty fallback before any countershape claim.
export
0 r179BeforeProviderFinish : CertifiedActionTrace Nat ToyKey ToyRuntime String ToyValue %search %search
  (MkSystemState (MkToyRuntime False False) emptyContext)
r179BeforeProviderFinish = fromMaybe
  (MkCertifiedActionTrace (MkSystemState (MkToyRuntime False False) emptyContext)
    NoTransitions TraceComponentsTotalEnd)
  (buildCertifiedActionTrace %search %search
    [OInsert 0 Root providerComponent, OInsert 1 Root emptyConsumerComponent,
     LBegin 0, LAdvance 0]
    (MkSystemState (MkToyRuntime False False) emptyContext))

||| The prefix REALLY executes four steps, yet its consumer cannot begin:
||| provider installation without Active visibility is insufficient.
export
0 r179EarlyConsumerBeginUnavailable :
  ((transitionCount (certifiedTrace r179BeforeProviderFinish) = 4),
   (applyAction (LBegin 1) (certifiedFinal r179BeforeProviderFinish) = Nothing))
r179EarlyConsumerBeginUnavailable = (Refl, Refl)

||| Complete the same checked prefix: Finish(provider); Begin(consumer);
||| Finish(consumer). Again a separate observation excludes the fallback.
export
0 r179AfterProviderFinish : CertifiedActionTrace Nat ToyKey ToyRuntime String ToyValue %search %search
  (certifiedFinal r179BeforeProviderFinish)
r179AfterProviderFinish = fromMaybe
  (MkCertifiedActionTrace (certifiedFinal r179BeforeProviderFinish)
    NoTransitions TraceComponentsTotalEnd)
  (buildCertifiedActionTrace %search %search
    [LAdvance 0, LBegin 1, LAdvance 1]
    (certifiedFinal r179BeforeProviderFinish))

||| Smaller observed boundary after the suffix count normalization stop:
||| the actual provider's next raw action does finish, without post-hoc WF.
export
0 r179ProviderFinishRawAvailable :
  ((case applyAction (LAdvance 0) (certifiedFinal r179BeforeProviderFinish) of
      Nothing => False
      Just (tag, afterState) => tagEq tag LFinishTag) = True)
r179ProviderFinishRawAvailable = Refl
