module DGamma.R174O17SortedProvisionGuard

import DGamma.Core
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4SupportQuiescence
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.Metatheory
import DGamma.Section3Example
import DGamma.Unified
import DGamma.R174O17ProvisionCollisionCandidate
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| The root-first prefix with parent initially inserted: root 2 is RETIRED
||| before begin 0, but not removed. Both child/root components really install K.
||| Only a subsequent checked count equation can exclude the empty fallback.
export
0 r174SortedProvisionPrefix : CertifiedActionTrace Nat ToyKey ToyRuntime String ToyValue %search %search
  (MkSystemState (MkToyRuntime False False) emptyContext)
r174SortedProvisionPrefix = fromMaybe
  (MkCertifiedActionTrace (MkSystemState (MkToyRuntime False False) emptyContext)
    NoTransitions TraceComponentsTotalEnd)
  (buildCertifiedActionTrace %search %search
    [OInsert 0 Root r174ProvisionParent, OInsert 2 Root providerComponent,
     ORetire 2, LBegin 0]
    (MkSystemState (MkToyRuntime False False) emptyContext))
