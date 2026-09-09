module DGamma.R198CanonicalMaybeControlPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20CanonicalMaybeControlSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R178GeneratedOrchestrationFixtures
import DGamma.R192RemovedBirthCurrentNameProbe
import DGamma.R193VestigialHistoryTransportPositive
import DGamma.R195EndpointRebaseBoundaryPositive
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| The native R192 six-edge Remove fixture supplies the actual original
||| Nothing. ANY supplied independent canonical capital then gives canonical
||| Nothing via B10. This declaration is conditional on capital; it does not
||| fabricate an accepted canonical schedule for the original history fixture.
export
0 r198RemovedCanonicalAbsence :
  (capital : IndependentCanonicalSchedule Nat R45Key Unit String R45Value
    r45Protocol r45NameEq r45KeyEq r192RemovedBirthTrace) ->
  (lookupFiber {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String} @{r45NameEq}
    1 (registry (canonicalFinal (canonicalSchedule capital))) = Nothing)
r198RemovedCanonicalAbsence capital =
  o20CanonicalAbsentFromOriginal r45NameEq r45KeyEq r45Protocol
    r192RemovedBirthTrace capital 1 r195RemovedRemainderActuallyAbsent

||| The RAW canonical-endpoint RELATION admits identity even at R193's
||| present-vestigial original endpoint. This packages NO independent canonical
||| schedule: it isolates why that endpoint predicate alone cannot force
||| withdrawal. No frozen/private sorting helper is called or made public.
public export
0 r198ClosingRawIdentityEndpoint :
  CanonicalEndpointRelation Nat R45Key Unit String R45Value r45NameEq r45KeyEq
    r193HistoricalClosed r193HistoricalClosed
r198ClosingRawIdentityEndpoint =
  MkCanonicalEndpointRelation [] []
    (MkEffectStateRelated Refl (\selected => Refl))
    (\selected, outside => fiberControlMaybeReflexive
      (lookupFiber {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String} @{r45NameEq}
        selected (registry r193HistoricalClosed)))
    (\selected, member => absurd member)
    (\selected, member => absurd member)
