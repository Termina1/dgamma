module DGamma.R200CanonicalBlockRemainderPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5O20CanonicalActionCompletenessSpike
import DGamma.CP5O20ProgramRoleWordSpike
import DGamma.CP5O20BlockEndRemainderSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R178GeneratedOrchestrationFixtures
import DGamma.R191CanonicalChildRetirementGap
import DGamma.R193VestigialHistoryTransportPositive
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| All THREE authentic R191 blocks have empty body-end remainders. The
||| parent and sibling blocks have nonempty later suffixes; this is a native
||| whole-block producer application, not a scalar endpoint normalization.
export
0 r200R191AllBlockRemainders :
  (actor : Nat) -> (member : Elem actor [0, 1, 2]) ->
  (o20FiberRoleRemainder
    (lookupFiber {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String} @{r45NameEq}
      actor (registry (blockEnd (r191ChildGapBlocks actor member))))) = []
r200R191AllBlockRemainders actor member =
  o20LocatedBlockEndRemainderEmpty (r191ChildGapBlocks actor member) r191ChildGapAligned
