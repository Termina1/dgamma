module DGamma.R206ControlRebasePositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20EpisodeSynchronizationSpike
import DGamma.CP5O20AllNameSynchronizationSpike
import DGamma.CP5O20EndpointRebaseBoundarySpike
import DGamma.CP5O20ControlRebaseSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R178GeneratedOrchestrationFixtures
import DGamma.R192RemovedBirthCurrentNameProbe
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| The real six-edge removal endpoint has current root0, while raw names1
||| and2 are absent. The two maps agree ONLY on actual present source entries.
export
0 r206RemovedCurrentAgreement :
  (selected : Nat) -> (fiber : Fiber Nat R45Key R45Value Unit String) ->
  lookupFiber @{r45NameEq} selected (registry r192RemovedBirthFinal) = Just fiber ->
  renameForward (identityNameBijection {name = Nat}) selected =
  renameForward r192AbsentBijection selected
r206RemovedCurrentAgreement Z fiber found = Refl
r206RemovedCurrentAgreement (S later) fiber found = void (nothingIsNotJust found)
