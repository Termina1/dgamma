module DGamma.L2R5ExtensionalFixtures

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import Decidable.Equality
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R2RootSnapshot
import DGamma.L2R2RootPhase
import DGamma.L2R3BundlePhaseStates
import DGamma.L2R3BundlePhase
import DGamma.L2R5Extensional

%default total
%unbound_implicits off

||| The existing one- and two-move native fixture prefix endpoints embed in
||| the revised relation. Six-edge alternate prefix ends at smallState9;
||| seven-edge R/S alternate prefix ends at bundlePhaseState3. Both stop at
||| Begin2, NOT the original seven-/eight-edge fixtures' Finish2 endpoints.
||| These are inherited real moves, not instances of a new iteration theorem.
export
0 extensionalFixtureEndpoints :
  (RegistryExtensional Nat Bool Unit String (\key => Unit) %search (smallState 9) (smallState 6),
   RegistryExtensional Nat Bool Unit String (\key => Unit) %search (bundlePhaseState 3)
     (snapshotRootFinal (rootPhaseSquare (sPhase bundlePhaseEvidence))))
extensionalFixtureEndpoints =
  (snapshotIntoExtensional %search (smallState 9) (smallState 6) (smallAlternateSnapshot smallNativeExecution),
   snapshotIntoExtensional %search (bundlePhaseState 3)
     (snapshotRootFinal (rootPhaseSquare (sPhase bundlePhaseEvidence)))
     (originalToMovedRuntime bundlePhaseEvidence))
