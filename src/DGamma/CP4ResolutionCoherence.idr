module DGamma.CP4ResolutionCoherence

import DGamma.Metatheory
import DGamma.CP3Support
import DGamma.CP4TerminalRecovery

%default total

||| Complete Theorem 64: the already-proved whole-episode resolution structure
||| is paired with constructive Corollary-62 terminal recovery.
public export
0 resolutionCoherenceTheoremProof :
  resolutionCoherenceTheorem name key value world error
resolutionCoherenceTheoremProof =
  resolutionCoherenceFromTerminalRecovery terminalRecoveryTheoremProof
