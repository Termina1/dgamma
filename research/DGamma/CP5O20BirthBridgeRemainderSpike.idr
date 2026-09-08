module DGamma.CP5O20BirthBridgeRemainderSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20SupportedBirthBridgeSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| Honest fourth-clause result indexed by the ACTUAL original child support.
||| The matched payload is the exact canonical/replay origin packet, unchanged.
||| False carries an explicit unresolved branch, NOT an invented opposite birth,
||| not proof of impossibility, and not a fallback claimed to close O20.
public export
data O20BirthBridgeAttempt : Bool -> Type -> Type where
  O20UnsupportedBirth : {matched : Type} -> O20BirthBridgeAttempt False matched
  O20MatchedBirth : {matched : Type} -> (0 evidence : matched) -> O20BirthBridgeAttempt True matched
