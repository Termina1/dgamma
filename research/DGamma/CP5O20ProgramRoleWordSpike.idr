module DGamma.CP5O20ProgramRoleWordSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O20BeginObservationSpike
import DGamma.CP5O20CanonicalActionCompletenessSpike
import DGamma.CP5O20NativeAdvanceAttachmentSpike
import DGamma.CP5O20SingleRoleAdvanceExtractionSpike
import DGamma.CP5O20PairedAdvanceSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Expected successful remaining activation tags for a finite program.
||| Empty and singleton programs finish on one Advance; longer programs emit
||| Iter until their final Finish. This function alone does not certify a run.
public export
o20ProgramRoleWord : {step : Type} -> List step -> List RuleTag
o20ProgramRoleWord [] = [LFinishTag]
o20ProgramRoleWord [current] = [LFinishTag]
o20ProgramRoleWord (current :: next :: later) = LIterTag :: o20ProgramRoleWord (next :: later)
