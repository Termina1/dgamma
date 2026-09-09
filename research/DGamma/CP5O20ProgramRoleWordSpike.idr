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

||| Executable per-fiber successful-activation remainder. Inactive includes
||| its next Begin, Reloading includes its remaining Advances, and all other
||| phases/absence give the empty word. Applicability is not asserted by this
||| observer (in particular an inactive failure need not admit Begin).
public export
o20FiberRoleRemainder :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  Maybe (Fiber name key value world error) -> List RuleTag
o20FiberRoleRemainder Nothing = []
o20FiberRoleRemainder (Just (MkFiber component parent retiredFlag table (Inactive outcome))) =
  LBeginTag :: o20ProgramRoleWord (componentProgram component)
o20FiberRoleRemainder (Just (MkFiber component parent retiredFlag table (Reloading remaining accumulator view))) =
  o20ProgramRoleWord remaining
o20FiberRoleRemainder (Just (MkFiber component parent retiredFlag table (Active accumulator view))) = []
o20FiberRoleRemainder (Just (MkFiber component parent retiredFlag table (Unloading accumulator view outcome))) = []
