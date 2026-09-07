module DGamma.CP5RetirementHistorySpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4Support
import DGamma.CP4DeletionSelectedOwn
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Needed to exclude closing classifications for supported endpoint births.
||| This is same-trace operational monotonicity, not cross-trace A9 agreement.
export
0 retirementUpdateFalseBackward :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (old, updated : Fiber name key value world error) ->
  RetirementUpdate old updated -> (retired updated = False) -> (retired old = False)
retirementUpdateFalseBackward name key world error value old updated (RetirementStable same) finalFalse =
  trans (sym same) finalFalse
retirementUpdateFalseBackward name key world error value old updated (RetirementApplied finalTrue) finalFalse =
  case trans (sym finalTrue) finalFalse of Refl impossible
