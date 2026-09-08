module DGamma.CP5O19CartesianWordRowSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19MixedRowDispatcherSpike
import DGamma.CP5O19MixedActivationRowSpike
import DGamma.CP5O19CartesianLengthSpike
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Cartesian row boundary strengthens the actual unified row by retaining
||| its exact residual source action word. Length alone cannot identify the
||| next left/right segment, and a separate scalar observer of a row builder
||| would not justify this equation. The row recursion must construct BOTH.
public export
record O19WordRow
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, sourceFinal, before, rightBefore, rightAfter : SystemState name key value world error}
  (source : Transitions initial sourceFinal) (earlier : Transitions initial before)
  (spine : Transitions before rightBefore) (right : Transition rightBefore rightAfter)
  (later : Transitions rightAfter sourceFinal) where
  constructor MkO19WordRow
  wordRow : O19MixedRow name key world error value protocol nameEq keyEq source earlier right (transitionCount spine)
  0 wordRowRest : o19ActionWord (mixedRowRest wordRow) = o19ActionWord spine ++ o19ActionWord later
