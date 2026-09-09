module DGamma.L2R3RemoveDispatch

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP4DeletionCommuteCore
import DGamma.CP4DeletionChildlessInvariant
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2CheckedSnapshot
import Decidable.Equality

%default total
%unbound_implicits off

||| Retirement changes no parent metadata. This one-constructor observation
||| supplies the native childlessness frame needed by a foreign Remove replay.
export
0 retirementKeepsParent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (fiber : Fiber name key value world error) ->
  fiberParent (retireFiber fiber) = fiberParent fiber
retirementKeepsParent (MkFiber component parent retired table lifecycle) = Refl
