module DGamma.CP4ProgressUnloadingShape

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import Decidable.Equality

%default total

||| Compact indexed evidence that a fiber is in the Unloading lifecycle.
public export
data IsUnloadingFiber : {name, key, world, error : Type} ->
  {value : key -> Type} -> Fiber name key value world error -> Type where
  UnloadingNow :
    IsUnloadingFiber
      (MkFiber component parent retiredFlag table
        (Unloading accumulator view outcome))
