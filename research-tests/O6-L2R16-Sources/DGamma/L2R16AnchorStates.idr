module DGamma.L2R16AnchorStates

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.L2R2SmallStates
import DGamma.L2R10OrdinalData
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Two independent declaration keys. The owner and spare child instead use
||| smallComponent False (no provisions). These programs perform no effects.
public export
anchorComponent : Bool -> Component Bool (\key => Unit) Unit String
anchorComponent provision = MkComponent (MkCoeffectSpec [] UniqueNil)
  (MkCoeffectSpec [provision] (UniqueCons (\member => uninhabited member) UniqueNil)) []
