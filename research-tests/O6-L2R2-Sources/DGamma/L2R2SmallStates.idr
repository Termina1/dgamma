module DGamma.L2R2SmallStates

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Two effectless, dependency-free components. True declares the single key
||| True; False declares no keys. Declaration occupancy, not active table
||| contents, makes the child's/root's True provisions collide natively.
public export
smallComponent : Bool -> Component Bool (\key => Unit) Unit String
smallComponent False = MkComponent (MkCoeffectSpec [] UniqueNil) (MkCoeffectSpec [] UniqueNil) []
smallComponent True = MkComponent (MkCoeffectSpec [] UniqueNil)
  (MkCoeffectSpec [True] (UniqueCons (\present => uninhabited present) UniqueNil)) []
