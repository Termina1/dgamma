module DGamma.L2R7ReleaseDecode

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R6ForcedScan
import DGamma.L2R7ObservedAny
import Data.List
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| The actual shared declared key, not a Boolean overlap label.
public export
record SharedKey {key : Type} (left, right : List key) where
  constructor MkSharedKey
  sharedKey : key
  0 inLeft : Elem sharedKey left
  0 inRight : Elem sharedKey right
