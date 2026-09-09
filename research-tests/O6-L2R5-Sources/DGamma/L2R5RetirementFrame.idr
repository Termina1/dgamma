module DGamma.L2R5RetirementFrame

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Data.List
import Decidable.Equality

%default total
%unbound_implicits off

||| Executable equality observation on two optional resolver views over the
||| SAME dependency list. This Bool is an observation, not an equality proof.
public export
sameOptionalView : {name, key : Type} -> {deps : List key} ->
  (nameEq : DecEq name) -> Maybe (View name deps) -> Maybe (View name deps) -> Bool
sameOptionalView nameEq Nothing Nothing = True
sameOptionalView nameEq Nothing (Just right) = False
sameOptionalView nameEq (Just left) Nothing = False
sameOptionalView nameEq (Just left) (Just right) = viewEq @{nameEq} left right
