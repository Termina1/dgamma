module DGamma.CP5SupportClauseTransportSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4SupportSolution
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5AllSupportedMetadataSpike
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

public export
supportClauseParent : (name : Type) -> (name -> Bool) -> Parent name -> Bool
supportClauseParent name predicate Root = True
supportClauseParent name predicate (ChildOf parent) = predicate parent
