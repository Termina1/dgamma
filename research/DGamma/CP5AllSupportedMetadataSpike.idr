module DGamma.CP5AllSupportedMetadataSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5MatchedBirthMetadataSpike
import DGamma.CP5RootBirthCoverageSpike
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

public export
supportMapParent : (name : Type) -> (name -> name) -> Parent name -> Parent name
supportMapParent name renaming Root = Root
supportMapParent name renaming (ChildOf parent) = ChildOf (renaming parent)
