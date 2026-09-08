module DGamma.CP5O20HistoryNameTransportSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| History-indexed target name. Unlike the current endpoint bijection, this
||| computation retains the insertion ordinal, including a removed generation.
public export
o20HistoricalTarget :
  {name : Type} -> RegistrationGenerationBijection name ->
  RegistrationGeneration name -> name
o20HistoricalTarget mapping generation = generationName (generationForward mapping generation)
