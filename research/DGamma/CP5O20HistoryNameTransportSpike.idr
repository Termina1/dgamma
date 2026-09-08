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

||| Two actual historical insertions coupled by the accepted generation map.
||| Current raw-name equality and endpoint presence are deliberately absent:
||| removed generations retain their authentic birth stamps and locations.
public export
record O20HistoryBirthPair
  (name, key, world, error : Type) (value : key -> Type)
  (mapping : RegistrationGenerationBijection name)
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error}
  (left : Transitions leftFirst leftFinal) (right : Transitions rightFirst rightFinal)
  (leftName, rightName : name) where
  constructor MkO20HistoryBirthPair
  historyLeftStamp : RegistrationGeneration name
  historyRightStamp : RegistrationGeneration name
  0 historyLeftBirth : CurrentGenerationBirth name key world error value left leftName historyLeftStamp
  0 historyRightBirth : CurrentGenerationBirth name key world error value right rightName historyRightStamp
  0 historyStampsMatched : (generationForward mapping historyLeftStamp = historyRightStamp)

||| The history-indexed computation selects the actual opposite birth name.
||| This equation uses authentic insertion stamps, not current presence.
export
0 o20HistoryTargetOwned :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {mapping : RegistrationGenerationBijection name} ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
  {leftName, rightName : name} ->
  (paired : O20HistoryBirthPair name key world error value mapping left right leftName rightName) ->
  (o20HistoricalTarget mapping (historyLeftStamp paired) = rightName)
o20HistoryTargetOwned paired =
  trans (cong generationName (historyStampsMatched paired))
    (cong generationName (currentBirthStampExact (historyRightBirth paired)))
