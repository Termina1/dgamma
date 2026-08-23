module DGamma.R10CoherentBothHalvesCapitalNegative

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import Decidable.Equality

%default total

||| Expected failure: even an internally coherent alternate correspondence has
||| no slot at O18. The output is fixed by sealed deletion then sorting folds.
public export
0 coherentBothHalvesCannotBecomeCapitalOutput :
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  (alternate : ActionRegistrationReplayCorrespondence name key world error value
    original (canonicalTrace (canonicalSchedule capital))) ->
  canonicalOccurrenceCorrespondence capital = alternate
coherentBothHalvesCannotBecomeCapitalOutput capital alternate = Refl
