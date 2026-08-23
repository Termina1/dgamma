module DGamma.R11DeletionFillerMapCertificateNegative

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import Decidable.Equality

%default total

||| Expected failure: a filler-selected coherent map is insufficient. Supplying
||| the before-segment constructor with `Refl` cannot cover arbitrary survivor
||| occurrences unless the exact retained-subsequence computation agrees.
public export
0 fillerMapCannotConstructDeletionCertificate :
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered episodeStartOrdinal episodeStartLive) ->
  (filler : ActionRegistrationReplayCorrespondence name key world error value
    original (survivingTrace result)) ->
  DeletionOperationalOccurrenceCertificate name key world error value nameEq keyEq
    original selected episode registered episodeStartOrdinal episodeStartLive result
fillerMapCannotConstructDeletionCertificate result filler =
  MkDeletionOperationalOccurrenceCertificate filler
    (\occurrence => DeletionBeforeEmbedding Refl)
