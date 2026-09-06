module DGamma.R171CoreHistoryCloneNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceDeletionChainSpike
import Decidable.Equality

%default total

||| Expected rejection: a typed alternate history is not the derivation's complete history.
public export
0 replaceCoreHistory :
  (core : ClosingFreeTraceCore name key world error value protocol nameEq keyEq trace) ->
  (alternate : List (generation : RegistrationGeneration name ** DeletedGenerationClassification name key world error value nameEq trace generation)) ->
  ClosingFreeTraceCore name key world error value protocol nameEq keyEq trace
replaceCoreHistory core alternate = { coreDeletionGenerationHistory := alternate } core
