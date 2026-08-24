module DGamma.R21WholeBundleQuietTransportNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

||| After moved alignment, discipline, empty-start facts, and final
||| well-formedness close, `replayQuiet` is the next whole-bundle field.  The
||| current relational endpoint exposes effects, controls, and target
||| well-formedness, but no direct quietness transport theorem.
0 relationalEndpointDoesNotDirectlyTransportQuiet :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (source, target : SystemState name key value world error) ->
  RelationalReplayEndpoint name key world error value nameEq keyEq source target ->
  quiet @{nameEq} @{keyEq} source = True ->
  quiet @{nameEq} @{keyEq} target = True
relationalEndpointDoesNotDirectlyTransportQuiet nameEq keyEq source target
  (MkRelationalReplayEndpoint effects controls targetWellFormed) sourceQuiet =
    sourceQuiet
