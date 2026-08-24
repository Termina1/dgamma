module DGamma.R21WholeBundleQuietTransportNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

||| Historical revision-21 transport-shape pin. Revision 22 supersedes this as
||| the active fixture diagnosis: the concrete R20 source endpoint is itself not
||| quiet, so no authenticated source `ReplayInvariantBundle` exists. This probe
||| still records that a bare endpoint has no direct quietness projection.
0 relationalEndpointDoesNotDirectlyTransportQuiet :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (source, target : SystemState name key value world error) ->
  RelationalReplayEndpoint name key world error value nameEq keyEq source target ->
  quiet @{nameEq} @{keyEq} source = True ->
  quiet @{nameEq} @{keyEq} target = True
relationalEndpointDoesNotDirectlyTransportQuiet nameEq keyEq source target
  (MkRelationalReplayEndpoint effects controls targetWellFormed) sourceQuiet =
    sourceQuiet
