module DGamma.CP4DeletionGenerationScan

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Data.List.Elem
import Decidable.Equality

%default total

public export
record GenerationScanResult
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name)
  {first, finalState : SystemState name key value world error}
  (startOrdinal : Nat) (startLive : GenerationEnvironment name)
  (trace : Transitions first finalState) where
  constructor MkGenerationScanResult
  scanFinalOrdinal : Nat
  scanFinalLive : GenerationEnvironment name
  0 generationScan : GenerationTraceScan nameEq startOrdinal startLive trace
    scanFinalOrdinal scanFinalLive

||| Every finite checked trace has a constructive generation scan.
public export
scanGenerations :
  (nameEq : DecEq name) ->
  (startOrdinal : Nat) -> (startLive : GenerationEnvironment name) ->
  (trace : Transitions first finalState) ->
  GenerationScanResult name key world error value nameEq startOrdinal startLive
    trace
scanGenerations {name} {key} {world} {error} {value}
  nameEq startOrdinal startLive NoTransitions =
  MkGenerationScanResult startOrdinal startLive GenerationTraceScanEnd
scanGenerations {name} {key} {world} {error} {value}
  nameEq startOrdinal startLive
  (MoreTransitions (Fired stepNameEq stepKeyEq action tag checked) rest) =
    case scanGenerations nameEq (S startOrdinal)
      (advanceGenerationEnvironment @{nameEq} startOrdinal action startLive)
      rest of
      MkGenerationScanResult finalOrdinal finalLive tail =>
        MkGenerationScanResult finalOrdinal finalLive
          (GenerationTraceScanStep
            (Fired stepNameEq stepKeyEq action tag checked) rest tail)

