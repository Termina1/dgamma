module DGamma.CP4DeletionSelectedCloseEffect

import DGamma.Core
import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP4DeletionSelectedEffectCore
import DGamma.CP4RecoveryTrace
import DGamma.CP4TerminalRecovery
import Decidable.Equality

%default total

||| The selected quotient's L-Unload effect join.  The checked closing step and
||| the intermediate boundary expose the same concrete runtime accumulator;
||| therefore the survivor's recovered projection is exactly the effect state
||| related to the original post-close target.
public export
0 selectedUnloadClosesEffectBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (boundary : SelectedEffectReplayBoundary name key world error value nameEq
    keyEq selected whole before survivor) ->
  (closing : UnloadStep nameEq keyEq selected before afterState) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} afterState)
    (projectEffectState @{nameEq} survivor)
selectedUnloadClosesEffectBoundary nameEq keyEq selected before afterState
  survivor whole
  (MkSelectedEffectReplayBoundary model boundaryRecovered boundaryRuns
    survivorToRecovered)
  closing =
    case closingStepAccumulatorResult nameEq keyEq selected before afterState
      closing of
      MkClosingAccumulatorResult handle handleAt closingRecoveredValue
        closingRuns closingToAfter =>
          let 0 handleSame = justInjective (trans (sym handleAt)
                (modelHandleAt model))
              0 closingRunsWithModel = replace
                {p = \observed => accumulatorEffectMap nameEq keyEq selected
                  observed (projectEffectState @{nameEq} before) =
                    Just closingRecoveredValue}
                handleSame closingRuns
              0 recoveredSame = justInjective (trans (sym boundaryRuns)
                closingRunsWithModel)
              0 survivorToClosing : EffectStateRelated keyEq
                (projectEffectState @{nameEq} survivor) closingRecoveredValue
              survivorToClosing = replace
                {p = \observed => EffectStateRelated keyEq
                  (projectEffectState @{nameEq} survivor) observed}
                recoveredSame survivorToRecovered
              0 survivorToAfter : EffectStateRelated keyEq
                (projectEffectState @{nameEq} survivor)
                (projectEffectState @{nameEq} afterState)
              survivorToAfter = transitive (EffectStateEquivalence keyEq)
                survivorToClosing closingToAfter
          in symmetric (EffectStateEquivalence keyEq) survivorToAfter
