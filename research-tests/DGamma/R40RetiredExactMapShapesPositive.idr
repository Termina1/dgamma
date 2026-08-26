module DGamma.R40RetiredExactMapShapesPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory

%default total

||| Historical revision-19 RAR generator-map field.  This is a retired shape,
||| not live replay authority: the landed record uses `replayGeneratorMapsRelated`.
public export
RetiredExactRelationalReplayGeneratorMapPreservation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {sourceFirst, sourceFinal, replayedFirst, replayedFinal :
    SystemState name key value world error} ->
  (source : Transitions sourceFirst sourceFinal) ->
  (replayed : Transitions replayedFirst replayedFinal) ->
  ((actor : name) ->
    TraceEffectGenerator name key world error value actor replayed ->
    TraceEffectGenerator name key world error value actor source) -> Type
RetiredExactRelationalReplayGeneratorMapPreservation name key world error value
  source replayed origin =
    (actor : name) ->
    (generator : TraceEffectGenerator name key world error value actor replayed) ->
    (state : EffectState name key value world) ->
    traceGeneratorMap (origin actor generator) state =
      traceGeneratorMap generator state

||| Historical private pointwise-head exact map field.
public export
RetiredExactPointwiseHeadMapPreservation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {sourceBefore, sourceAfter, replayedBefore, replayedAfter :
    SystemState name key value world error} ->
  Transition sourceBefore sourceAfter ->
  Transition replayedBefore replayedAfter -> Type
RetiredExactPointwiseHeadMapPreservation name key world error value sourceStep
  replayedStep =
    (state : EffectState name key value world) ->
    partialEffectMap sourceStep state = partialEffectMap replayedStep state

||| Historical revision-19 sealed-spine exact head capital.  It deliberately
||| remains a distinct name even though its old shape matched the pointwise field.
public export
RetiredExactSealedSuffixHeadMapPreservation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {sourceBefore, sourceAfter, replayedBefore, replayedAfter :
    SystemState name key value world error} ->
  Transition sourceBefore sourceAfter ->
  Transition replayedBefore replayedAfter -> Type
RetiredExactSealedSuffixHeadMapPreservation name key world error value sourceStep
  replayedStep =
    (state : EffectState name key value world) ->
    partialEffectMap sourceStep state = partialEffectMap replayedStep state

||| Exact equality still embeds into either retired private shape; this witness
||| makes the pins executable declaration checks rather than comment-only names.
public export
0 r40RetiredHeadShapesAgree :
  (sourceStep : Transition sourceBefore sourceAfter) ->
  (replayedStep : Transition replayedBefore replayedAfter) ->
  RetiredExactPointwiseHeadMapPreservation name key world error value sourceStep
    replayedStep ->
  RetiredExactSealedSuffixHeadMapPreservation name key world error value
    sourceStep replayedStep
r40RetiredHeadShapesAgree sourceStep replayedStep exact = exact
