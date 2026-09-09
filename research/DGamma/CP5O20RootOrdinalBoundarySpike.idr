module DGamma.CP5O20RootOrdinalBoundarySpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O20CanonicalOrdinalAttachmentSpike

%default total
%unbound_implicits off

||| Exact missing root law for ONE supplied replay correspondence. The field
||| concerns physical occurrence counts, not generated-child ordinals. This
||| is a specification packet, not a producer from arbitrary correspondences.
public export
record O20RootReplayOrdinals
  (name, key, world, error : Type) (value : key -> Type)
  {sourceFirst, sourceFinal, replayedFirst, replayedFinal : SystemState name key value world error}
  {source : Transitions sourceFirst sourceFinal}
  {replayed : Transitions replayedFirst replayedFinal}
  (correspondence : ActionRegistrationReplayCorrespondence name key world error value source replayed) where
  constructor MkO20RootReplayOrdinals
  0 rootReplayOrdinal :
    {root : name} -> {component : Component key value world error} ->
    (occurrence : LocatedActionOccurrence (OInsert root Root component) replayed) ->
    (generationForward (replayGenerationRenaming correspondence)
      (MkRegistrationGeneration root (locatedActionOrdinal (replayActionOrigin correspondence occurrence))) =
      MkRegistrationGeneration root (locatedActionOrdinal occurrence))

||| The literal identity replay owns its root equation on every occurrence.
||| No root correspondence or occurrence-count equality is an input.
export
0 o20IdentityRootReplayOrdinals :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  O20RootReplayOrdinals name key world error value
    (identityActionRegistrationReplayCorrespondence trace)
o20IdentityRootReplayOrdinals trace = MkO20RootReplayOrdinals (\occurrence => Refl)

||| Root laws compose at the SAME intermediate occurrence selected by the
||| right replay. The two input laws remain explicit; no law is extracted
||| from the generated-only field of the correspondence.
export
0 o20ComposeRootReplayOrdinals :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {sourceFirst, sourceFinal, middleFirst, middleFinal, targetFirst, targetFinal : SystemState name key value world error} ->
  {source : Transitions sourceFirst sourceFinal} ->
  {middle : Transitions middleFirst middleFinal} ->
  {target : Transitions targetFirst targetFinal} ->
  (left : ActionRegistrationReplayCorrespondence name key world error value source middle) ->
  (right : ActionRegistrationReplayCorrespondence name key world error value middle target) ->
  O20RootReplayOrdinals name key world error value left ->
  O20RootReplayOrdinals name key world error value right ->
  O20RootReplayOrdinals name key world error value
    (composeActionRegistrationReplayCorrespondence left right)
o20ComposeRootReplayOrdinals left right leftLaw rightLaw =
  MkO20RootReplayOrdinals (\occurrence =>
    trans (cong (generationForward (replayGenerationRenaming right))
      (rootReplayOrdinal leftLaw (replayActionOrigin right occurrence)))
      (rootReplayOrdinal rightLaw occurrence))

||| Two exact root replay laws attach the conjugated ordinal map to the
||| supplied root occurrences. Original occurrence matching is explicit;
||| accepted canonical producers still need to emit the two root laws.
export
0 o20RootOrdinalsAttached :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {leftFirst, leftFinal, rightFirst, rightFinal, leftNowFirst, leftNowFinal, rightNowFirst, rightNowFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
  {leftNow : Transitions leftNowFirst leftNowFinal} -> {rightNow : Transitions rightNowFirst rightNowFinal} ->
  (leftReplay : ActionRegistrationReplayCorrespondence name key world error value left leftNow) ->
  (rightReplay : ActionRegistrationReplayCorrespondence name key world error value right rightNow) ->
  O20RootReplayOrdinals name key world error value leftReplay ->
  O20RootReplayOrdinals name key world error value rightReplay ->
  (original : RegistrationGenerationBijection name) ->
  {root : name} -> {component : Component key value world error} ->
  (leftBirth : LocatedActionOccurrence (OInsert root Root component) leftNow) ->
  (rightBirth : LocatedActionOccurrence (OInsert root Root component) rightNow) ->
  (generationForward original
    (MkRegistrationGeneration root (locatedActionOrdinal (replayActionOrigin leftReplay leftBirth))) =
    MkRegistrationGeneration root (locatedActionOrdinal (replayActionOrigin rightReplay rightBirth))) ->
  (generationForward (o20ReplayOrdinalBijection (replayGenerationRenaming leftReplay) original (replayGenerationRenaming rightReplay))
    (MkRegistrationGeneration root (locatedActionOrdinal leftBirth)) =
    MkRegistrationGeneration root (locatedActionOrdinal rightBirth))
o20RootOrdinalsAttached {root} leftReplay rightReplay leftLaw rightLaw original leftBirth rightBirth matched =
  o20ReplayOrdinalMatched (replayGenerationRenaming leftReplay) original (replayGenerationRenaming rightReplay)
    (MkRegistrationGeneration root (locatedActionOrdinal (replayActionOrigin leftReplay leftBirth)))
    (MkRegistrationGeneration root (locatedActionOrdinal (replayActionOrigin rightReplay rightBirth)))
    (MkRegistrationGeneration root (locatedActionOrdinal leftBirth))
    (MkRegistrationGeneration root (locatedActionOrdinal rightBirth))
    (rootReplayOrdinal leftLaw leftBirth) (rootReplayOrdinal rightLaw rightBirth) matched
