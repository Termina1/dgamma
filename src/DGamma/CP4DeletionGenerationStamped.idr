module DGamma.CP4DeletionGenerationStamped

import DGamma.Calculus
import DGamma.CP3
import Data.List.Elem
import Decidable.Equality

%default total

||| Scanner coherence omitted from plain `GenerationEnvironment`: every map key
||| is the raw name carried by its current generation stamp.  Starting from the
||| empty scanner this is preserved by every action.
public export
0 GenerationEnvironmentStamped : GenerationEnvironment name -> Type
GenerationEnvironmentStamped live =
  (actor : name) -> (generation : RegistrationGeneration name) ->
  Elem (actor, generation) live -> generationName generation = actor

0 putCurrentGenerationPreservesStamped :
  (nameEq : DecEq name) -> (inserted : name) -> (ordinal : Nat) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentStamped live ->
  GenerationEnvironmentStamped
    (putCurrentGeneration @{nameEq} inserted
      (MkRegistrationGeneration inserted ordinal) live)
putCurrentGenerationPreservesStamped nameEq inserted ordinal [] stamped actor
  generation present = case present of
    Here => Refl
    There later => case later of Here impossible; There rest impossible
putCurrentGenerationPreservesStamped nameEq inserted ordinal
  ((candidate, current) :: rest) stamped actor generation present
  with (decEq @{nameEq} inserted candidate)
  putCurrentGenerationPreservesStamped nameEq candidate ordinal
    ((candidate, current) :: rest) stamped actor generation present | Yes Refl =
      case present of
        Here => Refl
        There later => stamped actor generation (There later)
  putCurrentGenerationPreservesStamped nameEq inserted ordinal
    ((candidate, current) :: rest) stamped actor generation present |
    No insertedDifferent = case present of
      Here => stamped candidate current Here
      There later => putCurrentGenerationPreservesStamped nameEq inserted ordinal
        rest (\selected, observed, occurs =>
          stamped selected observed (There occurs)) actor generation later

0 deleteCurrentGenerationPreservesStamped :
  (nameEq : DecEq name) -> (removed : name) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentStamped live ->
  GenerationEnvironmentStamped (deleteCurrentGeneration @{nameEq} removed live)
deleteCurrentGenerationPreservesStamped nameEq removed [] stamped actor generation
  present = case present of Here impossible; There later impossible
deleteCurrentGenerationPreservesStamped nameEq removed
  ((candidate, current) :: rest) stamped actor generation present
  with (decEq @{nameEq} removed candidate)
  deleteCurrentGenerationPreservesStamped nameEq candidate
    ((candidate, current) :: rest) stamped actor generation present | Yes Refl =
      stamped actor generation (There present)
  deleteCurrentGenerationPreservesStamped nameEq removed
    ((candidate, current) :: rest) stamped actor generation present |
    No removedDifferent = case present of
      Here => stamped candidate current Here
      There later => deleteCurrentGenerationPreservesStamped nameEq removed rest
        (\selected, observed, occurs =>
          stamped selected observed (There occurs)) actor generation later

public export
0 advanceGenerationEnvironmentPreservesStamped :
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (action : Action name key value world error) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentStamped live ->
  GenerationEnvironmentStamped
    (advanceGenerationEnvironment @{nameEq} ordinal action live)
advanceGenerationEnvironmentPreservesStamped nameEq ordinal
  (OInsert inserted parent component) live stamped =
    putCurrentGenerationPreservesStamped nameEq inserted ordinal live stamped
advanceGenerationEnvironmentPreservesStamped nameEq ordinal (ORemove removed)
  live stamped =
    deleteCurrentGenerationPreservesStamped nameEq removed live stamped
advanceGenerationEnvironmentPreservesStamped nameEq ordinal (ORetire actor) live
  stamped = stamped
advanceGenerationEnvironmentPreservesStamped nameEq ordinal (LBegin actor) live
  stamped = stamped
advanceGenerationEnvironmentPreservesStamped nameEq ordinal (LAdvance actor) live
  stamped = stamped
advanceGenerationEnvironmentPreservesStamped nameEq ordinal (LDivert actor) live
  stamped = stamped
advanceGenerationEnvironmentPreservesStamped nameEq ordinal (LLeave actor) live
  stamped = stamped
advanceGenerationEnvironmentPreservesStamped nameEq ordinal (LUnload actor) live
  stamped = stamped

||| Simultaneous scanner induction used by the selected quotient and endpoint
||| generation proofs.
public export
0 generationTraceScanPreservesStamped :
  (nameEq : DecEq name) ->
  (scan : GenerationTraceScan
    {name = name} {key = key} {value = value} {world = world} {error = error}
    nameEq ordinal live trace finalOrdinal finalLive) ->
  GenerationEnvironmentStamped live ->
  GenerationEnvironmentStamped finalLive
generationTraceScanPreservesStamped nameEq GenerationTraceScanEnd stamped =
  stamped
generationTraceScanPreservesStamped nameEq
  (GenerationTraceScanStep transition rest tail) stamped =
    generationTraceScanPreservesStamped nameEq tail
      (advanceGenerationEnvironmentPreservesStamped nameEq _
        (transitionAction transition) _ stamped)

public export
0 emptyGenerationEnvironmentStamped : GenerationEnvironmentStamped []
emptyGenerationEnvironmentStamped actor generation present = case present of
  Here impossible
  There later impossible
