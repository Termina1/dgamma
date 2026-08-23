module DGamma.R8WholeBlockShiftedNodeNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

||| Probe-50 reconstruction: reuse the exact same current node and replay origin
||| while changing only its selected repeated-step position from 0 to 1.
||| Occurrence-authenticated source ordinals must make this ill-typed.
public export
0 relabelExactSameNodeAtNextPosition :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {sourceInitial, sourceFinal, currentInitial, currentFinal :
    SystemState name key value world error} ->
  {sourceTrace : Transitions sourceInitial sourceFinal} ->
  {currentTrace : Transitions currentInitial currentFinal} ->
  {occurrences : ActionRegistrationReplayCorrespondence name key world error
    value sourceTrace currentTrace} ->
  {actor : name} ->
  {block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq actor
    sourceTrace} ->
  {action : Action name key value world error} ->
  {nodeOrdinal : Nat} ->
  NodeCrossesSourceBlockPosition name key world error value nameEq keyEq
    sourceTrace currentTrace occurrences block 0 action nodeOrdinal ->
  NodeCrossesSourceBlockPosition name key world error value nameEq keyEq
    sourceTrace currentTrace occurrences block 1 action nodeOrdinal
relabelExactSameNodeAtNextPosition label = label
