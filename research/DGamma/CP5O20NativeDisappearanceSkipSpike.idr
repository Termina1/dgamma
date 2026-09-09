module DGamma.CP5O20NativeDisappearanceSkipSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5O20WholeClosingJoinSpike
import DGamma.CP5O20RetainedClosingIndexSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Control.Relation
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Executable SOURCE-to-survivor physical position map for the actual native
||| filtering derivation. A deleted head consumes one SOURCE edge and no
||| target edge. Nothing denotes a removed or out-of-range source slot; it is
||| never an assertion that the source step is a zero-length native path.
public export
o20SubsequenceTargetOrdinal :
  {0 name, key, world, error : Type} -> {0 value : key -> Type} ->
  {0 nameEq : DecEq name} ->
  {0 deletable : Nat -> GenerationEnvironment name -> Action name key value world error -> Type} ->
  {0 ordinal : Nat} -> {0 live : GenerationEnvironment name} ->
  {0 first, finalState, otherFirst, otherFinal : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} -> {0 survivor : Transitions otherFirst otherFinal} ->
  GenerationActionSubsequence nameEq deletable ordinal live trace survivor -> Nat -> Maybe Nat
o20SubsequenceTargetOrdinal GenerationActionSubsequenceEnd source = Nothing
o20SubsequenceTargetOrdinal (KeepGenerationAction step rest target later outside same tail) Z = Just Z
o20SubsequenceTargetOrdinal (KeepGenerationAction step rest target later outside same tail) (S source) =
  map S (o20SubsequenceTargetOrdinal tail source)
o20SubsequenceTargetOrdinal (DeleteGenerationAction step rest deleted tail) Z = Nothing
o20SubsequenceTargetOrdinal (DeleteGenerationAction step rest deleted tail) (S source) =
  o20SubsequenceTargetOrdinal tail source
