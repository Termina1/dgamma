module DGamma.CP5O20RetainedClosingIndexSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5O20DeletionRetainedUnloadSpike
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Locate a REAL closing witness by its physical suffix index. This is not
||| an arbitrary index premise and does not yet transport a deletion.
export
0 o20UnloadOccurrenceIndex :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> (actor : name) ->
  ActionOccurs (LUnload actor) trace ->
  (ordinal : Nat ** (rawClosingActionAt name key world error value ordinal trace = Just (LUnload actor)))
o20UnloadOccurrenceIndex name key world error value _ actor
  (ActionOccursHere (Fired nameEq keyEq action tag checked) rest exact) =
    (Z ** cong Just exact)
o20UnloadOccurrenceIndex name key world error value _ actor
  (ActionOccursLater step rest later) =
    case o20UnloadOccurrenceIndex name key world error value rest actor later of
      (ordinal ** exact) => (S ordinal ** exact)
