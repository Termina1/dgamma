module DGamma.CP5O20SelectionCompletenessSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O20SafeBlockSelectionSpike
import DGamma.CP5O20LinearExtensionSpike
import DGamma.CP5O20OperationalProgressSpike
import DGamma.CP5O20OperationalDescentSpike
import DGamma.CP5O20RightOpeningTransportSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5RankedEarlyApplicabilitySpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Map preserves actual Maybe success without selecting or equating payloads.
export
0 o20MapMaybePresent : {a, b : Type} -> (make : a -> b) ->
  (source : Maybe a) -> isJust source = True -> isJust (map make source) = True
o20MapMaybePresent make Nothing Refl impossible
o20MapMaybePresent make (Just value) present = Refl

||| Any strict BeforeIn on a nonempty list puts its RIGHT member in the tail.
export
0 o20BeforeRightInTail :
  {name : Type} -> {left, right, head : name} -> {rest : List name} ->
  BeforeIn left right (head :: rest) -> Elem right rest
o20BeforeRightInTail (BeforeHere member) = member
o20BeforeRightInTail (BeforeThere later) = snd (o20BeforeMembers later)
