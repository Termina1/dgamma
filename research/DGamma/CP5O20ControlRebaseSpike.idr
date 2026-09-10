module DGamma.CP5O20ControlRebaseSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O20EpisodeSynchronizationSpike
import DGamma.CP5O20AllNameSynchronizationSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Primitive referenced-name transport, requiring agreement only on this
||| concrete finite list. No equality of functions or bijection records is used.
export
0 o20RebaseMappedNames :
  {name : Type} -> (before, after : NameBijection name) -> (names : List name) ->
  (0 agree : (selected : name) -> Elem selected names ->
    renameForward before selected = renameForward after selected) ->
  map (renameForward after) names = map (renameForward before) names
o20RebaseMappedNames before after [] agree = Refl
o20RebaseMappedNames before after (head :: rest) agree =
  rewrite sym (agree head Here) in
    cong (renameForward before head ::)
      (o20RebaseMappedNames before after rest (\selected, member => agree selected (There member)))
