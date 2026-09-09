module DGamma.L2R12InventoryDomain

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.EqOrd
import Prelude.Num
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R191CanonicalChildRetirementGap
import DGamma.L2R11WordInventory
import DGamma.L2R12PhaseAccepted
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Native finite-inventory acceptance discharges the kind premise for ANY
||| actual-word action. Unsupported kinds contradict their own inventory bit.
export
0 inventoryAdmittedKind : {name, key, world, error : Type} -> {value : key -> Type} ->
  (word : List (Action name key value world error)) ->
  (action : Action name key value world error) ->
  (0 restricted : all (\code => not (wordActionInventory word code) ||
    elemDec code [0, 1, 2, 3, 4]) [0, 1, 2, 3, 4, 5, 6, 7] = True) ->
  (0 present : wordActionInventory word (actionKindCode action) = True) ->
  Elem (actionKindCode action) [0, 1, 2, 3, 4]
inventoryAdmittedKind word (LBegin actor) restricted present = Here
inventoryAdmittedKind word (LAdvance actor) restricted present = There (Here)
inventoryAdmittedKind word (OInsert child parent component) restricted present = There (There (Here))
inventoryAdmittedKind word (ORetire child) restricted present = There (There (There (Here)))
inventoryAdmittedKind word (ORemove child) restricted present = There (There (There (There (Here))))
inventoryAdmittedKind word (LDivert actor) restricted present =
  absurd (replace {p = \seen => not seen || elemDec (the Nat 5) [0, 1, 2, 3, 4] = True}
    present (phaseAllMember {a = Nat} {item = 5} {items = [0, 1, 2, 3, 4, 5, 6, 7]} (\code => not (wordActionInventory word code) ||
      elemDec code [0, 1, 2, 3, 4]) (There (There (There (There (There (Here)))))) restricted))
inventoryAdmittedKind word (LLeave actor) restricted present =
  absurd (replace {p = \seen => not seen || elemDec (the Nat 6) [0, 1, 2, 3, 4] = True}
    present (phaseAllMember {a = Nat} {item = 6} {items = [0, 1, 2, 3, 4, 5, 6, 7]} (\code => not (wordActionInventory word code) ||
      elemDec code [0, 1, 2, 3, 4]) (There (There (There (There (There (There (Here))))))) restricted))
inventoryAdmittedKind word (LUnload actor) restricted present =
  absurd (replace {p = \seen => not seen || elemDec (the Nat 7) [0, 1, 2, 3, 4] = True}
    present (phaseAllMember {a = Nat} {item = 7} {items = [0, 1, 2, 3, 4, 5, 6, 7]} (\code => not (wordActionInventory word code) ||
      elemDec code [0, 1, 2, 3, 4]) (There (There (There (There (There (There (There (Here)))))))) restricted))
