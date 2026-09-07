module DGamma.R175OldGroupingPolicyCycle

import Data.List
import Data.Nat

%default total
%unbound_implicits off

||| Cheap ABSTRACT policy regression, not a full O17-input execution fixture.
||| Encode Begin1; Begin0; Finish0; Finish1 by ownership word [1,0,0,1].
||| For each pending actor [0,1], skip to its first node, skip its contiguous
||| run, then test for a remaining owned node: precisely the grouping-before-
||| ordering policy of canonicalWorkInspectScanned / SelectGroupingPair.
||| The first debt is actor1, moving the last node across its foreign neighbor.
||| Reinspection chooses actor0 and moves that same last position back.
||| This proves the abstract selection cycle only; no evaluator/bundle claim.
export
0 r175OldGroupingPolicyCycle :
  (Equal {a = Maybe Nat} {b = Maybe Nat}
    (Data.List.find (\actor => elem actor
      (Data.List.dropWhile (== actor) (Data.List.dropWhile (/= actor) (the (List Nat) [1, 0, 0, 1])))) [0, 1]) (Just 1),
   Equal {a = List Nat} {b = List Nat}
    (1 :: 0 :: Prelude.Types.List.reverse (the (List Nat) [0, 1])) [1, 0, 1, 0],
   Equal {a = Maybe Nat} {b = Maybe Nat}
    (Data.List.find (\actor => elem actor
      (Data.List.dropWhile (== actor) (Data.List.dropWhile (/= actor) (the (List Nat) [1, 0, 1, 0])))) [0, 1]) (Just 0),
   Equal {a = List Nat} {b = List Nat}
    (1 :: 0 :: Prelude.Types.List.reverse (the (List Nat) [1, 0])) [1, 0, 0, 1])
r175OldGroupingPolicyCycle = (Refl, Refl, Refl, Refl)
