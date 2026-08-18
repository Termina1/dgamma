module DGamma.CP4DeletionCommuteCore

import DGamma.Coeffects
import Decidable.Equality

%default total

0 notEqualSymmetric : Not (left = right) -> Not (right = left)
notEqualSymmetric distinct Refl = distinct Refl

||| Deleting a distinct key commutes with adding a fresh binding at the head of
||| the ordered runtime table.  The statement deliberately mentions only the
||| binding list; intrinsic uniqueness witnesses are erased representation data.
public export
0 deleteEntriesAfterDistinctInsert :
  (keyEq : DecEq key) ->
  (inserted, removed : key) ->
  Not (inserted = removed) ->
  (next : value inserted) ->
  (entries : List (Binding key value)) ->
  deleteEntries @{keyEq} removed (Bind inserted next :: entries) =
    Bind inserted next :: deleteEntries @{keyEq} removed entries
deleteEntriesAfterDistinctInsert keyEq inserted removed distinct next entries
  with (decEq @{keyEq} removed inserted)
  deleteEntriesAfterDistinctInsert keyEq inserted inserted distinct next entries |
    Yes Refl = void (distinct Refl)
  deleteEntriesAfterDistinctInsert keyEq inserted removed distinct next entries |
    No different = Refl

0 deleteEntriesOtherHead :
  (keyEq : DecEq key) ->
  (wanted, current : key) ->
  Not (wanted = current) ->
  (old : value current) ->
  (rest : List (Binding key value)) ->
  deleteEntries @{keyEq} wanted (Bind current old :: rest) =
    Bind current old :: deleteEntries @{keyEq} wanted rest
deleteEntriesOtherHead keyEq wanted current distinct old rest
  with (decEq @{keyEq} wanted current)
  deleteEntriesOtherHead keyEq current current distinct old rest | Yes Refl =
    void (distinct Refl)
  deleteEntriesOtherHead keyEq wanted current distinct old rest | No different =
    Refl

0 replaceEntriesOtherHead :
  (keyEq : DecEq key) ->
  (changed, current : key) ->
  Not (changed = current) ->
  (next : value changed) ->
  (old : value current) ->
  (rest : List (Binding key value)) ->
  replaceEntries @{keyEq} changed next (Bind current old :: rest) =
    Bind current old :: replaceEntries @{keyEq} changed next rest
replaceEntriesOtherHead keyEq changed current distinct next old rest
  with (decEq @{keyEq} changed current)
  replaceEntriesOtherHead keyEq current current distinct next old rest | Yes Refl =
    void (distinct Refl)
  replaceEntriesOtherHead keyEq changed current distinct next old rest |
    No different = Refl

||| Distinct replacement and deletion commute on the exact ordered binding
||| list.  No equality of the `UniqueKeys` certificates is asserted.
public export
0 deleteEntriesAfterDistinctReplace :
  (keyEq : DecEq key) ->
  (changed, removed : key) ->
  Not (changed = removed) ->
  (next : value changed) ->
  (entries : List (Binding key value)) ->
  deleteEntries @{keyEq} removed
    (replaceEntries @{keyEq} changed next entries) =
  replaceEntries @{keyEq} changed next
    (deleteEntries @{keyEq} removed entries)
deleteEntriesAfterDistinctReplace keyEq changed removed distinct next [] = Refl
deleteEntriesAfterDistinctReplace keyEq changed removed distinct next
  (Bind current old :: rest)
  with (decEq @{keyEq} changed current) proof changedCurrent
  deleteEntriesAfterDistinctReplace keyEq current removed distinct next
    (Bind current old :: rest) | Yes Refl
    with (decEq @{keyEq} removed current) proof removedCurrent
    deleteEntriesAfterDistinctReplace keyEq current current distinct next
      (Bind current old :: rest) | Yes Refl | Yes Refl =
        void (distinct Refl)
    deleteEntriesAfterDistinctReplace keyEq current removed distinct next
      (Bind current old :: rest) | Yes Refl | No notRemoved
      with (decEq @{keyEq} current current)
      deleteEntriesAfterDistinctReplace keyEq current removed distinct next
        (Bind current old :: rest) | Yes Refl | No notRemoved | Yes Refl = Refl
      deleteEntriesAfterDistinctReplace keyEq current removed distinct next
        (Bind current old :: rest) | Yes Refl | No notRemoved | No absurd =
          void (absurd Refl)
  deleteEntriesAfterDistinctReplace keyEq changed removed distinct next
    (Bind current old :: rest) | No notChanged
    with (decEq @{keyEq} removed current) proof removedCurrent
    deleteEntriesAfterDistinctReplace keyEq changed current distinct next
      (Bind current old :: rest) | No notChanged | Yes Refl = Refl
    deleteEntriesAfterDistinctReplace keyEq changed removed distinct next
      (Bind current old :: rest) | No notChanged | No notRemoved
      with (decEq @{keyEq} removed current)
      deleteEntriesAfterDistinctReplace keyEq changed current distinct next
        (Bind current old :: rest) | No notChanged | No notRemoved | Yes Refl =
          void (notRemoved Refl)
      deleteEntriesAfterDistinctReplace keyEq changed removed distinct next
        (Bind current old :: rest) | No notChanged | No notRemoved | No stillRemoved
        with (decEq @{keyEq} changed current)
        deleteEntriesAfterDistinctReplace keyEq current removed distinct next
          (Bind current old :: rest) | No notChanged | No notRemoved |
          No stillRemoved | Yes Refl = void (notChanged Refl)
        deleteEntriesAfterDistinctReplace keyEq changed removed distinct next
          (Bind current old :: rest) | No notChanged | No notRemoved |
          No stillRemoved | No stillChanged =
            cong (Bind current old ::)
              (deleteEntriesAfterDistinctReplace keyEq changed removed distinct
                next rest)

||| Deletions at two distinct keys commute on the exact ordered binding list.
public export
0 deleteEntriesDistinctCommute :
  (keyEq : DecEq key) ->
  (left, right : key) ->
  Not (left = right) ->
  (entries : List (Binding key value)) ->
  deleteEntries @{keyEq} left (deleteEntries @{keyEq} right entries) =
  deleteEntries @{keyEq} right (deleteEntries @{keyEq} left entries)
deleteEntriesDistinctCommute keyEq left right distinct [] = Refl
deleteEntriesDistinctCommute keyEq left right distinct
  (Bind current old :: rest)
  with (decEq @{keyEq} right current) proof rightCurrent
  deleteEntriesDistinctCommute keyEq left current distinct
    (Bind current old :: rest) | Yes Refl
    with (decEq @{keyEq} left current) proof leftCurrent
    deleteEntriesDistinctCommute keyEq current current distinct
      (Bind current old :: rest) | Yes Refl | Yes Refl =
        void (distinct Refl)
    deleteEntriesDistinctCommute keyEq left current distinct
      (Bind current old :: rest) | Yes Refl | No notLeft
      with (decEq @{keyEq} current current)
      deleteEntriesDistinctCommute keyEq left current distinct
        (Bind current old :: rest) | Yes Refl | No notLeft | Yes Refl = Refl
      deleteEntriesDistinctCommute keyEq left current distinct
        (Bind current old :: rest) | Yes Refl | No notLeft | No absurd =
          void (absurd Refl)
  deleteEntriesDistinctCommute keyEq left right distinct
    (Bind current old :: rest) | No notRight
    with (decEq @{keyEq} left current) proof leftCurrent
    deleteEntriesDistinctCommute keyEq current right distinct
      (Bind current old :: rest) | No notRight | Yes Refl = Refl
    deleteEntriesDistinctCommute keyEq left right distinct
      (Bind current old :: rest) | No notRight | No notLeft
      with (decEq @{keyEq} left current)
      deleteEntriesDistinctCommute keyEq current right distinct
        (Bind current old :: rest) | No notRight | No notLeft | Yes Refl =
          void (notLeft Refl)
      deleteEntriesDistinctCommute keyEq left right distinct
        (Bind current old :: rest) | No notRight | No notLeft | No stillLeft
        with (decEq @{keyEq} right current)
        deleteEntriesDistinctCommute keyEq left current distinct
          (Bind current old :: rest) | No notRight | No notLeft | No stillLeft |
          Yes Refl = void (notRight Refl)
        deleteEntriesDistinctCommute keyEq left right distinct
          (Bind current old :: rest) | No notRight | No notLeft | No stillLeft |
          No stillRight =
            cong (Bind current old ::)
              (deleteEntriesDistinctCommute keyEq left right distinct rest)

||| Observable projection of insertion, independent of its erased uniqueness
||| certificate.
public export
0 insertBindingRuntimeBindings :
  (keyEq : DecEq key) -> (inserted : key) -> (next : value inserted) ->
  (table : CoeffectContext key value) ->
  (0 absent : lookupBinding @{keyEq} inserted table = Nothing) ->
  bindings (insertBinding @{keyEq} inserted next table absent) =
    Bind inserted next :: bindings table
insertBindingRuntimeBindings keyEq inserted next
  (MkCoeffectContext entries unique) absent = Refl

||| Observable projection of replacement.
public export
0 replaceBindingRuntimeBindings :
  (keyEq : DecEq key) -> (changed : key) -> (next : value changed) ->
  (table : CoeffectContext key value) ->
  bindings (replaceBinding @{keyEq} changed next table) =
    replaceEntries @{keyEq} changed next (bindings table)
replaceBindingRuntimeBindings keyEq changed next
  (MkCoeffectContext entries unique) = Refl

||| Observable projection of deletion.
public export
0 deleteBindingRuntimeBindings :
  (keyEq : DecEq key) -> (removed : key) ->
  (table : CoeffectContext key value) ->
  bindings (deleteBinding @{keyEq} removed table) =
    deleteEntries @{keyEq} removed (bindings table)
deleteBindingRuntimeBindings keyEq removed
  (MkCoeffectContext entries unique) = Refl

||| Registry-level observable form of insertion/deletion commutation.
public export
0 deleteBindingAfterDistinctInsertBindings :
  (keyEq : DecEq key) ->
  (inserted, removed : key) ->
  Not (inserted = removed) ->
  (next : value inserted) ->
  (table : CoeffectContext key value) ->
  (0 absent : lookupBinding @{keyEq} inserted table = Nothing) ->
  bindings (deleteBinding @{keyEq} removed
    (insertBinding @{keyEq} inserted next table absent)) =
  Bind inserted next :: bindings (deleteBinding @{keyEq} removed table)
deleteBindingAfterDistinctInsertBindings keyEq inserted removed distinct next
  (MkCoeffectContext entries unique) absent =
    deleteEntriesAfterDistinctInsert keyEq inserted removed distinct next entries

||| Registry-level observable form of replacement/deletion commutation.
public export
0 deleteBindingAfterDistinctReplaceBindings :
  (keyEq : DecEq key) ->
  (changed, removed : key) ->
  Not (changed = removed) ->
  (next : value changed) ->
  (table : CoeffectContext key value) ->
  bindings (deleteBinding @{keyEq} removed
    (replaceBinding @{keyEq} changed next table)) =
  replaceEntries @{keyEq} changed next
    (bindings (deleteBinding @{keyEq} removed table))
deleteBindingAfterDistinctReplaceBindings keyEq changed removed distinct next
  (MkCoeffectContext entries unique) =
    deleteEntriesAfterDistinctReplace keyEq changed removed distinct next entries

||| Registry-level observable form of two distinct deletions commuting.
public export
0 deleteBindingDistinctCommuteBindings :
  (keyEq : DecEq key) ->
  (left, right : key) ->
  Not (left = right) ->
  (table : CoeffectContext key value) ->
  bindings (deleteBinding @{keyEq} left
    (deleteBinding @{keyEq} right table)) =
  bindings (deleteBinding @{keyEq} right
    (deleteBinding @{keyEq} left table))
deleteBindingDistinctCommuteBindings keyEq left right distinct
  (MkCoeffectContext entries unique) =
    deleteEntriesDistinctCommute keyEq left right distinct entries
