module DGamma.L2R5RootCatalog

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R4OrdinalObservation
import Data.List.Elem
import Data.Maybe
import Data.Nat

%default total
%unbound_implicits off

||| Runtime root-insertion catalog item: original physical ordinal, actor and
||| actual component. No forced-root classification or bundle is asserted.
public export
record RootCatalogEntry
  (name, key, world, error : Type) (value : key -> Type) where
  constructor MkRootCatalogEntry
  catalogOrdinal : Nat
  catalogRoot : name
  catalogComponent : Component key value world error

||| Exhaustive runtime Action classifier: only OInsert Root adds an entry.
||| Child Insert, root Retire/Remove and every lifecycle action are not births.
public export
rootCatalogStep : {name, key, world, error : Type} -> {value : key -> Type} ->
  Nat -> Action name key value world error ->
  List (RootCatalogEntry name key world error value) -> List (RootCatalogEntry name key world error value)
rootCatalogStep ordinal (OInsert root Root component) later = MkRootCatalogEntry ordinal root component :: later
rootCatalogStep ordinal (OInsert actor (ChildOf parent) component) later = later
rootCatalogStep ordinal (ORetire actor) later = later
rootCatalogStep ordinal (ORemove actor) later = later
rootCatalogStep ordinal (LBegin actor) later = later
rootCatalogStep ordinal (LAdvance actor) later = later
rootCatalogStep ordinal (LDivert actor) later = later
rootCatalogStep ordinal (LUnload actor) later = later
rootCatalogStep ordinal (LLeave actor) later = later

||| Total executable catalog scan FROM the actual checked native trail. All
||| input ordinals advance, including non-birth actions; no catalog is supplied.
public export
scanRootCatalog : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  (offset : Nat) -> AvailabilityTrace name key world error value trace ->
  List (RootCatalogEntry name key world error value)
scanRootCatalog offset (AvailabilityEnd state) = []
scanRootCatalog offset (AvailabilityStep first (Fired nameEq keyEq action tag checked) rest later) =
  rootCatalogStep offset action (scanRootCatalog (S offset) later)

||| A catalog member with producer-owned action and ordinal equations. This
||| authenticates a raw birth catalog only, NOT an AttachedBundleOccurrence.
public export
record RootCatalogContains
  (name, key, world, error : Type) (value : key -> Type)
  (0 entries : List (RootCatalogEntry name key world error value))
  (ordinal : Nat) (action : Action name key value world error) where
  constructor MkRootCatalogContains
  catalogItem : RootCatalogEntry name key world error value
  0 itemPresent : Elem catalogItem entries
  0 itemOrdinal : catalogOrdinal catalogItem = ordinal
  0 itemAction : OInsert (catalogRoot catalogItem) Root (catalogComponent catalogItem) = action

||| A head action observed as a root insertion is genuinely inserted by the
||| runtime classifier. Exhaustive Action elimination, no pre-supplied member.
export
0 rootCatalogHeadComplete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (offset : Nat) -> (action : Action name key value world error) ->
  (later : List (RootCatalogEntry name key world error value)) ->
  (root : name) -> (component : Component key value world error) ->
  (0 exact : action = OInsert root Root component) ->
  RootCatalogContains name key world error value (rootCatalogStep offset action later) offset (OInsert root Root component)
rootCatalogHeadComplete {name} {key} {world} {error} {value} offset (OInsert own Root ownComponent) later root component exact =
  replace {p = RootCatalogContains name key world error value
    (rootCatalogStep offset (OInsert own Root ownComponent) later) offset} exact
    (MkRootCatalogContains (MkRootCatalogEntry offset own ownComponent) Here Refl Refl)
rootCatalogHeadComplete offset (OInsert _ (ChildOf parent) _) later root component Refl impossible
rootCatalogHeadComplete offset (ORetire actor) later root component Refl impossible
rootCatalogHeadComplete offset (ORemove actor) later root component Refl impossible
rootCatalogHeadComplete offset (LBegin actor) later root component Refl impossible
rootCatalogHeadComplete offset (LAdvance actor) later root component Refl impossible
rootCatalogHeadComplete offset (LDivert actor) later root component Refl impossible
rootCatalogHeadComplete offset (LUnload actor) later root component Refl impossible
rootCatalogHeadComplete offset (LLeave actor) later root component Refl impossible

||| Membership from the scanned tail survives EVERY head action, whether or
||| not the head contributes an entry. Exact item action/ordinal are retained.
export
0 rootCatalogTailComplete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (offset : Nat) -> (action : Action name key value world error) ->
  (later : List (RootCatalogEntry name key world error value)) ->
  (ordinal : Nat) -> (wanted : Action name key value world error) ->
  RootCatalogContains name key world error value later ordinal wanted ->
  RootCatalogContains name key world error value (rootCatalogStep offset action later) ordinal wanted
rootCatalogTailComplete offset (OInsert root Root component) later ordinal wanted member =
  MkRootCatalogContains (catalogItem member) (There (itemPresent member)) (itemOrdinal member) (itemAction member)
rootCatalogTailComplete offset (OInsert actor (ChildOf parent) component) later ordinal wanted member = member
rootCatalogTailComplete offset (ORetire actor) later ordinal wanted member = member
rootCatalogTailComplete offset (ORemove actor) later ordinal wanted member = member
rootCatalogTailComplete offset (LBegin actor) later ordinal wanted member = member
rootCatalogTailComplete offset (LAdvance actor) later ordinal wanted member = member
rootCatalogTailComplete offset (LDivert actor) later ordinal wanted member = member
rootCatalogTailComplete offset (LUnload actor) later ordinal wanted member = member
rootCatalogTailComplete offset (LLeave actor) later ordinal wanted member = member

||| One ordinal elimination extends tail lookup-completeness to a native cons
||| trace. Count equalities transport offsets rather than unifying indices.
export
0 rootCatalogConsComplete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (later : AvailabilityTrace name key world error value rest) -> (offset : Nat) ->
  (0 tail : (ordinal : Nat) -> (root : name) -> (component : Component key value world error) ->
    nativeActionAt rest ordinal = Just (OInsert root Root component) ->
    RootCatalogContains name key world error value (scanRootCatalog (S offset) later) (S offset + ordinal) (OInsert root Root component)) ->
  (ordinal : Nat) -> (root : name) -> (component : Component key value world error) ->
  nativeActionAt (MoreTransitions step rest) ordinal = Just (OInsert root Root component) ->
  RootCatalogContains name key world error value
    (rootCatalogStep offset (transitionAction step) (scanRootCatalog (S offset) later)) (offset + ordinal) (OInsert root Root component)
rootCatalogConsComplete {name} {key} {world} {error} {value} step rest later offset tail Z root component exact =
  replace {p = \position => RootCatalogContains name key world error value
    (rootCatalogStep offset (transitionAction step) (scanRootCatalog (S offset) later)) position (OInsert root Root component)}
    (sym (plusZeroRightNeutral offset))
    (rootCatalogHeadComplete offset (transitionAction step) (scanRootCatalog (S offset) later) root component (justInjective exact))
rootCatalogConsComplete {name} {key} {world} {error} {value} step rest later offset tail (S n) root component exact =
  replace {p = \position => RootCatalogContains name key world error value
    (rootCatalogStep offset (transitionAction step) (scanRootCatalog (S offset) later)) position (OInsert root Root component)}
    (plusSuccRightSucc offset n)
    (rootCatalogTailComplete offset (transitionAction step) (scanRootCatalog (S offset) later)
      (S offset + n) (OInsert root Root component) (tail n root component exact))

||| GENERAL lookup completeness of the catalog GENERATED FROM the trace.
||| Every native root insertion lookup appears with the same ordinal/action;
||| no caller-supplied catalog or completeness callback. This is NOT bundle
||| assignment, front-normal placement, or AttachedNormalForm coverage.
export
0 scanRootLookupComplete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (offset : Nat) -> (trail : AvailabilityTrace name key world error value trace) ->
  (ordinal : Nat) -> (root : name) -> (component : Component key value world error) ->
  nativeActionAt trace ordinal = Just (OInsert root Root component) ->
  RootCatalogContains name key world error value (scanRootCatalog offset trail) (offset + ordinal) (OInsert root Root component)
scanRootLookupComplete offset (AvailabilityEnd state) ordinal root component exact = void (nothingIsNotJust exact)
scanRootLookupComplete offset (AvailabilityStep first (Fired nameEq keyEq action tag checked) rest later) ordinal root component exact =
  rootCatalogConsComplete (Fired nameEq keyEq action tag checked) rest later offset
    (scanRootLookupComplete (S offset) later) ordinal root component exact
