module DGamma.CP5O19ActivationResolutionSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4ProgressReliance
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionSelectedOwn
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceSelected
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Declared-key exclusion forces the ACTUAL provider candidate to be false,
||| irrespective of the lifecycle or table contents. Observe the Boolean once.
export
0 o19NonProviderObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (keyEq : DecEq key) -> (wanted : key) -> (fiber : Fiber name key value world error) ->
  (observed : Bool) -> (providerCandidate @{keyEq} wanted fiber = observed) ->
  Not (Elem wanted (dependencies (componentProvisions (fiberComponent fiber)))) ->
  observed = False
o19NonProviderObserved keyEq wanted fiber False exact excluded = Refl
o19NonProviderObserved keyEq wanted fiber True exact excluded =
  void (excluded (selectedCandidateDeclaresRelianceAnchor keyEq wanted fiber exact))

||| Separate observed-Boolean boundary approved after E2. The unchanged head
||| is decided from its actual candidate/equation, never by lazy-if congruence.
export
0 o19ProviderHeadObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) -> (current : name) ->
  (fiber : Fiber name key value world error) ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  (observed : Bool) ->
  (isActive (fiberLifecycle fiber) && memberKey @{keyEq} wanted (ownedValues (fiberTable fiber)) = observed) ->
  (providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted left =
   providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted right) ->
  (providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted (Bind current fiber :: left) =
   providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted (Bind current fiber :: right))
o19ProviderHeadObserved nameEq keyEq wanted current fiber left right False exact tailSame = rewrite exact in tailSame
o19ProviderHeadObserved nameEq keyEq wanted current fiber left right True exact tailSame = rewrite exact in Refl


||| E4 consumes the independently checked observed-Boolean head boundary.
export
0 o19ProviderReplaceHeadObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) ->
  (actor, current : name) -> (old, next : Fiber name key value world error) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  (decision : Dec (actor = current)) -> (decEq @{nameEq} actor current = decision) ->
  (providerCandidate @{keyEq} wanted next = False) ->
  ((actor = current) -> providerCandidate @{keyEq} wanted old = False) ->
  (providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted (replaceEntries @{nameEq} actor next rest) = providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted rest) ->
  (providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted (replaceEntries @{nameEq} actor next (Bind current old :: rest)) =
   providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted (Bind current old :: rest))
o19ProviderReplaceHeadObserved nameEq keyEq wanted actor _ old next rest (Yes Refl) exact nextFalse oldFalse tailSame =
  rewrite exact in rewrite nextFalse in rewrite oldFalse Refl in Refl
o19ProviderReplaceHeadObserved nameEq keyEq wanted actor current old next rest (No distinct) exact nextFalse oldFalse tailSame =
  rewrite exact in o19ProviderHeadObserved nameEq keyEq wanted current old
    (replaceEntries @{nameEq} actor next rest) rest
    (isActive (fiberLifecycle old) && memberKey @{keyEq} wanted (ownedValues (fiberTable old))) Refl tailSame

||| Induction on the ACTUAL ordered registry entries. Every unchanged head
||| passes through E3; the selected head is absent as a provider on both sides.
export
0 o19ProviderReplaceEntries :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) ->
  (actor : name) -> (next : Fiber name key value world error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (providerCandidate @{keyEq} wanted next = False) ->
  ((old : Fiber name key value world error) -> Elem (Bind actor old) entries -> providerCandidate @{keyEq} wanted old = False) ->
  (providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted (replaceEntries @{nameEq} actor next entries) =
   providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted entries)
o19ProviderReplaceEntries nameEq keyEq wanted actor next [] nextFalse excluded = Refl
o19ProviderReplaceEntries nameEq keyEq wanted actor next (Bind current old :: rest) nextFalse excluded =
  o19ProviderReplaceHeadObserved nameEq keyEq wanted actor current old next rest
    (decEq @{nameEq} actor current) Refl nextFalse
    (\same => excluded old (rewrite same in Here))
    (o19ProviderReplaceEntries nameEq keyEq wanted actor next rest nextFalse (\fiber, occurs => excluded fiber (There occurs)))

||| Replacement provider equality from a located source component's declared
||| nondependency and immutable component metadata. No candidate oracle remains.
export
0 o19ProviderReplaceNonDependency :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) -> (actor : name) ->
  (source : Registry name key value world error) -> (old, next : Fiber name key value world error) ->
  (lookupFiber @{nameEq} actor source = Just old) -> (fiberComponent next = fiberComponent old) ->
  Not (Elem wanted (dependencies (componentProvisions (fiberComponent old)))) ->
  (providerOf {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted (replaceBinding @{nameEq} actor next source) =
   providerOf {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted source)
o19ProviderReplaceNonDependency nameEq keyEq wanted actor (MkCoeffectContext entries unique) old next found static excluded =
  o19ProviderReplaceEntries nameEq keyEq wanted actor next entries
    (o19NonProviderObserved keyEq wanted next (providerCandidate @{keyEq} wanted next) Refl (rewrite static in excluded))
    (\fiber, occurs =>
      rewrite justInjective (trans (sym (lookupEntryFromElem nameEq entries unique occurs)) found) in
        o19NonProviderObserved keyEq wanted old (providerCandidate @{keyEq} wanted old) Refl excluded)

||| Lift one primitive provider observation through resolveView's Maybe case.
export
0 o19ResolveHeadObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) -> (rest : List key) ->
  (left, right : Registry name key value world error) -> (observed : Maybe name) ->
  (providerOf {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted left = observed) ->
  (providerOf {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted right = observed) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} rest left =
   resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} rest right) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (wanted :: rest) left =
   resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (wanted :: rest) right)
o19ResolveHeadObserved nameEq keyEq wanted rest left right Nothing leftProvider rightProvider tailSame =
  rewrite leftProvider in rewrite rightProvider in Refl
o19ResolveHeadObserved nameEq keyEq wanted rest left right (Just provider) leftProvider rightProvider tailSame =
  rewrite leftProvider in rewrite rightProvider in cong (map (ProviderView provider)) tailSame

||| Backwards AND forwards resolver equality for precisely the dependencies
||| that exclude the changing component's provision. Unrelated targets need
||| not agree. The actual ordered provider observations are derived internally.
export
0 o19ResolveReplaceNonDependency :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (deps : List key) -> (actor : name) ->
  (source : Registry name key value world error) -> (old, next : Fiber name key value world error) ->
  (lookupFiber @{nameEq} actor source = Just old) -> (fiberComponent next = fiberComponent old) ->
  ((wanted : key) -> Elem wanted deps -> Not (Elem wanted (dependencies (componentProvisions (fiberComponent old))))) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps (replaceBinding @{nameEq} actor next source) =
   resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps source)
o19ResolveReplaceNonDependency nameEq keyEq [] actor source old next found static excluded = Refl
o19ResolveReplaceNonDependency nameEq keyEq (wanted :: rest) actor source old next found static excluded =
  o19ResolveHeadObserved nameEq keyEq wanted rest (replaceBinding @{nameEq} actor next source) source
    (providerOf {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted source)
    (o19ProviderReplaceNonDependency nameEq keyEq wanted actor source old next found static (excluded wanted Here)) Refl
    (o19ResolveReplaceNonDependency nameEq keyEq rest actor source old next found static (\key, present => excluded key (There present)))

||| A located owner surviving a local update forces its replacement case.
||| Insert/delete are refuted from actual lookup observations. Static component
||| metadata supplied by the update carries declaration exclusion automatically.
export
0 o19ResolvePresentLocalUpdate :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (deps : List key) -> (actor : name) ->
  (source, target : Registry name key value world error) -> (old : Fiber name key value world error) ->
  (lookupFiber @{nameEq} actor source = Just old) ->
  (isJust (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor target) = True) ->
  RegistryLocalUpdate name key world error value nameEq actor source target ->
  ((wanted : key) -> Elem wanted deps -> Not (Elem wanted (dependencies (componentProvisions (fiberComponent old))))) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps target =
   resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps source)
o19ResolvePresentLocalUpdate nameEq keyEq deps actor source _ old found survives (LocalInsert next absent) excluded =
  void (nothingIsNotJust (trans (sym absent) found))
o19ResolvePresentLocalUpdate nameEq keyEq deps actor source _ old found survives
  (LocalReplace next {oldFiber} {oldFound} {staticComponent}) excluded =
    o19ResolveReplaceNonDependency nameEq keyEq deps actor source old next found
      (trans staticComponent (cong fiberComponent (justInjective (trans (sym oldFound) found)))) excluded
o19ResolvePresentLocalUpdate nameEq keyEq deps actor source _ old found survives LocalDelete excluded =
  case trans (sym (cong isJust (DGamma.CP4DeletionSelectedOwn.lookupDeleteSelf @{nameEq} actor source))) survives of Refl impossible
