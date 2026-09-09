module DGamma.L2R15NativeControlShapes

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.L2R14ActionShapes
import DGamma.L2R15OperationSnapshots
import Data.List
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Native retirement shape from its actual operation view. The view's
||| installed fiber is identified by lookup determinism, not a raw state
||| equality. No extra freshness or source-validity premise is needed.
export
0 nativeRetireShapeFromView : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (fiber : Fiber name key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (target : SystemState name key value world error) -> (tag : RuleTag) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor source = Just fiber) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (ORetire actor)
    (MkSystemState ambient source) = Just (tag, target)) ->
  RetireSuccessView name key world error value nameEq actor ambient source tag target ->
  NativeActionShape name key world error value nameEq keyEq (ORetire actor) (MkSystemState ambient source) tag
    (MkRuntimeSnapshot ambient (replaceEntries @{nameEq} actor (retireFiber fiber) (bindings source)))
nativeRetireShapeFromView nameEq keyEq actor fiber ambient source _ _ found checked
  (MkRetireSuccessView observed nativeFound) =
  MkNativeActionShape (MkSystemState ambient (replaceBinding @{nameEq} actor (retireFiber observed) source)) checked
    (trans (nativeReplaceSnapshot nameEq actor (retireFiber observed) ambient source)
      (cong (\owner => MkRuntimeSnapshot ambient (replaceEntries @{nameEq} actor (retireFiber owner) (bindings source)))
        (injective (trans (sym nativeFound) found))))

||| GENERAL retirement-shape producer at arbitrary state/payload, from the
||| actual native edge and its installed-fiber lookup. The abstract packet
||| already supplies that lookup for both old/new fresh-child retirements.
export
0 nativeRetireShape : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (fiber : Fiber name key value world error) ->
  (source, target : SystemState name key value world error) -> (tag : RuleTag) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry source) = Just fiber) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (ORetire actor) source = Just (tag, target)) ->
  NativeActionShape name key world error value nameEq keyEq (ORetire actor) source tag
    (MkRuntimeSnapshot (worldState source) (replaceEntries @{nameEq} actor (retireFiber fiber) (bindings (registry source))))
nativeRetireShape nameEq keyEq actor fiber (MkSystemState ambient source) target tag found checked =
  nativeRetireShapeFromView nameEq keyEq actor fiber ambient source target tag found checked
    (retireSuccessView nameEq keyEq actor ambient source tag target
      (checkedActionProjects nameEq keyEq (ORetire actor) (MkSystemState ambient source) target tag checked))

||| Native removal shape from its authentic operation view. The guards and
||| source fiber certify the actual edge, but the raw target is simply the
||| registry deletion. Never evaluates the forbidden intermediate Remove.
export
0 nativeRemoveShapeFromView : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (target : SystemState name key value world error) -> (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (ORemove actor)
    (MkSystemState ambient source) = Just (tag, target)) ->
  RemoveSuccessView name key world error value nameEq actor ambient source tag target ->
  NativeActionShape name key world error value nameEq keyEq (ORemove actor) (MkSystemState ambient source) tag
    (MkRuntimeSnapshot ambient (deleteEntries @{nameEq} actor (bindings source)))
nativeRemoveShapeFromView nameEq keyEq actor ambient source _ _ checked
  (MkRemoveSuccessView fiber found removable noChild) =
  MkNativeActionShape (MkSystemState ambient (deleteBinding @{nameEq} actor source)) checked
    (nativeDeleteSnapshot nameEq actor ambient source)

||| GENERAL removal-shape producer from ONE original native edge, for any
||| registry and actor. Covers both old/new packet removals without requiring
||| an alternate Remove, a chosen target shape, or additional freshness.
export
0 nativeRemoveShape : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (source, target : SystemState name key value world error) -> (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (ORemove actor) source = Just (tag, target)) ->
  NativeActionShape name key world error value nameEq keyEq (ORemove actor) source tag
    (MkRuntimeSnapshot (worldState source) (deleteEntries @{nameEq} actor (bindings (registry source))))
nativeRemoveShape nameEq keyEq actor (MkSystemState ambient source) target tag checked =
  nativeRemoveShapeFromView nameEq keyEq actor ambient source target tag checked
    (removeSuccessView nameEq keyEq actor ambient source tag target
      (checkedActionProjects nameEq keyEq (ORemove actor) (MkSystemState ambient source) target tag checked))
