module DGamma.L2R13SquareSuccessor

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.L2R11ClassifierSquare
import DGamma.L2R13InsertExtensional
import DGamma.L2R2CheckedSnapshot
import DGamma.L2R4InsertReplay
import DGamma.L2R5Extensional
import DGamma.L2R5ExtensionalRetire
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| FROM a classifier square, apply the actual following root edge at the
||| new square endpoint. The native successor, same tag and RegistryExtensional
||| equation are PRODUCED. Only scalar declaration-scan framing stays explicit;
||| it is not implied here by RegistryExtensional or square existence alone.
export
0 squareFollowingRoot : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (root, following : name) ->
  (component, followingComponent : Component key value world error) ->
  (source, oldFinal, oldSuccessor : SystemState name key value world error) ->
  (action : Action name key value world error) -> (crossTag, followingTag : RuleTag) ->
  (square : ClassifierSquare name key world error value nameEq keyEq root component source action crossTag oldFinal) ->
  (0 next : checkedApplyAction @{nameEq} @{keyEq} (OInsert following Root followingComponent) oldFinal =
    Just (followingTag, oldSuccessor)) ->
  (0 frame : provisionsDisjointFrom {name} {key} {world} {error} {value} @{keyEq}
    (componentProvisions followingComponent) (bindings (registry (squareFinal square))) =
    provisionsDisjointFrom {name} {key} {world} {error} {value} @{keyEq}
      (componentProvisions followingComponent) (bindings (registry oldFinal))) ->
  CheckedExtensionalStep name key world error value nameEq keyEq (OInsert following Root followingComponent)
    (squareFinal square) followingTag oldSuccessor
squareFollowingRoot {name} {key} {world} {error} {value}
  nameEq keyEq root following component followingComponent source oldFinal oldSuccessor action crossTag followingTag square next frame =
  checkedRootAcrossExtensional nameEq keyEq following followingComponent oldFinal oldSuccessor (squareFinal square)
    followingTag next (squareEndpoint square)
    (checkedActionTargetValid nameEq keyEq action (squareMiddle square) (squareFinal square) crossTag (laterChecked square))
    (provisionsDisjointFrom {name} {key} {world} {error} {value} @{keyEq}
      (componentProvisions followingComponent) (bindings (registry oldFinal))) Refl frame
