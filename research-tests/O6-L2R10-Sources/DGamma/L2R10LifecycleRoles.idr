module DGamma.L2R10LifecycleRoles

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2CheckedSnapshot
import DGamma.L2R5RetirementFrame
import DGamma.L2R9ResolverRetirement
import DGamma.L2R9LifecycleRoles
import DGamma.L2R10BeginAdapter
import DGamma.L2R10AdvanceReplay
import Prelude.Types
import Prelude.Interfaces
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Exact retained three-role CONTRACT now produced. All operational inputs
||| are the original checked edge, actual frame, and admissible current cut.
||| This is not the universally quantified all-action ForeignReplay callback.
export
0 replayRetirementLifecycle :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, actor : name) ->
  (childFiber, actorFiber : Fiber name key value world error) ->
  (before : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  NativeLifecycleRetirementRole nameEq keyEq child parent actor childFiber actorFiber before action tag
replayRetirementLifecycle nameEq keyEq child parent actor childFiber actorFiber before _ _
  Here frame distinct valid afterState original =
  replayRetirementBegin nameEq keyEq child parent actor childFiber actorFiber before afterState frame distinct valid original
replayRetirementLifecycle nameEq keyEq child parent actor childFiber actorFiber before _ _
  (There Here) frame distinct valid afterState original =
  replayRetirementAdvance nameEq keyEq child parent actor childFiber actorFiber before afterState LIterTag frame distinct valid original
replayRetirementLifecycle nameEq keyEq child parent actor childFiber actorFiber before _ _
  (There (There Here)) frame distinct valid afterState original =
  replayRetirementAdvance nameEq keyEq child parent actor childFiber actorFiber before afterState LFinishTag frame distinct valid original
replayRetirementLifecycle nameEq keyEq child parent actor childFiber actorFiber before action tag
  (There (There (There impossibleRole))) frame distinct valid afterState original = absurd impossibleRole
