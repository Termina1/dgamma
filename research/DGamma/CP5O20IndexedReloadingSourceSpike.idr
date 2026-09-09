module DGamma.CP5O20IndexedReloadingSourceSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20AllNameSynchronizationSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| Actual right source indexed by the ALREADY chosen component/program.
||| Unlike an unindexed shared-source existential, this type cannot forget
||| which left program the successor must execute. Only lookup proof is erased.
public export
record O20MatchingReloadingSource
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (actor : name)
  (state : SystemState name key value world error)
  (component : Component key value world error)
  (remaining : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) where
  constructor MkO20MatchingReloadingSource
  matchingParent : Parent name
  matchingRetired : Bool
  matchingTable : OwnedTable key value (componentProvisions component)
  matchingOlder : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)
  matchingView : View name (dependencies (componentDependencies component))
  0 matchingFound :
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry state) =
      Just (MkFiber component matchingParent matchingRetired matchingTable (Reloading remaining matchingOlder matchingView)))
