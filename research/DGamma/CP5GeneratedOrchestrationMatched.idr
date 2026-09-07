module DGamma.CP5GeneratedOrchestrationMatched

import DGamma.Calculus
import DGamma.CP3
import Decidable.Equality
import Data.Nat

%default total
%unbound_implicits off

||| False is retirement, True is removal. Births are already covered by the
||| accepted RegistrationTraceCorrespondence, not by this A9 operation code.
public export
generatedOrchestrationAction :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  Bool -> name -> Action name key value world error
generatedOrchestrationAction name key world error value False actor = ORetire actor
generatedOrchestrationAction name key world error value True actor = ORemove actor
