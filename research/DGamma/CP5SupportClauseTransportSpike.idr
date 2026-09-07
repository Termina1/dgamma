module DGamma.CP5SupportClauseTransportSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4SupportSolution
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5AllSupportedMetadataSpike
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

public export
supportClauseParent : (name : Type) -> (name -> Bool) -> Parent name -> Bool
supportClauseParent name predicate Root = True
supportClauseParent name predicate (ChildOf parent) = predicate parent

0 clauseAndTrue : (left, right : Bool) -> (left = True) -> (right = True) -> (left && right = True)
clauseAndTrue True True Refl Refl = Refl

0 clauseAndParts : (left, right : Bool) -> (left && right = True) -> (left = True, right = True)
clauseAndParts False right exact = case exact of Refl impossible
clauseAndParts True right exact = (Refl, exact)

0 clauseOrCases : (left, right : Bool) -> (left || right = True) -> Either (left = True) (right = True)
clauseOrCases False right exact = Right exact
clauseOrCases True right exact = Left Refl

0 clauseOrFromEither : (left, right : Bool) -> Either (left = True) (right = True) -> (left || right = True)
clauseOrFromEither left right (Left exact) = rewrite exact in Refl
clauseOrFromEither False right (Right exact) = exact
clauseOrFromEither True right (Right exact) = Refl

0 clauseAllListAt : (element : Type) -> (predicate : element -> Bool) -> (items : List element) ->
  (selected : element) -> Elem selected items -> (allList predicate items = True) -> (predicate selected = True)
clauseAllListAt element predicate (_ :: rest) selected Here exact = fst (clauseAndParts (predicate selected) (allList predicate rest) exact)
clauseAllListAt element predicate (head :: rest) selected (There later) exact =
  clauseAllListAt element predicate rest selected later (snd (clauseAndParts (predicate head) (allList predicate rest) exact))
