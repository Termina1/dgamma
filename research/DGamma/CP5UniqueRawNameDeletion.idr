module DGamma.CP5UniqueRawNameDeletion

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5UniqueRawNameInsertions
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

0 uniqueMapSuccessorNotZero : (observed : Maybe Nat) -> (map S observed = Just Z) -> Void
uniqueMapSuccessorNotZero Nothing same = case same of Refl impossible
uniqueMapSuccessorNotZero (Just earlier) same = case same of Refl impossible
