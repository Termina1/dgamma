module DGamma.R176BareCapitalFreshnessNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5UniqueRawNameCanonicalCapital
import Decidable.Equality

%default total
%unbound_implicits off

||| A bare capital's real independence projection is NOT original freshness.
||| This tests the missing hypothesis boundary, not logical non-derivability.
0 bareCapitalCannotSupplyFreshness :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  (UniqueRawNameInsertions name key world error value nameEq keyEq
    (canonicalTrace (canonicalSchedule capital)))
bareCapitalCannotSupplyFreshness name key world error value protocol nameEq keyEq capital =
  capitalCanonicalUniqueInsertions name key world error value protocol nameEq keyEq capital
    (originalTraceIndependent capital)
