module DGamma.CP5O19WholeBlockSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19CartesianColumnsSpike
import DGamma.CP5O19CartesianNumericSpike
import DGamma.CP5O19OrdinalPlanSpike
import DGamma.CP5O19ActualCartesianSpike
import DGamma.CP5O19GridCertificationSpike
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Observe a nonempty view of an EXISTING finite chain. The forgetful
||| equation preserves its actual nodes, not just length or action labels.
public export
record O19NonEmptyChain
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, sourceFinal, targetFinal : SystemState name key value world error}
  {source : Transitions initial sourceFinal} {target : Transitions initial targetFinal}
  (derivation : FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq source target) where
  constructor MkO19NonEmptyChain
  observedNonEmptyChain : NonEmptyFiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq source target
  0 observedChainExact : (nonEmptyToFiniteAdjacentSwapDerivation observedNonEmptyChain = derivation)
  0 observedChainCount : (nonEmptyAdjacentSwapNodeCount observedNonEmptyChain = finiteAdjacentSwapNodeCount derivation)
