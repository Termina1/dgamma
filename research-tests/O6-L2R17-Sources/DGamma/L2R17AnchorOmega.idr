module DGamma.L2R17AnchorOmega

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.EqOrd
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5UniqueRawNameInsertions
import DGamma.L2R2SmallStates
import DGamma.L2R3ForcedClosure
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R10OrdinalData
import DGamma.L2R16AnchorStates
import DGamma.L2R16AnchorNative
import DGamma.L2R16AnchorTrace
import DGamma.L2R16AnchorTrail
import DGamma.L2R16ProductionBridge
import Data.Bool
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core
import Decidable.Decidable

%default total
%unbound_implicits off

||| Executable inverse-position uniqueness check on the authentic original
||| different-anchor word. None is vacuous; every actual insertion must
||| satisfy ordinal = rawName + 3. No conditional on the selected name.
public export
ω : Nat -> Bool
ω position =
  case rawInsertionNameAt Nat Bool Unit String (\key => Unit) position (anchorTrace False) of
    Nothing => True
    Just selected => isYes (decEq @{fst fixtureDictionaries} position (selected + 3))

||| Complete-domain native computation, including every beyond-end ordinal.
public export
0 omegaDataAgreement : (position : Nat) -> ω position = True
omegaDataAgreement 0 = Refl
omegaDataAgreement 1 = Refl
omegaDataAgreement 2 = Refl
omegaDataAgreement 3 = Refl
omegaDataAgreement 4 = Refl
omegaDataAgreement 5 = Refl
omegaDataAgreement 6 = Refl
omegaDataAgreement 7 = Refl
omegaDataAgreement 8 = Refl
omegaDataAgreement (S (S (S (S (S (S (S (S (S later))))))))) = Refl
