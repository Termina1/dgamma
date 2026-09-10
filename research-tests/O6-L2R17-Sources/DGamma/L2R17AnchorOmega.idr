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
  maybe True (\selected => isYes (decEq @{fst fixtureDictionaries} position (selected + 3)))
    (rawInsertionNameAt Nat Bool Unit String (\key => Unit) position (anchorTrace False))

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

||| Erased decoder observes the library decider at its own call site.
||| The Bool evidence is consumed, not an unused premise on a fresh oracle.
public export
0 omegaSound : (position, selected : Nat) ->
  (0 checked : ω position = True) ->
  (0 observed : rawInsertionNameAt Nat Bool Unit String (\key => Unit)
    position (anchorTrace False) = Just selected) ->
  position = selected + 3
omegaSound position selected checked observed =
  case the (answer : Dec (position = selected + 3) **
    decEq @{fst fixtureDictionaries} position (selected + 3) = answer)
    (decEq @{fst fixtureDictionaries} position (selected + 3) ** Refl) of
      (Yes same ** decision) => same
      (No different ** decision) =>
        absurd (replace {p = \answer => isYes answer = True} decision
          (replace {p = \raw => maybe True
            (\found => isYes (decEq @{fst fixtureDictionaries} position (found + 3))) raw = True}
            observed checked))

||| Actual inhabitant of the full quantified insertion contract, consuming
||| computed True for both arbitrary occurrences. Counts, not dependent
||| states or token equality, meet at the same arithmetic inverse.
public export
0 anchorUniqueFromOmega :
  UniqueRawNameInsertions Nat Bool Unit String (\key => Unit)
    (fst fixtureDictionaries) (snd fixtureDictionaries) (anchorTrace False)
anchorUniqueFromOmega = MkUniqueRawNameInsertions
  (\selected, leftParent, rightParent, leftComponent, rightComponent, left, right =>
    trans (omegaSound (locatedActionOrdinal left) selected
      (omegaDataAgreement (locatedActionOrdinal left))
      (rawInsertionNameAtLocated Nat Bool Unit String (\key => Unit)
        (anchorTrace False) selected leftParent leftComponent left))
      (sym (omegaSound (locatedActionOrdinal right) selected
        (omegaDataAgreement (locatedActionOrdinal right))
        (rawInsertionNameAtLocated Nat Bool Unit String (\key => Unit)
          (anchorTrace False) selected rightParent rightComponent right))))
