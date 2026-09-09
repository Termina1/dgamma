module DGamma.L2R4NoStraddling

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.L2R3Attached
import DGamma.L2R3AttachedGap
import DGamma.L2R3FixtureCoverage
import DGamma.L2R4Localization
import DGamma.L2R4OrdinalObservation
import Data.Nat
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| ANY observed Begin cut excludes EVERY authenticated bundle straddling it.
||| Localization constructs a native root occurrence at the same cut; its
||| observed OInsert action contradicts LBegin. No catalog endpoint assumption.
export
0 beginCutNoStraddling :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, finalState : SystemState name key value world error} ->
  {global : Transitions first finalState} ->
  (cut : Nat) -> (actor : name) ->
  (0 observed : nativeActionAt global cut = Just (LBegin actor)) ->
  NoBundleStraddlesCut nameEq keyEq global cut
beginCutNoStraddling {global} cut actor observed action ordinal member lower upper =
  case justInjective (trans (sym observed)
    (replace {p = \n => nativeActionAt global n = Just
        (OInsert (insertedRoot (attachedInteriorRoot member cut lower upper)) Root
          (insertedComponent (attachedInteriorRoot member cut lower upper)))}
      (rootOrdinal (attachedInteriorRoot member cut lower upper))
      (occurrenceObserved (rootOccurrence (attachedInteriorRoot member cut lower upper))))) of
    Refl impossible
