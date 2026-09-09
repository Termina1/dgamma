module DGamma.CP5O20CanonicalMaybeControlSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Both genuine withdrawal alternatives own actual survivor lookup absence.
||| This consumes a canonical endpoint field, not the frozen O21 theorem.
export
0 o20WithdrawnNameActuallyAbsent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {selected : name} ->
  {originalFinal, canonicalFinal : SystemState name key value world error} ->
  WithdrawnNameResult nameEq selected originalFinal canonicalFinal ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry canonicalFinal) = Nothing)
o20WithdrawnNameActuallyAbsent (VestigialNameWithdrawn fiber found retiredFlag inactive empty absent) = absent
o20WithdrawnNameActuallyAbsent (NameAlreadyAbsent originalAbsent canonicalAbsent) = canonicalAbsent

||| The primitive control relation preserves observed absence. The equivalent
||| frozen helper is private; this standalone eliminator changes no visibility.
export
0 o20AbsentControlTarget :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {observed : Maybe (Fiber name key value world error)} ->
  FiberControlMaybeRelated (the (Maybe (Fiber name key value world error)) Nothing) observed ->
  (observed = Nothing)
o20AbsentControlTarget NoControlFibers = Refl
