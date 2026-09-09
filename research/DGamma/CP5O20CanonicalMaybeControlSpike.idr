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

||| Exact one-name ORIGINAL->canonical control alternatives at observed
||| MaybeFiber values. Withdrawn means actual canonical Nothing; kept means
||| complete identity-name control (including absent/absent), not presence.
||| Neither alternative equates unsupportedness with withdrawal/vestigiality.
public export
data O20CanonicalControlDisposition :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (selected : name) -> (withdrawn : List name) ->
  (original, canonical : Maybe (Fiber name key value world error)) -> Type where
  CanonicalControlWithdrawn :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {selected : name} -> {withdrawn : List name} ->
    {original, canonical : Maybe (Fiber name key value world error)} ->
    (0 member : Elem selected withdrawn) -> (0 absent : (canonical = Nothing)) ->
    O20CanonicalControlDisposition selected withdrawn original canonical
  CanonicalControlKept :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {selected : name} -> {withdrawn : List name} ->
    {original, canonical : Maybe (Fiber name key value world error)} ->
    (0 outside : Not (Elem selected withdrawn)) ->
    (0 controls : FiberControlMaybeRelated original canonical) ->
    O20CanonicalControlDisposition selected withdrawn original canonical

||| Single-constructor observation of BOTH actual primitive endpoint lookups,
||| retaining runtime MaybeFiber values and erased exact equations/disposition.
||| This concerns one trace's canonical endpoint, not a cross-trace name map.
public export
record O20CanonicalControlObservation
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (originalFinal, canonicalFinal : SystemState name key value world error)
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq originalFinal canonicalFinal)
  (selected : name) where
  constructor MkO20CanonicalControlObservation
  observedOriginalFiber : Maybe (Fiber name key value world error)
  observedCanonicalFiber : Maybe (Fiber name key value world error)
  0 originalFiberObserved :
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry originalFinal) = observedOriginalFiber)
  0 canonicalFiberObserved :
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry canonicalFinal) = observedCanonicalFiber)
  0 canonicalControlDisposition : O20CanonicalControlDisposition selected
    (endpointWithdrawnNames endpoint) observedOriginalFiber observedCanonicalFiber

||| Executable single-constructor producer at the observed LIBRARY membership
||| decision and both observed primitive lookups. Eliminate Dec BEFORE building
||| the packet. The endpoint's own fields produce withdrawal or full controls;
||| no control relation, canonical absence or successor packet is assumed.
export
o20CanonicalControlsAtDecision :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (originalFinal, canonicalFinal : SystemState name key value world error) ->
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq originalFinal canonicalFinal) ->
  (selected : name) ->
  (original, canonical : Maybe (Fiber name key value world error)) ->
  (0 originalExact : (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry originalFinal) = original)) ->
  (0 canonicalExact : (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry canonicalFinal) = canonical)) ->
  (decision : Dec (Elem selected (endpointWithdrawnNames endpoint))) ->
  (0 decisionExact : (isElem @{nameEq} selected (endpointWithdrawnNames endpoint) = decision)) ->
  O20CanonicalControlObservation name key world error value nameEq keyEq originalFinal canonicalFinal endpoint selected
o20CanonicalControlsAtDecision nameEq keyEq originalFinal canonicalFinal endpoint selected
  original canonical originalExact canonicalExact (Yes member) decisionExact =
    MkO20CanonicalControlObservation original canonical originalExact canonicalExact
      (CanonicalControlWithdrawn member
        (trans (sym canonicalExact) (o20WithdrawnNameActuallyAbsent (endpointNamesWithdrawn endpoint selected member))))
o20CanonicalControlsAtDecision {name} {key} {world} {error} {value}
  nameEq keyEq originalFinal canonicalFinal endpoint selected
  original canonical originalExact canonicalExact (No outside) decisionExact =
    MkO20CanonicalControlObservation original canonical originalExact canonicalExact
      (CanonicalControlKept outside
        (replace {p = \left => FiberControlMaybeRelated left canonical} originalExact
          (replace {p = \right => FiberControlMaybeRelated
            (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry originalFinal)) right}
            canonicalExact (endpointControlsOutside endpoint selected outside))))

||| Observe BOTH actual primitive MaybeFiber lookups and the library isElem
||| decision with their own equations. Produces the control disposition for
||| ANY name, including present unsupported and already-removed names. It
||| does not decide which original vestigial names MUST be withdrawn.
export
o20ObserveCanonicalControls :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (originalFinal, canonicalFinal : SystemState name key value world error) ->
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq originalFinal canonicalFinal) ->
  (selected : name) ->
  O20CanonicalControlObservation name key world error value nameEq keyEq originalFinal canonicalFinal endpoint selected
o20ObserveCanonicalControls {name} {key} {world} {error} {value}
  nameEq keyEq originalFinal canonicalFinal endpoint selected =
    o20CanonicalControlsAtDecision nameEq keyEq originalFinal canonicalFinal endpoint selected
      (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry originalFinal))
      (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry canonicalFinal))
      Refl Refl (isElem @{nameEq} selected (endpointWithdrawnNames endpoint)) Refl

||| Both exact observed control alternatives preserve an original Nothing.
||| No choice of withdrawal membership or present-vestigial evidence enters.
export
0 o20DispositionPreservesAbsence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {selected : name} -> {withdrawn : List name} ->
  {original, canonical : Maybe (Fiber name key value world error)} ->
  O20CanonicalControlDisposition selected withdrawn original canonical ->
  (original = Nothing) -> (canonical = Nothing)
o20DispositionPreservesAbsence (CanonicalControlWithdrawn member absent) originalAbsent = absent
o20DispositionPreservesAbsence {canonical} (CanonicalControlKept outside controls) originalAbsent =
  o20AbsentControlTarget
    (replace {p = \observed => FiberControlMaybeRelated observed canonical} originalAbsent controls)

||| Consume ONE observation packet to turn actual original lookup absence
||| into actual canonical lookup absence. Equations refer to that same packet;
||| no projected guard or equality of separately reconstructed observations.
export
0 o20CanonicalObservationAbsent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {originalFinal, canonicalFinal : SystemState name key value world error} ->
  {endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq originalFinal canonicalFinal} ->
  {selected : name} ->
  (observation : O20CanonicalControlObservation name key world error value nameEq keyEq originalFinal canonicalFinal endpoint selected) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry originalFinal) = Nothing) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry canonicalFinal) = Nothing)
o20CanonicalObservationAbsent observation originalAbsent =
  trans (canonicalFiberObserved observation)
    (o20DispositionPreservesAbsence (canonicalControlDisposition observation)
      (trans (sym (originalFiberObserved observation)) originalAbsent))
