module DGamma.R206ControlRebasePositive

import DGamma.Core
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Section3Example
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20EpisodeSynchronizationSpike
import DGamma.CP5O20AllNameSynchronizationSpike
import DGamma.CP5O20EndpointRebaseBoundarySpike
import DGamma.CP5O20ControlRebaseSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R178GeneratedOrchestrationFixtures
import DGamma.R192RemovedBirthCurrentNameProbe
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| The real six-edge removal endpoint has current root0, while raw names1
||| and2 are absent. The two maps agree ONLY on actual present source entries.
export
0 r206RemovedCurrentAgreement :
  (selected : Nat) -> (fiber : Fiber Nat R45Key R45Value Unit String) ->
  lookupFiber @{r45NameEq} selected (registry r192RemovedBirthFinal) = Just fiber ->
  renameForward (identityNameBijection {name = Nat}) selected =
  renameForward r192AbsentBijection selected
r206RemovedCurrentAgreement Z fiber found = Refl
r206RemovedCurrentAgreement (S later) fiber found = void (nothingIsNotJust found)

||| Actual root0 has no parent reference and its Active view is empty. This
||| supplies the two reference fields separately, not a guessed global map law.
export
0 r206RemovedReferenceAgreements :
  ((selected : Nat) -> (fiber : Fiber Nat R45Key R45Value Unit String) ->
    lookupFiber @{r45NameEq} selected (registry r192RemovedBirthFinal) = Just fiber ->
    (parent : Nat) -> fiberParent fiber = ChildOf parent ->
    renameForward (identityNameBijection {name = Nat}) parent = renameForward r192AbsentBijection parent,
   (selected : Nat) -> (fiber : Fiber Nat R45Key R45Value Unit String) ->
    lookupFiber @{r45NameEq} selected (registry r192RemovedBirthFinal) = Just fiber ->
    (provider : Nat) -> Elem provider (o20LifecycleControlNames (fiberLifecycle fiber)) ->
    renameForward (identityNameBijection {name = Nat}) provider = renameForward r192AbsentBijection provider)
r206RemovedReferenceAgreements =
  ((\selected, fiber, found, parent, reference => case selected of
    Z => case justInjective found of Refl => case reference of Refl impossible
    S later => void (nothingIsNotJust found)),
   (\selected, fiber, found, provider, member => case selected of
    Z => case justInjective found of Refl => absurd member
    S later => void (nothingIsNotJust found)))

||| Positive full ALL-name endpoint cut under the genuinely nonidentity map.
||| The historical child was removed; this is NOT canonical capital or D5.
export
0 r206RemovedAllNameRebase :
  O20AllNameCut Nat R45Key Unit String R45Value r45NameEq r192AbsentBijection
    r192RemovedBirthFinal r192RemovedBirthFinal
r206RemovedAllNameRebase = o20RebaseAllNameCutConditional r45NameEq identityNameBijection r192AbsentBijection
  r192RemovedBirthFinal r192RemovedBirthFinal
  (o20IdentityAllNameCut r45NameEq r192RemovedBirthFinal)
  r206RemovedCurrentAgreement (fst r206RemovedReferenceAgreements) (snd r206RemovedReferenceAgreements)

||| The map really changes raw name1 to2, but the actual absent image is
||| proved by the new inverse/domain transport, not assumed or supplied.
export
0 r206RemovedAbsentTransport :
  (renameForward r192AbsentBijection 1 = 2,
   lookupFiber {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String}
     @{r45NameEq} 1 (registry r192RemovedBirthFinal) = Nothing,
   lookupFiber {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String}
     @{r45NameEq} (renameForward r192AbsentBijection 1) (registry r192RemovedBirthFinal) = Nothing)
r206RemovedAbsentTransport = (Refl, Refl,
  o20RebaseAbsentDomain r45NameEq identityNameBijection r192AbsentBijection
    r192RemovedBirthFinal r192RemovedBirthFinal (o20IdentityAllNameCut r45NameEq r192RemovedBirthFinal)
    r206RemovedCurrentAgreement 1 Refl)

||| Nonempty parent/provider metadata fixture: ChildOf0 and an actual
||| single-provider Active view. This is a control VALUE, not a checked trace.
||| The map still differs at1/2; finite references cannot be replaced by a
||| falsely asserted global equality of the two name functions.
export
0 r206NonemptyReferenceControls :
  (ParentRelatedBy r192AbsentBijection (ChildOf 0) (ChildOf 0),
   LifecycleRelatedBy {name = Nat} {key = ToyKey} {value = ToyValue}
     {world = ToyRuntime} {error = String} {deps = [ServiceA]} {provision = toyEmptySpec}
     r192AbsentBijection (Active id (ProviderView 0 EmptyView)) (Active id (ProviderView 0 EmptyView)))
r206NonemptyReferenceControls =
  (o20RebaseParentReferences identityNameBijection r192AbsentBijection (ChildOf 0) (ChildOf 0)
    (\selected, reference => case reference of Refl => Refl) (ChildrenRelated Refl),
   o20RebaseLifecycleReferences {name = Nat} {key = ToyKey} {value = ToyValue}
     {world = ToyRuntime} {error = String} {deps = [ServiceA]} {provision = toyEmptySpec}
     identityNameBijection r192AbsentBijection (Active id (ProviderView 0 EmptyView)) (Active id (ProviderView 0 EmptyView))
     (\selected, member => case member of
       Here => Refl
       There later => absurd later)
     (o20IdentityLifecycle {error = String} (Active id (ProviderView 0 EmptyView))))

||| Negative-control map: a constructive bijection moves the live root0 to
||| absent name1. Unlike the positive map, present-domain agreement is false.
public export
r206MovedCurrentBijection : NameBijection Nat
r206MovedCurrentBijection = MkNameBijection
  (\selected => case selected of
    Z => 1
    S Z => 0
    S (S later) => S (S later))
  (\selected => case selected of
    Z => 1
    S Z => 0
    S (S later) => S (S later))
  (\selected => case selected of
    Z => Refl
    S Z => Refl
    S (S later) => Refl)
  (\selected => case selected of
    Z => Refl
    S Z => Refl
    S (S later) => Refl)

||| NEGATIVE theorem, also native PASS: dropping present-domain agreement
||| would send the real present root0 to absence, so a full cut is impossible.
export
0 r206RejectsMovedCurrentCut :
  Not (O20AllNameCut Nat R45Key Unit String R45Value r45NameEq r206MovedCurrentBijection
    r192RemovedBirthFinal r192RemovedBirthFinal)
r206RejectsMovedCurrentCut cut =
  o20PresentAbsentImpossible {name = Nat} {key = R45Key} {value = R45Value}
    {world = Unit} {error = String} {renaming = r206MovedCurrentBijection} (allNameControls cut 0)
