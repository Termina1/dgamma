module DGamma.R195RootOrdinalBoundaryPositive

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O20RootOrdinalBoundarySpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive

%default total
%unbound_implicits off

||| The actual checked singleton root insertion contains no generated child
||| occurrence. Only the existing checked edge is used; no canonical capital
||| or assumption about root replay is part of this fixture.
export
0 r195RootOnlyNoChildBirth :
  {child, parent : Nat} ->
  {component : Component R45Key R45Value Unit String} ->
  LocatedGeneratedRegistration child parent component
    (MoreTransitions r45ParentInsert NoTransitions) -> Void
r195RootOnlyNoChildBirth
  (MkLocatedGeneratedRegistration _ _ NoTransitions _ NoTransitions action Refl) =
    case action of Refl impossible
r195RootOnlyNoChildBirth
  (MkLocatedGeneratedRegistration _ _ NoTransitions step (MoreTransitions head tail) action decomposition) =
    case cong transitionCount decomposition of Refl impossible
r195RootOnlyNoChildBirth
  (MkLocatedGeneratedRegistration _ _ (MoreTransitions head NoTransitions) step tail action decomposition) =
    case cong transitionCount decomposition of Refl impossible
r195RootOnlyNoChildBirth
  (MkLocatedGeneratedRegistration _ _ (MoreTransitions head (MoreTransitions next rest)) step tail action decomposition) =
    case cong transitionCount decomposition of Refl impossible

||| A total executable swap of ordinals zero and one, preserving every raw
||| name. It deliberately moves the fixture's root stamp (0,0).
public export
r195SwapRootOrdinals : RegistrationGeneration Nat -> RegistrationGeneration Nat
r195SwapRootOrdinals (MkRegistrationGeneration selected Z) = MkRegistrationGeneration selected 1
r195SwapRootOrdinals (MkRegistrationGeneration selected (S Z)) = MkRegistrationGeneration selected 0
r195SwapRootOrdinals (MkRegistrationGeneration selected (S (S later))) = MkRegistrationGeneration selected (S (S later))

||| The root-ordinal swap is an involution on ALL generation stamps.
export
0 r195SwapRootOrdinalsInvolutive :
  (stamp : RegistrationGeneration Nat) ->
  (r195SwapRootOrdinals (r195SwapRootOrdinals stamp) = stamp)
r195SwapRootOrdinalsInvolutive (MkRegistrationGeneration selected Z) = Refl
r195SwapRootOrdinalsInvolutive (MkRegistrationGeneration selected (S Z)) = Refl
r195SwapRootOrdinalsInvolutive (MkRegistrationGeneration selected (S (S later))) = Refl

||| Full original ActionRegistrationReplayCorrespondence for a checked root
||| singleton replayed literally to itself. Every action/tag/coherence field
||| is satisfied, and its generated-only ordinal law is genuinely vacuous.
||| Its generation map nevertheless moves the existing root's ordinal.
public export
0 r195RootLawFreeCorrespondence :
  ActionRegistrationReplayCorrespondence Nat R45Key Unit String R45Value
    (MoreTransitions r45ParentInsert NoTransitions)
    (MoreTransitions r45ParentInsert NoTransitions)
r195RootLawFreeCorrespondence = MkActionRegistrationReplayCorrespondence
  (MkRegistrationGenerationBijection r195SwapRootOrdinals r195SwapRootOrdinals
    r195SwapRootOrdinalsInvolutive r195SwapRootOrdinalsInvolutive)
  id (\occurrence => Refl) id (\occurrence => Refl)
  (\occurrence => void (r195RootOnlyNoChildBirth occurrence))

||| The precise actual root occurrence in the checked singleton, with its
||| own native source/target states and literal decomposition.
public export
0 r195ActualRootOccurrence :
  LocatedActionOccurrence (OInsert 0 Root r45Parent)
    (MoreTransitions r45ParentInsert NoTransitions)
r195ActualRootOccurrence = MkLocatedActionOccurrence r45Initial r45AfterParent
  NoTransitions r45ParentInsert NoTransitions Refl Refl
