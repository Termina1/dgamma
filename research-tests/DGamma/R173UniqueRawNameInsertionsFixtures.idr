module DGamma.R173UniqueRawNameInsertionsFixtures

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R172O17OpenParentRootReuseCandidate

%default total
%unbound_implicits off

||| The designated eight-step trace inserts raw name 1 at ordinals 2 and 5.
||| This is a proved negation of the new premise, not a sorting negation.
public export
0 r173ReuseRejectsUniqueInsertions :
  (Not (UniqueRawNameInsertions Nat R45Key Unit String R45Value
    r45NameEq r45KeyEq r172ReuseTrace))
r173ReuseRejectsUniqueInsertions unique =
  case uniqueInsertionPosition unique 1 (ChildOf 0) Root r45Child r45Child
    (generatedRegistrationActionOccurrence r172ReuseOriginalChildBirth)
    (MkLocatedActionOccurrence r45AfterBegin r172ReuseAfterRoot
      (appendTransitions r45SourceTrace (MoreTransitions r172ReuseRemove NoTransitions))
      r172ReuseRoot (MoreTransitions r172ReuseRetire (MoreTransitions r172ReuseFinish NoTransitions))
      Refl Refl) of Refl impossible

||| The four-step source has births (0,0) and (2,1), and no other birth.
0 r173DistinctBirthPosition :
  (selected, ordinal : Nat) ->
  (rawInsertionNameAt Nat R45Key Unit String R45Value ordinal r45SourceTrace = Just selected) ->
  (ordinal = selected + selected)
r173DistinctBirthPosition selected Z observed = case observed of Refl => Refl
r173DistinctBirthPosition selected (S Z) observed = case observed of Refl impossible
r173DistinctBirthPosition selected (S (S Z)) observed = case observed of Refl => Refl
r173DistinctBirthPosition selected (S (S (S Z))) observed = case observed of Refl impossible
r173DistinctBirthPosition selected (S (S (S (S later)))) observed = case observed of Refl impossible
