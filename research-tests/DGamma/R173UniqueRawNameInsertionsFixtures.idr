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
