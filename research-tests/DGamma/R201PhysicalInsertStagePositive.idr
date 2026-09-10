module DGamma.R201PhysicalInsertStagePositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O20StampedHistoryFoldSpike
import DGamma.CP5O20PhysicalInsertStageSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R191CanonicalChildRetirementGap
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| The actual child Insert in R191's three-block history and the actual
||| child Insert in R193/R195's closing history both run through the NEW native
||| observation producer. No stage constructor, reconstructed target equality,
||| canonical capital or whole-history synchronization is supplied.
export
0 r201NativeChildInsertStages :
  (O20StampedStage Nat R45Key Unit String R45Value r45NameEq r45KeyEq
    identityRegistrationGenerationBijection identityNameBijection 4 4
    [(0, MkRegistrationGeneration 0 0), (1, MkRegistrationGeneration 1 1), (2, MkRegistrationGeneration 2 2)]
    [(0, MkRegistrationGeneration 0 0), (1, MkRegistrationGeneration 1 1), (2, MkRegistrationGeneration 2 2)]
    [(0, MkRegistrationGeneration 0 0), (1, MkRegistrationGeneration 1 1), (2, MkRegistrationGeneration 2 2), (3, MkRegistrationGeneration 3 4)]
    [(0, MkRegistrationGeneration 0 0), (1, MkRegistrationGeneration 1 1), (2, MkRegistrationGeneration 2 2), (3, MkRegistrationGeneration 3 4)]
    (r191ChildGapState 4) (r191ChildGapState 4) (r191ChildGapState 5) (r191ChildGapState 5),
   O20StampedStage Nat R45Key Unit String R45Value r45NameEq r45KeyEq
    identityRegistrationGenerationBijection identityNameBijection 2 2
    [(0, MkRegistrationGeneration 0 0)] [(0, MkRegistrationGeneration 0 0)]
    [(0, MkRegistrationGeneration 0 0), (1, MkRegistrationGeneration 1 2)]
    [(0, MkRegistrationGeneration 0 0), (1, MkRegistrationGeneration 1 2)]
    r45AfterBegin r45AfterBegin r45SourcePairFinal r45SourcePairFinal)
r201NativeChildInsertStages =
  (o20InsertStageAtCheckedStates {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String}
    r45NameEq r45KeyEq identityNameBijection {mapping = identityRegistrationGenerationBijection}
    {leftOrdinal = 4} {rightOrdinal = 4}
    {leftLive = [(0, MkRegistrationGeneration 0 0), (1, MkRegistrationGeneration 1 1), (2, MkRegistrationGeneration 2 2)]}
    {rightLive = [(0, MkRegistrationGeneration 0 0), (1, MkRegistrationGeneration 1 1), (2, MkRegistrationGeneration 2 2)]}
    3 r45Child (ChildOf 0) (ChildOf 0) (ChildrenRelated Refl)
    (r191ChildGapState 4) (r191ChildGapState 4) OInsertTag (r191ChildGapState 5) Refl OInsertTag (r191ChildGapState 5) Refl Refl,
   o20InsertStageAtCheckedStates {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String}
    r45NameEq r45KeyEq identityNameBijection {mapping = identityRegistrationGenerationBijection}
    {leftOrdinal = 2} {rightOrdinal = 2}
    {leftLive = [(0, MkRegistrationGeneration 0 0)]} {rightLive = [(0, MkRegistrationGeneration 0 0)]}
    1 r45Child (ChildOf 0) (ChildOf 0) (ChildrenRelated Refl)
    r45AfterBegin r45AfterBegin OInsertTag r45SourcePairFinal r45ChildInsertChecked
    OInsertTag r45SourcePairFinal r45ChildInsertChecked Refl)
