module DGamma.R6ScannerThirdOrdering

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Decidable.Equality

%default total

ThirdValue : Unit -> Type
ThirdValue _ = Unit

thirdSpec : CoeffectSpec Unit
thirdSpec = MkCoeffectSpec [] UniqueNil

thirdComponent : Component Unit ThirdValue Unit String
thirdComponent = MkComponent thirdSpec thirdSpec []

record ThirdIndexes where
  constructor MkThirdIndexes
  thirdLeft : RegistrationIndexState Nat
  thirdRight : RegistrationIndexState Nat

applyThird : ScannerEvent Nat -> ThirdIndexes -> ThirdIndexes
applyThird (ScannerLeftDiscard (MkRegistrationGeneration child ordinal))
  (MkThirdIndexes left right) =
    MkThirdIndexes
      (advanceDeletedRegistrationIndex ordinal child 0 thirdComponent left) right
applyThird (ScannerRightDiscard (MkRegistrationGeneration child ordinal))
  (MkThirdIndexes left right) =
    MkThirdIndexes left
      (advanceDeletedRegistrationIndex ordinal child 0 thirdComponent right)
applyThird _ indexes = indexes

runThird : List (ScannerEvent Nat) -> ThirdIndexes -> ThirdIndexes
runThird [] indexes = indexes
runThird (event :: rest) indexes = runThird rest (applyThird event indexes)

||| Unreviewed third cross-side ordering: L6,R9,R14,L18.  Per-side ordinal
||| chronology is preserved although the cross-side alternation differs.
thirdOrder : List (ScannerEvent Nat)
thirdOrder =
  [ ScannerLeftDiscard DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth6
  , ScannerRightDiscard DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth9
  , ScannerRightDiscard DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth14
  , ScannerLeftDiscard DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18
  ]

public export
thirdFinal : ThirdIndexes
thirdFinal = runThird thirdOrder
  (MkThirdIndexes DGamma.CP3.emptyRegistrationIndex
    DGamma.CP3.emptyRegistrationIndex)

public export
0 thirdFullIndexExact :
  DGamma.R6ScannerThirdOrdering.thirdFinal =
    MkThirdIndexes
      (MkRegistrationIndexState
        [(1, DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18)] [] []
        [ DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18
        , DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth6 ])
      (MkRegistrationIndexState
        [(1, DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth14)] [] []
        [ DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth14
        , DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth9 ])
thirdFullIndexExact = Refl

public export
0 thirdDeletedListsExact :
  ( indexedDeletedGenerations
      (thirdLeft DGamma.R6ScannerThirdOrdering.thirdFinal) =
      [ DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18
      , DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth6 ]
  , indexedDeletedGenerations
      (thirdRight DGamma.R6ScannerThirdOrdering.thirdFinal) =
      [ DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth14
      , DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth9 ]
  )
thirdDeletedListsExact = (Refl, Refl)
