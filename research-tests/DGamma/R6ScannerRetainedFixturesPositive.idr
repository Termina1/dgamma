module DGamma.R6ScannerRetainedFixturesPositive

import DGamma.CP3
import DGamma.CP5ConfluenceRenamingCompositionSpike

%default total

public export
0 consumeBothFullIndexes :
  ( DGamma.CP5ConfluenceRenamingCompositionSpike.concreteTargetFinalIndexes =
      MkConcreteScannerIndexes
        (MkRegistrationIndexState
          [(1, DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18)] [] []
          [ DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18
          , DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth6 ])
        (MkRegistrationIndexState
          [(1, DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth14)] [] []
          [ DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth14
          , DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth9 ])
  , DGamma.CP5ConfluenceRenamingCompositionSpike.concreteReorderedFinalIndexes =
      MkConcreteScannerIndexes
        (MkRegistrationIndexState
          [(1, DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18)] [] []
          [ DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18
          , DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth6 ])
        (MkRegistrationIndexState
          [(1, DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth14)] [] []
          [ DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth14
          , DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth9 ])
  )
consumeBothFullIndexes =
  ( DGamma.CP5ConfluenceRenamingCompositionSpike.concreteTargetIndexesExact
  , DGamma.CP5ConfluenceRenamingCompositionSpike.concreteReorderedIndexesExact )

public export
0 consumeBothExactDeletedLists :
  ( (indexedDeletedGenerations (concreteLeftIndex
        DGamma.CP5ConfluenceRenamingCompositionSpike.concreteTargetFinalIndexes) =
        [ DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18
        , DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth6 ],
     indexedDeletedGenerations (concreteRightIndex
        DGamma.CP5ConfluenceRenamingCompositionSpike.concreteTargetFinalIndexes) =
        [ DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth14
        , DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth9 ])
  , (indexedDeletedGenerations (concreteLeftIndex
        DGamma.CP5ConfluenceRenamingCompositionSpike.concreteReorderedFinalIndexes) =
        [ DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18
        , DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth6 ],
     indexedDeletedGenerations (concreteRightIndex
        DGamma.CP5ConfluenceRenamingCompositionSpike.concreteReorderedFinalIndexes) =
        [ DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth14
        , DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth9 ])
  )
consumeBothExactDeletedLists =
  ( DGamma.CP5ConfluenceRenamingCompositionSpike.concreteTargetDeletedListsExact
  , DGamma.CP5ConfluenceRenamingCompositionSpike.concreteReorderedDeletedListsExact )
