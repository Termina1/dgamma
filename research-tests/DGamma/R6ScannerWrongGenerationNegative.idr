module DGamma.R6ScannerWrongGenerationNegative

import DGamma.CP3
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Data.List.Elem

%default total

||| Same raw name is insufficient: the head proof is for birth 18, not birth 6.
0 conflateSameRawNameBirths :
  Elem DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth6
    [ DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18
    , DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth6 ]
conflateSameRawNameBirths = Here
