module DGamma.L2R11CorePackets

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.Num
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.L2R2SmallStates
import DGamma.L2R8ContiguityStates
import DGamma.L2R9ContiguityPackets
import DGamma.L2R9RestoredPackets
import DGamma.L2R10OrdinalData
import DGamma.L2R11OpaqueCore
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core

%default total
%unbound_implicits off

||| Original native B packet instantiated without re-normalizing ANY edge.
||| Only two small explicit source lookups are reduced. This is not split8->9.
public export
originalCorePacket : CoreNativePacket contiguityState
originalCorePacket = MkCoreNativePacket
  (fst contiguityOriginalFirst)
  (fst (snd contiguityOriginalFirst))
  (fst (snd (snd contiguityOriginalFirst)))
  (fst (snd (snd (snd contiguityOriginalFirst))))
  (snd (snd (snd (snd contiguityOriginalFirst)))) Refl Refl
