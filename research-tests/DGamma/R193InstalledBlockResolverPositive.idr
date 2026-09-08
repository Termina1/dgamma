module DGamma.R193InstalledBlockResolverPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.Section3Example
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O20BlockResolverFrameSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Executable setup: install the real two-step ServiceA provider and insert
||| two dependent, provision-empty siblings. Fallback is total only; the
||| subsequent native Begin and live-resolver checks must exclude it.
||| This is a native physical-frame regression, not canonical schedule capital
||| or a tagged-child RegistrationDiscipline/placement fixture.
public export
r193FrameBefore : SystemState Nat ToyKey ToyValue ToyRuntime String
r193FrameBefore = fromMaybe initialSystem (do
  begun <- providerBeginRun
  iterated <- applyTagged LIterTag (LAdvance 0) begun
  active <- applyTagged LFinishTag (LAdvance 0) iterated
  leftAdded <- applyTagged OInsertTag (OInsert 2 Root emptyConsumerComponent) active
  applyTagged OInsertTag (OInsert 1 Root emptyConsumerComponent) leftAdded)

public export
r193FrameStart : SystemState Nat ToyKey ToyValue ToyRuntime String
r193FrameStart = fromMaybe r193FrameBefore (applyTagged LBeginTag (LBegin 2) r193FrameBefore)

public export
r193FrameChild : SystemState Nat ToyKey ToyValue ToyRuntime String
r193FrameChild = fromMaybe r193FrameStart (applyTagged OInsertTag (OInsert 3 (ChildOf 2) emptyConsumerComponent) r193FrameStart)

public export
r193FrameEnd : SystemState Nat ToyKey ToyValue ToyRuntime String
r193FrameEnd = fromMaybe r193FrameChild (applyTagged LFinishTag (LAdvance 2) r193FrameChild)

public export
r193FrameRightStart : SystemState Nat ToyKey ToyValue ToyRuntime String
r193FrameRightStart = fromMaybe r193FrameEnd (applyTagged LBeginTag (LBegin 1) r193FrameEnd)
