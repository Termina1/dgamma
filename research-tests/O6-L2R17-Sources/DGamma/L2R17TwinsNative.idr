module DGamma.L2R17TwinsNative

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.EqOrd
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5UniqueRawNameInsertions
import DGamma.L2R2SmallStates
import DGamma.L2R3ForcedClosure
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R10OrdinalData
import DGamma.L2R16AnchorStates
import DGamma.L2R16AnchorNative
import DGamma.L2R16AnchorTrace
import DGamma.L2R16AnchorTrail
import DGamma.L2R16ProductionBridge
import Data.Bool
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core
import Decidable.Decidable

%default total
%unbound_implicits off

||| Executable checked trace builder, stopping at the first rejected edge.
||| No success is postulated: later concrete shape proofs must compute the
||| entire requested word. The checked result is observed at its call site.
public export
runNative : (source : SystemState Nat Bool (\key => Unit) Unit String) ->
  List (Action Nat Bool (\key => Unit) Unit String) ->
  (target : SystemState Nat Bool (\key => Unit) Unit String ** Transitions source target)
runNative source [] = (source ** NoTransitions)
runNative source (action :: rest) =
  case the (answer : Maybe (RuleTag, SystemState Nat Bool (\key => Unit) Unit String) **
    checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} action source = answer)
    (checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} action source ** Refl) of
      (Nothing ** observed) => (source ** NoTransitions)
      (Just (tag, middle) ** observed) =>
        (fst (runNative middle rest) **
          MoreTransitions (Fired {before = source} {afterState = middle}
            (fst fixtureDictionaries) (snd fixtureDictionaries) action tag observed)
            (snd (runNative middle rest)))
