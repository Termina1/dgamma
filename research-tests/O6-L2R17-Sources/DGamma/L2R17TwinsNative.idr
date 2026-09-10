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

||| Two installed actors and their own key-disjoint children. This is an
||| explicit initial registry, NOT bundle-history evidence. Every production
||| ActorWithForcedRoots wrapper below starts its own priorRoots at [].
public export
twinsInput : (SystemState Nat Bool (\key => Unit) Unit String,
  List (Action Nat Bool (\key => Unit) Unit String),
  List (Action Nat Bool (\key => Unit) Unit String))
twinsInput =
  (MkSystemState ()
    (insertBinding @{fst fixtureDictionaries} 1 (freshFiber (anchorComponent True) (ChildOf 0))
      (insertBinding @{fst fixtureDictionaries} 3 (freshFiber (anchorComponent False) (ChildOf 2))
        (insertBinding @{fst fixtureDictionaries} 0 (freshFiber (smallComponent False) Root)
          (insertBinding @{fst fixtureDictionaries} 2 (freshFiber (smallComponent False) Root)
            emptyContext Refl) Refl) Refl) Refl),
   [LBegin 0, LAdvance 0, ORetire 1, ORemove 1, OInsert 4 Root (anchorComponent True)],
   [LBegin 2, LAdvance 2, ORetire 3, ORemove 3, OInsert 5 Root (anchorComponent False)])

||| Actual computed cut in either block ordering; a rejected request halts
||| rather than inventing a state. The block constructors certify success.
public export
twinsCut : Bool -> Nat -> SystemState Nat Bool (\key => Unit) Unit String
twinsCut swapped position = fst (runNative (fst twinsInput)
  (Data.List.take position (if swapped
    then snd (snd twinsInput) ++ fst (snd twinsInput)
    else fst (snd twinsInput) ++ snd (snd twinsInput))))
