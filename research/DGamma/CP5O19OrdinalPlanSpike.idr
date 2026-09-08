module DGamma.CP5O19OrdinalPlanSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5UniqueRawNameOrdinalCapital
import DGamma.CP5O19AdjacentReplayProducerSpike
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| The sealed numeric adjacent transposition is its own inverse. This is
||| ordinal-only, so equal action labels never identify distinct occurrences.
export
0 o19AdjacentOrdinalSymmetric :
  {point, target, source : Nat} -> AdjacentSwapOrdinalRelation point target source ->
  AdjacentSwapOrdinalRelation point source target
o19AdjacentOrdinalSymmetric (AdjacentPrefixOrdinal earlier) = AdjacentPrefixOrdinal earlier
o19AdjacentOrdinalSymmetric AdjacentMovedRightOrdinal = AdjacentMovedLeftOrdinal
o19AdjacentOrdinalSymmetric AdjacentMovedLeftOrdinal = AdjacentMovedRightOrdinal
o19AdjacentOrdinalSymmetric (AdjacentSuffixOrdinal later) = AdjacentSuffixOrdinal later

||| An ACTUAL sealed node's origin ordinal agrees with the executable
||| four-region classifier. Source-position uniqueness is not action equality.
export
0 o19AdjacentSourceOrdinalExact :
  (point, target, source : Nat) -> AdjacentSwapOrdinalRelation point target source ->
  (source = fst (adjacentSwapOrdinalExhaustive point target))
o19AdjacentSourceOrdinalExact point target source relation =
  uniqueAdjacentOrdinalInjective point source (fst (adjacentSwapOrdinalExhaustive point target)) target target
    (o19AdjacentOrdinalSymmetric relation)
    (o19AdjacentOrdinalSymmetric (snd (adjacentSwapOrdinalExhaustive point target))) Refl

||| The same actual prefix correspondence owns an executable ordinal map
||| and its all-occurrence authentication. This distinguishes repeated Iter
||| occurrences even when their complete action/tag labels are identical.
public export
record O19OrdinalActionMap
  (name, key, world, error : Type) (value : key -> Type)
  {sourceFirst, sourceFinal, currentFirst, currentFinal : SystemState name key value world error}
  (source : Transitions sourceFirst sourceFinal) (current : Transitions currentFirst currentFinal)
  (correspondence : ActionRegistrationReplayCorrespondence name key world error value source current) where
  constructor MkO19OrdinalActionMap
  ordinalOrigin : Nat -> Nat
  0 ordinalOriginExact : {action : Action name key value world error} ->
    (occurrence : LocatedActionOccurrence action current) ->
    (locatedActionOrdinal (replayActionOrigin correspondence occurrence) = ordinalOrigin (locatedActionOrdinal occurrence))

||| Compose the SAME prefix ordinal map through one ACTUAL sealed adjacent
||| result. Both the correspondence index and every new ordinal equation use
||| the very same node's operationalOccurrenceFold.
public export
0 o19OrdinalMapAfterNode :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} -> {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, sourceFinal, currentFinal, before, middle, afterState : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> {current : Transitions initial currentFinal} ->
  (correspondence : ActionRegistrationReplayCorrespondence name key world error value source current) ->
  O19OrdinalActionMap name key world error value source current correspondence ->
  (earlier : Transitions initial before) -> (left : Transition before middle) -> (right : Transition middle afterState) ->
  (later : Transitions afterState currentFinal) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq current earlier left right later diamond) ->
  O19OrdinalActionMap name key world error value source (swappedTrace result)
    (composeActionRegistrationReplayCorrespondence correspondence (swappedOccurrenceCorrespondence result))
o19OrdinalMapAfterNode correspondence previous earlier left right later diamond result =
  MkO19OrdinalActionMap
    (\position => ordinalOrigin previous (fst (adjacentSwapOrdinalExhaustive (transitionCount earlier) position)))
    (\occurrence => trans (ordinalOriginExact previous (replayActionOrigin (swappedOccurrenceCorrespondence result) occurrence))
      (cong (ordinalOrigin previous)
        (o19AdjacentSourceOrdinalExact (transitionCount earlier) (locatedActionOrdinal occurrence)
          (locatedActionOrdinal (replayActionOrigin (swappedOccurrenceCorrespondence result) occurrence))
          (operationalOrdinalRelation (swappedOccurrenceFold result) occurrence))))

||| The ORIGINAL coordinate map starts at actual correspondence identity.
export
0 o19IdentityOrdinalMap :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, last : SystemState name key value world error} -> (source : Transitions first last) ->
  O19OrdinalActionMap name key world error value source source (identityActionRegistrationReplayCorrespondence source)
o19IdentityOrdinalMap source = MkO19OrdinalActionMap id (\occurrence => Refl)

||| Exact GLOBAL-origin plan for a real finite chain. Unlike the paper's
||| BlockCrossingOriginPlan this does not claim selected-block-local ranges
||| or Cartesian coverage. It records the two TRUE source ordinals at every
||| node while definitionally composing that same node's occurrence map.
public export
data O19GlobalCrossingPlan :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  {currentFinal, targetFinal : SystemState name key value world error} ->
  {current : Transitions initial currentFinal} -> {target : Transitions initial targetFinal} ->
  (correspondence : ActionRegistrationReplayCorrespondence name key world error value source current) ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq current target -> List (Nat, Nat) -> Type where
  GlobalOriginPlanDone :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {protocol : RegistrationProtocol key value world error} -> {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {initial, sourceFinal, currentFinal : SystemState name key value world error} ->
    {source : Transitions initial sourceFinal} -> {current : Transitions initial currentFinal} ->
    {correspondence : ActionRegistrationReplayCorrespondence name key world error value source current} ->
    O19GlobalCrossingPlan name key world error value protocol nameEq keyEq source correspondence FiniteAdjacentSwapDone []
  GlobalOriginPlanStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {protocol : RegistrationProtocol key value world error} -> {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {initial, sourceFinal, currentFinal, before, middle, afterState, targetFinal : SystemState name key value world error} ->
    {source : Transitions initial sourceFinal} ->
    (current : Transitions initial currentFinal) -> (earlier : Transitions initial before) ->
    (left : Transition before middle) -> (right : Transition middle afterState) -> (later : Transitions afterState currentFinal) ->
    (orientation : AdjacentSwapOrientationEvidence left right) ->
    (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
    (result : AdjacentSwapResult name key world error value protocol nameEq keyEq current earlier left right later diamond) ->
    (target : Transitions initial targetFinal) ->
    (rest : FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq (swappedTrace result) target) ->
    (correspondence : ActionRegistrationReplayCorrespondence name key world error value source current) ->
    (leftOrdinal, rightOrdinal : Nat) ->
    (0 leftExact : locatedActionOrdinal (replayActionOrigin correspondence (adjacentLeftNodeOccurrence result)) = leftOrdinal) ->
    (0 rightExact : locatedActionOrdinal (replayActionOrigin correspondence (adjacentRightNodeOccurrence result)) = rightOrdinal) ->
    (positions : List (Nat, Nat)) ->
    O19GlobalCrossingPlan name key world error value protocol nameEq keyEq source
      (composeActionRegistrationReplayCorrespondence correspondence (swappedOccurrenceCorrespondence result)) rest positions ->
    O19GlobalCrossingPlan name key world error value protocol nameEq keyEq source correspondence
      (FiniteAdjacentSwapStep current earlier left right later orientation diamond result target rest)
      ((leftOrdinal, rightOrdinal) :: positions)

||| Simultaneous global list, authentic source-origin plan and exact node
||| count. This is NOT selected Cartesian coverage, bounds or uniqueness.
public export
record O19GlobalPlanResult
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error) (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, sourceFinal : SystemState name key value world error} (source : Transitions initial sourceFinal)
  {currentFinal, targetFinal : SystemState name key value world error}
  {current : Transitions initial currentFinal} {target : Transitions initial targetFinal}
  (correspondence : ActionRegistrationReplayCorrespondence name key world error value source current)
  (derivation : FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq current target) where
  constructor MkO19GlobalPlanResult
  globalCrossingPositions : List (Nat, Nat)
  0 globalCrossingPlan : O19GlobalCrossingPlan name key world error value protocol nameEq keyEq source correspondence derivation globalCrossingPositions
  0 globalCrossingCount : length globalCrossingPositions = finiteAdjacentSwapNodeCount derivation

||| Prepend the ACTUAL node to an explicit already-produced tail plan.
||| Coordinates are evaluated from the authentic current prefix map; exact
||| occurrence equations and count are constructed with that same list.
export
0 o19GlobalPlanPrepend :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} -> {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, sourceFinal, currentFinal, before, middle, afterState, targetFinal : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} ->
  (current : Transitions initial currentFinal) -> (earlier : Transitions initial before) ->
  (left : Transition before middle) -> (right : Transition middle afterState) -> (later : Transitions afterState currentFinal) ->
  (orientation : AdjacentSwapOrientationEvidence left right) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq current earlier left right later diamond) ->
  (target : Transitions initial targetFinal) ->
  (rest : FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq (swappedTrace result) target) ->
  (correspondence : ActionRegistrationReplayCorrespondence name key world error value source current) ->
  (currentMap : O19OrdinalActionMap name key world error value source current correspondence) ->
  O19GlobalPlanResult name key world error value protocol nameEq keyEq source
    (composeActionRegistrationReplayCorrespondence correspondence (swappedOccurrenceCorrespondence result)) rest ->
  O19GlobalPlanResult name key world error value protocol nameEq keyEq source correspondence
    (FiniteAdjacentSwapStep current earlier left right later orientation diamond result target rest)
o19GlobalPlanPrepend current earlier left right later orientation diamond result target rest correspondence currentMap
  (MkO19GlobalPlanResult positions plan count) =
    MkO19GlobalPlanResult
      ((ordinalOrigin currentMap (transitionCount earlier), ordinalOrigin currentMap (S (transitionCount earlier))) :: positions)
      (GlobalOriginPlanStep current earlier left right later orientation diamond result target rest correspondence
        (ordinalOrigin currentMap (transitionCount earlier)) (ordinalOrigin currentMap (S (transitionCount earlier)))
        (ordinalOriginExact currentMap (adjacentLeftNodeOccurrence result))
        (trans (ordinalOriginExact currentMap (adjacentRightNodeOccurrence result))
          (cong (ordinalOrigin currentMap) (transitionPrefixLength earlier left))) positions plan)
      (cong S count)

||| Construct the exact GLOBAL source-origin plan for every node of an
||| ACTUAL finite derivation. The current map is threaded by the same sealed
||| result, not selected afresh or inferred from equal action words. No
||| crossing ordinal equations or plan are required from the caller.
public export
0 o19BuildGlobalOriginPlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} -> {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, sourceFinal, currentFinal, targetFinal : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> {current : Transitions initial currentFinal} -> {target : Transitions initial targetFinal} ->
  (correspondence : ActionRegistrationReplayCorrespondence name key world error value source current) ->
  O19OrdinalActionMap name key world error value source current correspondence ->
  (derivation : FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq current target) ->
  O19GlobalPlanResult name key world error value protocol nameEq keyEq source correspondence derivation
o19BuildGlobalOriginPlan correspondence currentMap FiniteAdjacentSwapDone = MkO19GlobalPlanResult [] GlobalOriginPlanDone Refl
o19BuildGlobalOriginPlan correspondence currentMap
  (FiniteAdjacentSwapStep current earlier left right later orientation diamond result target rest) =
    o19GlobalPlanPrepend current earlier left right later orientation diamond result target rest correspondence currentMap
      (o19BuildGlobalOriginPlan
        (composeActionRegistrationReplayCorrespondence correspondence (swappedOccurrenceCorrespondence result))
        (o19OrdinalMapAfterNode correspondence currentMap earlier left right later diamond result) rest)

||| Localize a produced GLOBAL plan using ONE exact offset-list equation.
||| This transports real node origins, not action labels. Proving that the
||| actual Cartesian algorithm's global list IS the shifted complete/unique
||| Cartesian coordinate list remains the explicit missing obligation.
export
0 o19LocalizeGlobalPlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} -> {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, sourceFinal, currentFinal, targetFinal : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> {current : Transitions initial currentFinal} -> {target : Transitions initial targetFinal} ->
  {correspondence : ActionRegistrationReplayCorrespondence name key world error value source current} ->
  {derivation : FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq current target} ->
  {leftActor, rightActor : name} ->
  (leftBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq leftActor source) ->
  (rightBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq rightActor source) ->
  {globalPositions : List (Nat, Nat)} ->
  O19GlobalCrossingPlan name key world error value protocol nameEq keyEq source correspondence derivation globalPositions ->
  (positions : List (Nat, Nat)) ->
  (globalPositions = map (\pair => (transitionCount (traceBeforeBlock leftBlock) + fst pair, transitionCount (traceBeforeBlock rightBlock) + snd pair)) positions) ->
  BlockCrossingOriginPlan name key world error value protocol nameEq keyEq source leftBlock rightBlock correspondence derivation positions
o19LocalizeGlobalPlan leftBlock rightBlock GlobalOriginPlanDone [] exact = CrossingOriginPlanDone
o19LocalizeGlobalPlan leftBlock rightBlock GlobalOriginPlanDone (pair :: positions) exact = void (uninhabited (cong length exact))
o19LocalizeGlobalPlan leftBlock rightBlock
  (GlobalOriginPlanStep current earlier left right later orientation diamond result target rest correspondence leftOrdinal rightOrdinal leftExact rightExact globalPositions tail)
  [] exact = void (uninhabited (cong length exact))
o19LocalizeGlobalPlan leftBlock rightBlock
  (GlobalOriginPlanStep current earlier left right later orientation diamond result target rest correspondence leftOrdinal rightOrdinal leftExact rightExact globalPositions tail)
  ((leftPosition, rightPosition) :: positions) exact =
    CrossingOriginPlanStep current earlier left right later orientation diamond result target rest correspondence leftBlock rightBlock
      (trans leftExact (cong fst (fst (consInjective exact))))
      (trans rightExact (cong snd (fst (consInjective exact)))) positions
      (o19LocalizeGlobalPlan leftBlock rightBlock tail positions (snd (consInjective exact)))

||| Every ACTUAL finite sealed replay is ordinal-injective for ALL actions,
||| not merely O-Insert births. Repeated identical Iter labels therefore
||| remain distinct. This does not itself make the algorithm's crossing-pair
||| list unique: an arbitrary finite derivation may still revisit a pair.
export
0 o19FiniteOrdinalInjective :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} -> {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> {target : Transitions initial targetFinal} ->
  (derivation : FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq source target) ->
  {firstAction, secondAction : Action name key value world error} ->
  (first : LocatedActionOccurrence firstAction target) -> (second : LocatedActionOccurrence secondAction target) ->
  (locatedActionOrdinal (replayActionOrigin (finiteDerivationOccurrenceCorrespondence derivation) first) =
    locatedActionOrdinal (replayActionOrigin (finiteDerivationOccurrenceCorrespondence derivation) second)) ->
  (locatedActionOrdinal first = locatedActionOrdinal second)
o19FiniteOrdinalInjective FiniteAdjacentSwapDone first second exact = exact
o19FiniteOrdinalInjective
  (FiniteAdjacentSwapStep source earlier left right later orientation diamond result target rest) first second exact =
    o19FiniteOrdinalInjective rest first second
      (uniqueAdjacentOrdinalInjective (transitionCount earlier)
        (locatedActionOrdinal (replayActionOrigin (finiteDerivationOccurrenceCorrespondence rest) first))
        (locatedActionOrdinal (replayActionOrigin (finiteDerivationOccurrenceCorrespondence rest) second))
        (locatedActionOrdinal (replayActionOrigin (swappedOccurrenceCorrespondence result)
          (replayActionOrigin (finiteDerivationOccurrenceCorrespondence rest) first)))
        (locatedActionOrdinal (replayActionOrigin (swappedOccurrenceCorrespondence result)
          (replayActionOrigin (finiteDerivationOccurrenceCorrespondence rest) second)))
        (operationalOrdinalRelation (swappedOccurrenceFold result) (replayActionOrigin (finiteDerivationOccurrenceCorrespondence rest) first))
        (operationalOrdinalRelation (swappedOccurrenceFold result) (replayActionOrigin (finiteDerivationOccurrenceCorrespondence rest) second)) exact)

||| Observe ONE explicit produced tail-plan constructor at B11's prepend
||| boundary. This is not a scalar Refl claim about nested Cartesian builders.
export
0 o19GlobalPlanPrependPositions :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} -> {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, sourceFinal, currentFinal, before, middle, afterState, targetFinal : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} ->
  (current : Transitions initial currentFinal) -> (earlier : Transitions initial before) ->
  (left : Transition before middle) -> (right : Transition middle afterState) -> (later : Transitions afterState currentFinal) ->
  (orientation : AdjacentSwapOrientationEvidence left right) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq current earlier left right later diamond) ->
  (target : Transitions initial targetFinal) ->
  (rest : FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq (swappedTrace result) target) ->
  (correspondence : ActionRegistrationReplayCorrespondence name key world error value source current) ->
  (currentMap : O19OrdinalActionMap name key world error value source current correspondence) ->
  (tailPlan : O19GlobalPlanResult name key world error value protocol nameEq keyEq source
    (composeActionRegistrationReplayCorrespondence correspondence (swappedOccurrenceCorrespondence result)) rest) ->
  (globalCrossingPositions (o19GlobalPlanPrepend current earlier left right later orientation diamond result target rest correspondence currentMap tailPlan) =
    (ordinalOrigin currentMap (transitionCount earlier), ordinalOrigin currentMap (S (transitionCount earlier))) :: globalCrossingPositions tailPlan)
o19GlobalPlanPrependPositions current earlier left right later orientation diamond result target rest correspondence currentMap
  (MkO19GlobalPlanResult positions plan count) = Refl

||| Pointwise observation of B8's SINGLE identity-map constructor in its
||| owning producer module. No function extensionality or rebuilt replay.
export
0 o19IdentityOrdinalMapPoint :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, last : SystemState name key value world error} -> (source : Transitions first last) -> (position : Nat) ->
  (ordinalOrigin (o19IdentityOrdinalMap source) position = position)
o19IdentityOrdinalMapPoint source position = Refl
