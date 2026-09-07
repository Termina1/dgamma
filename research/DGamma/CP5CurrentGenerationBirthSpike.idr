module DGamma.CP5CurrentGenerationBirthSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryPlan
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionSelectedOwn
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5UniqueRawNameInsertions
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| An authenticated scanner stamp names an actual insertion of the selected
||| raw name in the ORIGINAL checked trace. No caller-selected origin map.
public export
record CurrentGenerationBirth
  (name, key, world, error : Type) (value : key -> Type)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) (selected : name)
  (generation : RegistrationGeneration name) where
  constructor MkCurrentGenerationBirth
  currentBirthParent : Parent name
  currentBirthComponent : Component key value world error
  currentLocatedBirth : LocatedActionOccurrence
    (OInsert selected currentBirthParent currentBirthComponent) trace
  0 currentBirthStampExact : generation =
    MkRegistrationGeneration selected (locatedActionOrdinal currentLocatedBirth)

||| Observe the exact dictionary decision once, retaining its equation.
0 currentPutObserved :
  (name : Type) -> (nameEq : DecEq name) ->
  (inserted : name) -> (fresh : RegistrationGeneration name) ->
  (candidate : name) -> (current : RegistrationGeneration name) ->
  (rest : GenerationEnvironment name) -> (observed : Dec (inserted = candidate)) ->
  (decEq @{nameEq} inserted candidate = observed) ->
  (putCurrentGeneration @{nameEq} inserted fresh ((candidate, current) :: rest) =
    (case observed of
      Yes same => (inserted, fresh) :: rest
      No distinct => (candidate, current) :: putCurrentGeneration @{nameEq} inserted fresh rest))
currentPutObserved name nameEq inserted fresh candidate current rest (Yes same) exact =
  rewrite exact in case same of Refl => Refl
currentPutObserved name nameEq inserted fresh candidate current rest (No distinct) exact =
  rewrite exact in Refl

||| A put entry is either the exact inserted pair or an actual old entry.
||| The recursive view is typed explicitly, never inferred through a local let.
0 currentPutEntryObserved :
  (name : Type) -> (nameEq : DecEq name) ->
  (inserted : name) -> (fresh : RegistrationGeneration name) ->
  (candidate : name) -> (current : RegistrationGeneration name) ->
  (rest : GenerationEnvironment name) -> (observed : Dec (inserted = candidate)) ->
  (decEq @{nameEq} inserted candidate = observed) ->
  ((selected : name) -> (generation : RegistrationGeneration name) ->
    Elem (selected, generation) (putCurrentGeneration @{nameEq} inserted fresh rest) ->
    Either ((selected, generation) = (inserted, fresh)) (Elem (selected, generation) rest)) ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  Elem (selected, generation) (putCurrentGeneration @{nameEq} inserted fresh ((candidate, current) :: rest)) ->
  Either ((selected, generation) = (inserted, fresh)) (Elem (selected, generation) ((candidate, current) :: rest))
currentPutEntryObserved name nameEq inserted fresh candidate current rest (Yes same) exact recur selected generation member =
  case replace {p = Elem (selected, generation)}
    (currentPutObserved name nameEq inserted fresh candidate current rest (Yes same) exact) member of
    Here => Left Refl
    There later => Right (There later)
currentPutEntryObserved name nameEq inserted fresh candidate current rest (No distinct) exact recur selected generation member =
  case replace {p = Elem (selected, generation)}
    (currentPutObserved name nameEq inserted fresh candidate current rest (No distinct) exact) member of
    Here => Right Here
    There later => case recur selected generation later of
      Left same => Left same
      Right old => Right (There old)

0 currentPutEntryOrigin :
  (name : Type) -> (nameEq : DecEq name) ->
  (inserted : name) -> (fresh : RegistrationGeneration name) ->
  (live : GenerationEnvironment name) ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  Elem (selected, generation) (putCurrentGeneration @{nameEq} inserted fresh live) ->
  Either ((selected, generation) = (inserted, fresh)) (Elem (selected, generation) live)
currentPutEntryOrigin name nameEq inserted fresh [] selected generation member = case member of
  Here => Left Refl
  There later => absurd later
currentPutEntryOrigin name nameEq inserted fresh ((candidate, current) :: rest) selected generation member =
  currentPutEntryObserved name nameEq inserted fresh candidate current rest
    (decEq @{nameEq} inserted candidate) Refl
    (currentPutEntryOrigin name nameEq inserted fresh rest) selected generation member

0 currentBirthAfterPut :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) -> (live : GenerationEnvironment name) ->
  (inserted : name) -> (fresh : RegistrationGeneration name) ->
  CurrentGenerationBirth name key world error value global inserted fresh ->
  ((selected : name) -> (generation : RegistrationGeneration name) ->
    Elem (selected, generation) live -> CurrentGenerationBirth name key world error value global selected generation) ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  Elem (selected, generation) (putCurrentGeneration @{nameEq} inserted fresh live) ->
  CurrentGenerationBirth name key world error value global selected generation
currentBirthAfterPut name key world error value nameEq global live inserted fresh birth previous selected generation member =
  case currentPutEntryOrigin name nameEq inserted fresh live selected generation member of
    Left exact => case exact of Refl => birth
    Right old => previous selected generation old

||| The generation update introduces only the actual head insertion at its
||| authenticated global ordinal; all other entries retain their real births.
0 currentBirthAfterAction :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) -> (ordinal : Nat) ->
  (live : GenerationEnvironment name) -> (action : Action name key value world error) ->
  (occurrence : LocatedActionOccurrence action global) ->
  (locatedActionOrdinal occurrence = ordinal) ->
  ((selected : name) -> (generation : RegistrationGeneration name) ->
    Elem (selected, generation) live -> CurrentGenerationBirth name key world error value global selected generation) ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  Elem (selected, generation) (advanceGenerationEnvironment @{nameEq} ordinal action live) ->
  CurrentGenerationBirth name key world error value global selected generation
currentBirthAfterAction name key world error value nameEq global ordinal live (OInsert inserted parent component) occurrence exact previous =
  currentBirthAfterPut name key world error value nameEq global live inserted (MkRegistrationGeneration inserted ordinal)
    (MkCurrentGenerationBirth parent component occurrence (sym (cong (MkRegistrationGeneration inserted) exact))) previous
currentBirthAfterAction name key world error value nameEq global ordinal live (ORetire actor) occurrence exact previous = previous
currentBirthAfterAction name key world error value nameEq global ordinal live (ORemove actor) occurrence exact previous =
  \selected, generation, member => previous selected generation (entryAfterDeleteComesFromOld nameEq actor live selected generation member)
currentBirthAfterAction name key world error value nameEq global ordinal live (LBegin actor) occurrence exact previous = previous
currentBirthAfterAction name key world error value nameEq global ordinal live (LAdvance actor) occurrence exact previous = previous
currentBirthAfterAction name key world error value nameEq global ordinal live (LDivert actor) occurrence exact previous = previous
currentBirthAfterAction name key world error value nameEq global ordinal live (LLeave actor) occurrence exact previous = previous
currentBirthAfterAction name key world error value nameEq global ordinal live (LUnload actor) occurrence exact previous = previous

0 currentBirthPrependLocation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (action : Action name key value world error) ->
  LocatedActionOccurrence action rest -> LocatedActionOccurrence action (MoreTransitions step rest)
currentBirthPrependLocation name key world error value step rest action
  (MkLocatedActionOccurrence before afterState prior located later exact decomposition) =
    MkLocatedActionOccurrence before afterState (MoreTransitions step prior) located later exact
      (cong (MoreTransitions step) decomposition)

0 currentBirthPrependOrdinal :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (action : Action name key value world error) -> (occurrence : LocatedActionOccurrence action rest) ->
  (locatedActionOrdinal (currentBirthPrependLocation name key world error value step rest action occurrence) = S (locatedActionOrdinal occurrence))
currentBirthPrependOrdinal name key world error value step rest action
  (MkLocatedActionOccurrence before afterState prior located later exact decomposition) = Refl

||| Authenticate all current entries by forward induction over the exact scan.
||| The embedding is structural prefix inclusion and carries its ordinal law.
0 currentBirthScanInvariant :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  {initial, finalState, first, last : SystemState name key value world error} ->
  (global : Transitions initial finalState) -> (segment : Transitions first last) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq ordinal live segment finalOrdinal finalLive ->
  (embedding : (action : Action name key value world error) -> LocatedActionOccurrence action segment -> LocatedActionOccurrence action global) ->
  ((action : Action name key value world error) -> (occurrence : LocatedActionOccurrence action segment) ->
    (locatedActionOrdinal (embedding action occurrence) = ordinal + locatedActionOrdinal occurrence)) ->
  ((selected : name) -> (generation : RegistrationGeneration name) ->
    Elem (selected, generation) live -> CurrentGenerationBirth name key world error value global selected generation) ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  Elem (selected, generation) finalLive -> CurrentGenerationBirth name key world error value global selected generation
currentBirthScanInvariant name key world error value nameEq global segment ordinal live finalOrdinal finalLive scan embedding exact previous =
  case scan of
    GenerationTraceScanEnd => previous
    GenerationTraceScanStep step rest tail =>
      currentBirthScanInvariant name key world error value nameEq global rest (S ordinal)
        (advanceGenerationEnvironment @{nameEq} ordinal (transitionAction step) live) finalOrdinal finalLive tail
        (\action, occurrence => embedding action (currentBirthPrependLocation name key world error value step rest action occurrence))
        (\action, occurrence => trans (exact action (currentBirthPrependLocation name key world error value step rest action occurrence))
          (trans (cong (ordinal +) (currentBirthPrependOrdinal name key world error value step rest action occurrence))
            (sym (plusSuccRightSucc ordinal (locatedActionOrdinal occurrence)))))
        (currentBirthAfterAction name key world error value nameEq global ordinal live (transitionAction step)
          (embedding (transitionAction step) (MkLocatedActionOccurrence _ _ NoTransitions step rest Refl Refl))
          (trans (exact (transitionAction step) (MkLocatedActionOccurrence _ _ NoTransitions step rest Refl Refl))
            (plusZeroRightNeutral ordinal)) previous)

||| A scan from the actual empty initial environment supplies its OWN located
||| original birth and exact current stamp. No uniqueness or chosen birth input.
export
0 currentBirthFromGenerationScan :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq Z [] trace finalOrdinal finalLive ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} selected finalLive = Just generation) ->
  CurrentGenerationBirth name key world error value trace selected generation
currentBirthFromGenerationScan name key world error value nameEq trace finalOrdinal finalLive scan selected generation current =
  currentBirthScanInvariant name key world error value nameEq trace trace Z [] finalOrdinal finalLive scan
    (\action, occurrence => occurrence) (\action, occurrence => Refl)
    (\actor, birth, member => absurd member) selected generation
    (currentGenerationEntryFromLookup nameEq selected generation finalLive current)

||| Reconcile the authenticated scan birth with R175 B10's actual component
||| birth at a reached prefix. Uniqueness is used only AFTER both are located.
export
0 currentBirthAtPrefixComponent :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, middle, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (prior : Transitions initial middle) -> (later : Transitions middle finalState) ->
  (appendTransitions prior later = global) ->
  AlignedTransitions name key world error value nameEq keyEq prior ->
  (bindings (registry initial) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq global ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  CurrentGenerationBirth name key world error value global selected generation ->
  (observed : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry middle) = Just observed) ->
  (parent : Parent name **
    birth : LocatedActionOccurrence (OInsert selected parent (fiberComponent observed)) global **
    generation = MkRegistrationGeneration selected (locatedActionOrdinal birth))
currentBirthAtPrefixComponent name key world error value nameEq keyEq global prior later decomposition aligned empty unique
  selected generation authentication observed found =
    case authentication of
      MkCurrentGenerationBirth scanParent scanComponent scanBirth exact =>
        case rawComponentBirthAtPrefix name key world error value nameEq keyEq global prior later decomposition aligned empty selected observed found of
          (parent ** birth) => (parent ** birth ** trans exact
            (cong (MkRegistrationGeneration selected)
              (uniqueInsertionPosition unique selected scanParent parent scanComponent (fiberComponent observed) scanBirth birth)))

export
0 currentBirthTraceAppendEmpty :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) -> (appendTransitions trace NoTransitions = trace)
currentBirthTraceAppendEmpty name key world error value NoTransitions = Refl
currentBirthTraceAppendEmpty name key world error value (MoreTransitions step rest) =
  cong (MoreTransitions step) (currentBirthTraceAppendEmpty name key world error value rest)

||| Explicit observed remove view, not an inferred local evaluator view.
0 currentRemoveViewAbsent :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (actor : name) -> (ambient : world) -> (source : Registry name key value world error) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  RemoveSuccessView name key world error value nameEq actor ambient source tag afterState ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} actor (registry afterState) = Nothing)
currentRemoveViewAbsent name key world error value nameEq actor ambient source _ _
  (MkRemoveSuccessView oldFiber found guards noChild) =
    DGamma.CP4DeletionSelectedOwn.lookupDeleteSelf @{nameEq} actor source
