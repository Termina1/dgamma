module DGamma.CP5RegistrationParentBirthSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryPlan
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Every stored current generation AND parent-activation generation has a
||| genuine birth of its stored raw name in the fixed ORIGINAL global trace.
||| Historical parent stamps need not be endpoint-current; that is separate.
public export
record RegistrationIndexBirths
  (name, key, world, error : Type) (value : key -> Type)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState) (index : RegistrationIndexState name) where
  constructor MkRegistrationIndexBirths
  0 indexCurrentBirths : (selected : name) -> (generation : RegistrationGeneration name) ->
    Elem (selected, generation) (indexedLiveGenerations index) ->
    CurrentGenerationBirth name key world error value global selected generation
  0 indexActivationBirths : (selected : name) -> (activation : RegistrationActivation name) ->
    Elem (selected, activation) (indexedParentActivations index) ->
    CurrentGenerationBirth name key world error value global selected (activationParentGeneration activation)

||| Observe the actual parent-activation dictionary branch explicitly.
0 parentPutObserved :
  (name : Type) -> (nameEq : DecEq name) ->
  (inserted : name) -> (fresh : RegistrationActivation name) ->
  (candidate : name) -> (current : RegistrationActivation name) ->
  (rest : List (name, RegistrationActivation name)) -> (observed : Dec (inserted = candidate)) ->
  (decEq @{nameEq} inserted candidate = observed) ->
  (putParentActivation @{nameEq} inserted fresh ((candidate, current) :: rest) =
    (case observed of
      Yes same => (inserted, fresh) :: rest
      No distinct => (candidate, current) :: putParentActivation @{nameEq} inserted fresh rest))
parentPutObserved name nameEq inserted fresh candidate current rest (Yes same) exact =
  rewrite exact in case same of Refl => Refl
parentPutObserved name nameEq inserted fresh candidate current rest (No distinct) exact =
  rewrite exact in Refl


||| Typed observed entry transport for parent activations.
0 parentPutEntryObserved :
  (name : Type) -> (nameEq : DecEq name) ->
  (inserted : name) -> (fresh : RegistrationActivation name) ->
  (candidate : name) -> (current : RegistrationActivation name) ->
  (rest : List (name, RegistrationActivation name)) -> (observed : Dec (inserted = candidate)) ->
  (decEq @{nameEq} inserted candidate = observed) ->
  ((selected : name) -> (generation : RegistrationActivation name) ->
    Elem (selected, generation) (putParentActivation @{nameEq} inserted fresh rest) ->
    Either ((selected, generation) = (inserted, fresh)) (Elem (selected, generation) rest)) ->
  (selected : name) -> (generation : RegistrationActivation name) ->
  Elem (selected, generation) (putParentActivation @{nameEq} inserted fresh ((candidate, current) :: rest)) ->
  Either ((selected, generation) = (inserted, fresh)) (Elem (selected, generation) ((candidate, current) :: rest))
parentPutEntryObserved name nameEq inserted fresh candidate current rest (Yes same) exact recur selected generation member =
  case replace {p = Elem (selected, generation)}
    (parentPutObserved name nameEq inserted fresh candidate current rest (Yes same) exact) member of
    Here => Left Refl
    There later => Right (There later)
parentPutEntryObserved name nameEq inserted fresh candidate current rest (No distinct) exact recur selected generation member =
  case replace {p = Elem (selected, generation)}
    (parentPutObserved name nameEq inserted fresh candidate current rest (No distinct) exact) member of
    Here => Right Here
    There later => case recur selected generation later of
      Left same => Left same
      Right old => Right (There old)


||| A stored parent activation is the inserted one or a genuine prior entry.
0 parentPutEntryOrigin :
  (name : Type) -> (nameEq : DecEq name) ->
  (inserted : name) -> (fresh : RegistrationActivation name) ->
  (live : List (name, RegistrationActivation name)) ->
  (selected : name) -> (generation : RegistrationActivation name) ->
  Elem (selected, generation) (putParentActivation @{nameEq} inserted fresh live) ->
  Either ((selected, generation) = (inserted, fresh)) (Elem (selected, generation) live)
parentPutEntryOrigin name nameEq inserted fresh [] selected generation member = case member of
  Here => Left Refl
  There later => absurd later
parentPutEntryOrigin name nameEq inserted fresh ((candidate, current) :: rest) selected generation member =
  parentPutEntryObserved name nameEq inserted fresh candidate current rest
    (decEq @{nameEq} inserted candidate) Refl
    (parentPutEntryOrigin name nameEq inserted fresh rest) selected generation member


||| A parent activation carries the genuine insertion birth of its stamped generation.
0 parentBirthAfterPut :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) -> (live : List (name, RegistrationActivation name)) ->
  (inserted : name) -> (fresh : RegistrationActivation name) ->
  CurrentGenerationBirth name key world error value global inserted (activationParentGeneration fresh) ->
  ((selected : name) -> (generation : RegistrationActivation name) ->
    Elem (selected, generation) live -> CurrentGenerationBirth name key world error value global selected (activationParentGeneration generation)) ->
  (selected : name) -> (generation : RegistrationActivation name) ->
  Elem (selected, generation) (putParentActivation @{nameEq} inserted fresh live) ->
  CurrentGenerationBirth name key world error value global selected (activationParentGeneration generation)
parentBirthAfterPut name key world error value nameEq global live inserted fresh birth previous selected generation member =
  case parentPutEntryOrigin name nameEq inserted fresh live selected generation member of
    Left exact => case exact of Refl => birth
    Right old => previous selected generation old


||| Observe only activation-index deletion; this is not a trace withdrawal proof.
0 parentDeleteObserved :
  (name : Type) -> (nameEq : DecEq name) -> (removed, candidate : name) ->
  (current : RegistrationActivation name) -> (rest : List (name, RegistrationActivation name)) ->
  (observed : Dec (removed = candidate)) -> decEq @{nameEq} removed candidate = observed ->
  deleteParentActivation @{nameEq} removed ((candidate, current) :: rest) =
    (case observed of
      Yes same => rest
      No distinct => (candidate, current) :: deleteParentActivation @{nameEq} removed rest)
parentDeleteObserved name nameEq removed candidate current rest (Yes same) exact =
  rewrite exact in case same of Refl => Refl
parentDeleteObserved name nameEq removed candidate current rest (No distinct) exact =
  rewrite exact in Refl

0 parentDeleteEntryObserved :
  (name : Type) -> (nameEq : DecEq name) -> (removed, candidate : name) ->
  (current : RegistrationActivation name) -> (rest : List (name, RegistrationActivation name)) ->
  (observed : Dec (removed = candidate)) -> decEq @{nameEq} removed candidate = observed ->
  ((selected : name) -> (activation : RegistrationActivation name) ->
    Elem (selected, activation) (deleteParentActivation @{nameEq} removed rest) -> Elem (selected, activation) rest) ->
  (selected : name) -> (activation : RegistrationActivation name) ->
  Elem (selected, activation) (deleteParentActivation @{nameEq} removed ((candidate, current) :: rest)) ->
  Elem (selected, activation) ((candidate, current) :: rest)
parentDeleteEntryObserved name nameEq removed candidate current rest (Yes same) exact recur selected activation member =
  There (replace {p = Elem (selected, activation)}
    (parentDeleteObserved name nameEq removed candidate current rest (Yes same) exact) member)
parentDeleteEntryObserved name nameEq removed candidate current rest (No distinct) exact recur selected activation member =
  case replace {p = Elem (selected, activation)}
    (parentDeleteObserved name nameEq removed candidate current rest (No distinct) exact) member of
    Here => Here
    There later => There (recur selected activation later)

0 parentDeleteEntryOrigin :
  (name : Type) -> (nameEq : DecEq name) -> (removed : name) ->
  (activations : List (name, RegistrationActivation name)) ->
  (selected : name) -> (activation : RegistrationActivation name) ->
  Elem (selected, activation) (deleteParentActivation @{nameEq} removed activations) ->
  Elem (selected, activation) activations
parentDeleteEntryOrigin name nameEq removed [] selected activation member = absurd member
parentDeleteEntryOrigin name nameEq removed ((candidate, current) :: rest) selected activation member =
  parentDeleteEntryObserved name nameEq removed candidate current rest
    (decEq @{nameEq} removed candidate) Refl
    (parentDeleteEntryOrigin name nameEq removed rest) selected activation member

0 parentLookupObserved :
  (name : Type) -> (nameEq : DecEq name) -> (selected, candidate : name) ->
  (current : RegistrationActivation name) -> (rest : List (name, RegistrationActivation name)) ->
  (observed : Dec (selected = candidate)) -> decEq @{nameEq} selected candidate = observed ->
  lookupParentActivation @{nameEq} selected ((candidate, current) :: rest) =
    (case observed of
      Yes same => Just current
      No distinct => lookupParentActivation @{nameEq} selected rest)
parentLookupObserved name nameEq selected candidate current rest (Yes same) exact =
  rewrite exact in case same of Refl => Refl
parentLookupObserved name nameEq selected candidate current rest (No distinct) exact =
  rewrite exact in Refl

0 parentLookupEntryObserved :
  (name : Type) -> (nameEq : DecEq name) -> (selected, candidate : name) ->
  (current : RegistrationActivation name) -> (rest : List (name, RegistrationActivation name)) ->
  (observed : Dec (selected = candidate)) -> decEq @{nameEq} selected candidate = observed ->
  ((activation : RegistrationActivation name) -> lookupParentActivation @{nameEq} selected rest = Just activation ->
    Elem (selected, activation) rest) ->
  (activation : RegistrationActivation name) ->
  lookupParentActivation @{nameEq} selected ((candidate, current) :: rest) = Just activation ->
  Elem (selected, activation) ((candidate, current) :: rest)
parentLookupEntryObserved name nameEq selected candidate current rest (Yes same) exact recur activation found =
  replace {p = \entry => Elem entry ((candidate, current) :: rest)}
    (cong2 MkPair (sym same)
      (justInjective (trans (sym (parentLookupObserved name nameEq selected candidate current rest (Yes same) exact)) found))) Here
parentLookupEntryObserved name nameEq selected candidate current rest (No distinct) exact recur activation found =
  There (recur activation
    (trans (sym (parentLookupObserved name nameEq selected candidate current rest (No distinct) exact)) found))

||| Public lookup-to-actual-entry bridge for parent-activation authentication.
export
0 parentActivationEntryFromLookup :
  (name : Type) -> (nameEq : DecEq name) -> (selected : name) ->
  (activations : List (name, RegistrationActivation name)) -> (activation : RegistrationActivation name) ->
  lookupParentActivation @{nameEq} selected activations = Just activation -> Elem (selected, activation) activations
parentActivationEntryFromLookup name nameEq selected [] activation found = case found of Refl impossible
parentActivationEntryFromLookup name nameEq selected ((candidate, current) :: rest) activation found =
  parentLookupEntryObserved name nameEq selected candidate current rest
    (decEq @{nameEq} selected candidate) Refl
    (parentActivationEntryFromLookup name nameEq selected rest) activation found

||| L-Begin stores the actual currently authenticated parent generation.
0 registrationBeginBirthsObserved :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) -> (ordinal : Nat) -> (actor : name) ->
  (live : GenerationEnvironment name) -> (activations : List (name, RegistrationActivation name)) ->
  (counts : List (RegistrationActivation name, Nat)) -> (deleted : List (RegistrationGeneration name)) ->
  RegistrationIndexBirths name key world error value global (MkRegistrationIndexState live activations counts deleted) ->
  (observed : Maybe (RegistrationGeneration name)) -> lookupCurrentGeneration @{nameEq} actor live = observed ->
  RegistrationIndexBirths name key world error value global
    (advanceRegistrationIndex @{nameEq} ordinal (the (Action name key value world error) (LBegin actor))
      (MkRegistrationIndexState live activations counts deleted))
registrationBeginBirthsObserved name key world error value nameEq global ordinal actor live activations counts deleted births Nothing exact =
  rewrite exact in births
registrationBeginBirthsObserved name key world error value nameEq global ordinal actor live activations counts deleted births (Just generation) exact =
  rewrite exact in MkRegistrationIndexBirths (indexCurrentBirths births)
    (parentBirthAfterPut name key world error value nameEq global activations actor (MkRegistrationActivation generation ordinal)
      (indexCurrentBirths births actor generation (currentGenerationEntryFromLookup nameEq actor generation live exact))
      (indexActivationBirths births))

||| Full index-action induction for real current AND historical parent births.
export
0 registrationIndexBirthAction :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) -> (ordinal : Nat) ->
  (action : Action name key value world error) -> (index : RegistrationIndexState name) ->
  (occurrence : LocatedActionOccurrence action global) -> locatedActionOrdinal occurrence = ordinal ->
  RegistrationIndexBirths name key world error value global index ->
  RegistrationIndexBirths name key world error value global (advanceRegistrationIndex @{nameEq} ordinal action index)
registrationIndexBirthAction name key world error value nameEq global ordinal (OInsert actor Root component)
  (MkRegistrationIndexState live activations counts deleted) occurrence exact births =
    MkRegistrationIndexBirths
      (currentBirthActionProgress name key world error value nameEq global ordinal live (OInsert actor Root component) occurrence exact (indexCurrentBirths births))
      (indexActivationBirths births)
registrationIndexBirthAction name key world error value nameEq global ordinal (OInsert child (ChildOf parent) component)
  (MkRegistrationIndexState live activations counts deleted) occurrence exact births =
    MkRegistrationIndexBirths
      (currentBirthActionProgress name key world error value nameEq global ordinal live (OInsert child (ChildOf parent) component) occurrence exact (indexCurrentBirths births))
      (indexActivationBirths births)
registrationIndexBirthAction name key world error value nameEq global ordinal (ORetire actor)
  (MkRegistrationIndexState live activations counts deleted) occurrence exact births = births
registrationIndexBirthAction name key world error value nameEq global ordinal (ORemove actor)
  (MkRegistrationIndexState live activations counts deleted) occurrence exact births =
    MkRegistrationIndexBirths
      (currentBirthActionProgress name key world error value nameEq global ordinal live (ORemove actor) occurrence exact (indexCurrentBirths births))
      (\selected, activation, member => indexActivationBirths births selected activation
        (parentDeleteEntryOrigin name nameEq actor activations selected activation member))
registrationIndexBirthAction name key world error value nameEq global ordinal (LBegin actor)
  (MkRegistrationIndexState live activations counts deleted) occurrence exact births =
    registrationBeginBirthsObserved name key world error value nameEq global ordinal actor live activations counts deleted births
      (lookupCurrentGeneration @{nameEq} actor live) Refl
registrationIndexBirthAction name key world error value nameEq global ordinal (LAdvance actor)
  (MkRegistrationIndexState live activations counts deleted) occurrence exact births = births
registrationIndexBirthAction name key world error value nameEq global ordinal (LDivert actor)
  (MkRegistrationIndexState live activations counts deleted) occurrence exact births = births
registrationIndexBirthAction name key world error value nameEq global ordinal (LLeave actor)
  (MkRegistrationIndexState live activations counts deleted) occurrence exact births = births
registrationIndexBirthAction name key world error value nameEq global ordinal (LUnload actor)
  (MkRegistrationIndexState live activations counts deleted) occurrence exact births =
    MkRegistrationIndexBirths (indexCurrentBirths births)
      (\selected, activation, member => indexActivationBirths births selected activation
        (parentDeleteEntryOrigin name nameEq actor activations selected activation member))

||| Retaining a generated event changes only counters beyond its genuine births.
export
0 registrationSurvivingBirthsObserved :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) -> (ordinal : Nat) -> (child, parent : name) ->
  (component : Component key value world error) ->
  (live : GenerationEnvironment name) -> (activations : List (name, RegistrationActivation name)) ->
  (counts : List (RegistrationActivation name, Nat)) -> (deleted : List (RegistrationGeneration name)) ->
  (occurrence : LocatedActionOccurrence (OInsert child (ChildOf parent) component) global) ->
  locatedActionOrdinal occurrence = ordinal ->
  RegistrationIndexBirths name key world error value global (MkRegistrationIndexState live activations counts deleted) ->
  (observed : Maybe (RegistrationActivation name)) -> lookupParentActivation @{nameEq} parent activations = observed ->
  RegistrationIndexBirths name key world error value global
    (advanceSurvivingRegistrationIndex @{nameEq} ordinal child parent component
      (MkRegistrationIndexState live activations counts deleted))
registrationSurvivingBirthsObserved name key world error value nameEq global ordinal child parent component
  live activations counts deleted occurrence exact births Nothing observedExact =
    rewrite observedExact in registrationIndexBirthAction name key world error value nameEq global ordinal (OInsert child (ChildOf parent) component) (MkRegistrationIndexState live activations counts deleted) occurrence exact births
registrationSurvivingBirthsObserved name key world error value nameEq global ordinal child parent component
  live activations counts deleted occurrence exact births (Just activation) observedExact =
    rewrite observedExact in MkRegistrationIndexBirths
      (indexCurrentBirths (registrationIndexBirthAction name key world error value nameEq global ordinal (OInsert child (ChildOf parent) component) (MkRegistrationIndexState live activations counts deleted) occurrence exact births))
      (indexActivationBirths (registrationIndexBirthAction name key world error value nameEq global ordinal (OInsert child (ChildOf parent) component) (MkRegistrationIndexState live activations counts deleted) occurrence exact births))

||| Counters/discard bookkeeping does not change authenticated birth domains.
||| Only explicit index-field equalities are transported; global trace is fixed.
export
0 registrationIndexBirthsRetarget :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) -> (source, target : RegistrationIndexState name) ->
  indexedLiveGenerations source = indexedLiveGenerations target ->
  indexedParentActivations source = indexedParentActivations target ->
  RegistrationIndexBirths name key world error value global source ->
  RegistrationIndexBirths name key world error value global target
registrationIndexBirthsRetarget name key world error value global source target liveSame activationsSame births =
  MkRegistrationIndexBirths
    (\selected, generation, member => indexCurrentBirths births selected generation
      (replace {p = Elem (selected, generation)} (sym liveSame) member))
    (\selected, activation, member => indexActivationBirths births selected activation
      (replace {p = Elem (selected, activation)} (sym activationsSame) member))

||| The event's observed parent activation names a genuine original parent birth.
export
0 registrationEventParentBirthHead :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) -> (ordinal : Nat) -> (index : RegistrationIndexState name) ->
  (child, parent : name) -> (component : Component key value world error) ->
  RegistrationIndexBirths name key world error value global index ->
  (activation : RegistrationActivation name) ->
  eventParentActivation (registrationEventAt @{nameEq} ordinal index child parent component) = Just activation ->
  CurrentGenerationBirth name key world error value global
    (eventParent (registrationEventAt @{nameEq} ordinal index child parent component))
    (activationParentGeneration activation)
registrationEventParentBirthHead name key world error value nameEq global ordinal
  (MkRegistrationIndexState live activations counts deleted) child parent component births activation present =
    indexActivationBirths births parent activation
      (parentActivationEntryFromLookup name nameEq parent activations activation present)
