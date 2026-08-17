module DGamma.CP4ProgressNumeric

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressBound
import DGamma.CP4ProgressProgramBound
import DGamma.CP4ProgressPotential
import DGamma.CP4ProgressStepCore
import DGamma.CP4ProgressStep
import Data.Nat
import Decidable.Equality

%default total

0 stayedOwnerBudget :
  LTE restSteps (middlePotential + tailBudget) ->
  LTE (S middlePotential) firstPotential ->
  LTE (S restSteps) (firstPotential + tailBudget)
stayedOwnerBudget restBound drops = lteTransitive (LTESucc restBound)
  (plusLteMonotoneRight tailBudget (S middlePotential) firstPotential drops)

0 changedForeignBudget :
  LTE restSteps (middlePotential + tailBudget) ->
  LTE middlePotential interval ->
  LTE restSteps (firstPotential + (interval + tailBudget))
changedForeignBudget restBound middleBound =
  let toInterval = lteTransitive restBound
        (plusLteMonotoneRight tailBudget middlePotential interval middleBound)
      addFirst = plusLteMonotoneRight (interval + tailBudget) Z firstPotential
        LTEZero
  in lteTransitive toInterval addFirst

0 changedOwnerBudget :
  LTE restSteps (middlePotential + tailBudget) ->
  LTE middlePotential interval -> LTE 1 firstPotential ->
  LTE (S restSteps) (firstPotential + (interval + tailBudget))
changedOwnerBudget restBound middleBound sourcePositive =
  let toInterval = lteTransitive restBound
        (plusLteMonotoneRight tailBudget middlePotential interval middleBound)
      successor = LTESucc toInterval
      absorb = plusLteMonotoneRight (interval + tailBudget) 1 firstPotential
        sourcePositive
  in lteTransitive successor absorb

0 countedHeadSame :
  (nameEq : DecEq name) -> (owner, actor : name) -> (later : Nat) ->
  owner = actor ->
  (case decEq @{nameEq} owner actor of
    Yes Refl => S later
    No distinct => later) = S later
countedHeadSame nameEq owner actor later same with
  (decEq @{nameEq} owner actor)
  countedHeadSame nameEq _ actor later same | Yes Refl = Refl
  countedHeadSame nameEq owner actor later same | No distinct =
    void (distinct same)

0 countedHeadDifferent :
  (nameEq : DecEq name) -> (owner, actor : name) -> (later : Nat) ->
  Not (owner = actor) ->
  (case decEq @{nameEq} owner actor of
    Yes Refl => S later
    No distinct => later) = later
countedHeadDifferent nameEq owner actor later different with
  (decEq @{nameEq} owner actor)
  countedHeadDifferent nameEq _ actor later different | Yes same =
    void (different same)
  countedHeadDifferent nameEq owner actor later different | No distinct = Refl

0 countedActionHeadSame :
  (nameEq : DecEq name) ->
  (action : Action name key value world error) -> (actor : name) ->
  (later : Nat) -> actionOwner action = actor ->
  (case action of
    OInsert owner parent component => case decEq @{nameEq} owner actor of
      Yes Refl => S later
      No distinct => later
    ORetire owner => case decEq @{nameEq} owner actor of
      Yes Refl => S later
      No distinct => later
    ORemove owner => case decEq @{nameEq} owner actor of
      Yes Refl => S later
      No distinct => later
    LBegin owner => case decEq @{nameEq} owner actor of
      Yes Refl => S later
      No distinct => later
    LAdvance owner => case decEq @{nameEq} owner actor of
      Yes Refl => S later
      No distinct => later
    LDivert owner => case decEq @{nameEq} owner actor of
      Yes Refl => S later
      No distinct => later
    LLeave owner => case decEq @{nameEq} owner actor of
      Yes Refl => S later
      No distinct => later
    LUnload owner => case decEq @{nameEq} owner actor of
      Yes Refl => S later
      No distinct => later) = S later
countedActionHeadSame nameEq (OInsert owner parent component) actor later same with
  (decEq @{nameEq} owner actor)
  countedActionHeadSame nameEq (OInsert _ parent component) _ later same | Yes Refl = Refl
  countedActionHeadSame nameEq (OInsert owner parent component) actor later same | No distinct =
    void (distinct same)
countedActionHeadSame nameEq (ORetire owner) actor later same with
  (decEq @{nameEq} owner actor)
  countedActionHeadSame nameEq (ORetire _) _ later same | Yes Refl = Refl
  countedActionHeadSame nameEq (ORetire owner) actor later same | No distinct =
    void (distinct same)
countedActionHeadSame nameEq (ORemove owner) actor later same with
  (decEq @{nameEq} owner actor)
  countedActionHeadSame nameEq (ORemove _) _ later same | Yes Refl = Refl
  countedActionHeadSame nameEq (ORemove owner) actor later same | No distinct =
    void (distinct same)
countedActionHeadSame nameEq (LBegin owner) actor later same with
  (decEq @{nameEq} owner actor)
  countedActionHeadSame nameEq (LBegin _) _ later same | Yes Refl = Refl
  countedActionHeadSame nameEq (LBegin owner) actor later same | No distinct =
    void (distinct same)
countedActionHeadSame nameEq (LAdvance owner) actor later same with
  (decEq @{nameEq} owner actor)
  countedActionHeadSame nameEq (LAdvance _) _ later same | Yes Refl = Refl
  countedActionHeadSame nameEq (LAdvance owner) actor later same | No distinct =
    void (distinct same)
countedActionHeadSame nameEq (LDivert owner) actor later same with
  (decEq @{nameEq} owner actor)
  countedActionHeadSame nameEq (LDivert _) _ later same | Yes Refl = Refl
  countedActionHeadSame nameEq (LDivert owner) actor later same | No distinct =
    void (distinct same)
countedActionHeadSame nameEq (LLeave owner) actor later same with
  (decEq @{nameEq} owner actor)
  countedActionHeadSame nameEq (LLeave _) _ later same | Yes Refl = Refl
  countedActionHeadSame nameEq (LLeave owner) actor later same | No distinct =
    void (distinct same)
countedActionHeadSame nameEq (LUnload owner) actor later same with
  (decEq @{nameEq} owner actor)
  countedActionHeadSame nameEq (LUnload _) _ later same | Yes Refl = Refl
  countedActionHeadSame nameEq (LUnload owner) actor later same | No distinct =
    void (distinct same)

0 countedActionHeadDifferent :
  (nameEq : DecEq name) ->
  (action : Action name key value world error) -> (actor : name) ->
  (later : Nat) -> Not (actionOwner action = actor) ->
  (case action of
    OInsert owner parent component => case decEq @{nameEq} owner actor of
      Yes Refl => S later
      No distinct => later
    ORetire owner => case decEq @{nameEq} owner actor of
      Yes Refl => S later
      No distinct => later
    ORemove owner => case decEq @{nameEq} owner actor of
      Yes Refl => S later
      No distinct => later
    LBegin owner => case decEq @{nameEq} owner actor of
      Yes Refl => S later
      No distinct => later
    LAdvance owner => case decEq @{nameEq} owner actor of
      Yes Refl => S later
      No distinct => later
    LDivert owner => case decEq @{nameEq} owner actor of
      Yes Refl => S later
      No distinct => later
    LLeave owner => case decEq @{nameEq} owner actor of
      Yes Refl => S later
      No distinct => later
    LUnload owner => case decEq @{nameEq} owner actor of
      Yes Refl => S later
      No distinct => later) = later
countedActionHeadDifferent nameEq (OInsert owner parent component) actor later different with
  (decEq @{nameEq} owner actor)
  countedActionHeadDifferent nameEq (OInsert _ parent component) _ later different | Yes same =
    void (different same)
  countedActionHeadDifferent nameEq (OInsert owner parent component) actor later different | No distinct = Refl
countedActionHeadDifferent nameEq (ORetire owner) actor later different with
  (decEq @{nameEq} owner actor)
  countedActionHeadDifferent nameEq (ORetire _) _ later different | Yes same =
    void (different same)
  countedActionHeadDifferent nameEq (ORetire owner) actor later different | No distinct = Refl
countedActionHeadDifferent nameEq (ORemove owner) actor later different with
  (decEq @{nameEq} owner actor)
  countedActionHeadDifferent nameEq (ORemove _) _ later different | Yes same =
    void (different same)
  countedActionHeadDifferent nameEq (ORemove owner) actor later different | No distinct = Refl
countedActionHeadDifferent nameEq (LBegin owner) actor later different with
  (decEq @{nameEq} owner actor)
  countedActionHeadDifferent nameEq (LBegin _) _ later different | Yes same =
    void (different same)
  countedActionHeadDifferent nameEq (LBegin owner) actor later different | No distinct = Refl
countedActionHeadDifferent nameEq (LAdvance owner) actor later different with
  (decEq @{nameEq} owner actor)
  countedActionHeadDifferent nameEq (LAdvance _) _ later different | Yes same =
    void (different same)
  countedActionHeadDifferent nameEq (LAdvance owner) actor later different | No distinct = Refl
countedActionHeadDifferent nameEq (LDivert owner) actor later different with
  (decEq @{nameEq} owner actor)
  countedActionHeadDifferent nameEq (LDivert _) _ later different | Yes same =
    void (different same)
  countedActionHeadDifferent nameEq (LDivert owner) actor later different | No distinct = Refl
countedActionHeadDifferent nameEq (LLeave owner) actor later different with
  (decEq @{nameEq} owner actor)
  countedActionHeadDifferent nameEq (LLeave _) _ later different | Yes same =
    void (different same)
  countedActionHeadDifferent nameEq (LLeave owner) actor later different | No distinct = Refl
countedActionHeadDifferent nameEq (LUnload owner) actor later different with
  (decEq @{nameEq} owner actor)
  countedActionHeadDifferent nameEq (LUnload _) _ later different | Yes same =
    void (different same)
  countedActionHeadDifferent nameEq (LUnload owner) actor later different | No distinct = Refl

0 countedFiredHeadSame :
  {first, middle : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action first =
    Just (tag, middle)) ->
  (actor : name) -> (later : Nat) -> actionOwner action = actor ->
  (case decEq @{nameEq}
    (transitionActor (Fired {before = first} {afterState = middle}
      nameEq keyEq action tag checked)) actor of
    Yes Refl => S later
    No distinct => later) = S later
countedFiredHeadSame nameEq keyEq (OInsert owner parent component) tag checked
  actor later same with (decEq @{nameEq} owner actor)
  countedFiredHeadSame nameEq keyEq (OInsert _ parent component) tag checked _
    later same | Yes Refl = Refl
  countedFiredHeadSame nameEq keyEq (OInsert owner parent component) tag checked
    actor later same | No distinct = void (distinct same)
countedFiredHeadSame nameEq keyEq (ORetire owner) tag checked actor later same
  with (decEq @{nameEq} owner actor)
  countedFiredHeadSame nameEq keyEq (ORetire _) tag checked _ later same |
    Yes Refl = Refl
  countedFiredHeadSame nameEq keyEq (ORetire owner) tag checked actor later same |
    No distinct = void (distinct same)
countedFiredHeadSame nameEq keyEq (ORemove owner) tag checked actor later same
  with (decEq @{nameEq} owner actor)
  countedFiredHeadSame nameEq keyEq (ORemove _) tag checked _ later same |
    Yes Refl = Refl
  countedFiredHeadSame nameEq keyEq (ORemove owner) tag checked actor later same |
    No distinct = void (distinct same)
countedFiredHeadSame nameEq keyEq (LBegin owner) tag checked actor later same
  with (decEq @{nameEq} owner actor)
  countedFiredHeadSame nameEq keyEq (LBegin _) tag checked _ later same |
    Yes Refl = Refl
  countedFiredHeadSame nameEq keyEq (LBegin owner) tag checked actor later same |
    No distinct = void (distinct same)
countedFiredHeadSame nameEq keyEq (LAdvance owner) tag checked actor later same
  with (decEq @{nameEq} owner actor)
  countedFiredHeadSame nameEq keyEq (LAdvance _) tag checked _ later same |
    Yes Refl = Refl
  countedFiredHeadSame nameEq keyEq (LAdvance owner) tag checked actor later same |
    No distinct = void (distinct same)
countedFiredHeadSame nameEq keyEq (LDivert owner) tag checked actor later same
  with (decEq @{nameEq} owner actor)
  countedFiredHeadSame nameEq keyEq (LDivert _) tag checked _ later same |
    Yes Refl = Refl
  countedFiredHeadSame nameEq keyEq (LDivert owner) tag checked actor later same |
    No distinct = void (distinct same)
countedFiredHeadSame nameEq keyEq (LLeave owner) tag checked actor later same
  with (decEq @{nameEq} owner actor)
  countedFiredHeadSame nameEq keyEq (LLeave _) tag checked _ later same |
    Yes Refl = Refl
  countedFiredHeadSame nameEq keyEq (LLeave owner) tag checked actor later same |
    No distinct = void (distinct same)
countedFiredHeadSame nameEq keyEq (LUnload owner) tag checked actor later same
  with (decEq @{nameEq} owner actor)
  countedFiredHeadSame nameEq keyEq (LUnload _) tag checked _ later same |
    Yes Refl = Refl
  countedFiredHeadSame nameEq keyEq (LUnload owner) tag checked actor later same |
    No distinct = void (distinct same)

0 countedFiredHeadDifferent :
  {first, middle : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action first =
    Just (tag, middle)) ->
  (actor : name) -> (later : Nat) -> Not (actionOwner action = actor) ->
  (case decEq @{nameEq}
    (transitionActor (Fired {before = first} {afterState = middle}
      nameEq keyEq action tag checked)) actor of
    Yes Refl => S later
    No distinct => later) = later
countedFiredHeadDifferent nameEq keyEq (OInsert owner parent component) tag
  checked actor later different with (decEq @{nameEq} owner actor)
  countedFiredHeadDifferent nameEq keyEq (OInsert _ parent component) tag checked
    _ later different | Yes same = void (different same)
  countedFiredHeadDifferent nameEq keyEq (OInsert owner parent component) tag
    checked actor later different | No distinct = Refl
countedFiredHeadDifferent nameEq keyEq (ORetire owner) tag checked actor later
  different with (decEq @{nameEq} owner actor)
  countedFiredHeadDifferent nameEq keyEq (ORetire _) tag checked _ later
    different | Yes same = void (different same)
  countedFiredHeadDifferent nameEq keyEq (ORetire owner) tag checked actor later
    different | No distinct = Refl
countedFiredHeadDifferent nameEq keyEq (ORemove owner) tag checked actor later
  different with (decEq @{nameEq} owner actor)
  countedFiredHeadDifferent nameEq keyEq (ORemove _) tag checked _ later
    different | Yes same = void (different same)
  countedFiredHeadDifferent nameEq keyEq (ORemove owner) tag checked actor later
    different | No distinct = Refl
countedFiredHeadDifferent nameEq keyEq (LBegin owner) tag checked actor later
  different with (decEq @{nameEq} owner actor)
  countedFiredHeadDifferent nameEq keyEq (LBegin _) tag checked _ later different |
    Yes same = void (different same)
  countedFiredHeadDifferent nameEq keyEq (LBegin owner) tag checked actor later
    different | No distinct = Refl
countedFiredHeadDifferent nameEq keyEq (LAdvance owner) tag checked actor later
  different with (decEq @{nameEq} owner actor)
  countedFiredHeadDifferent nameEq keyEq (LAdvance _) tag checked _ later
    different | Yes same = void (different same)
  countedFiredHeadDifferent nameEq keyEq (LAdvance owner) tag checked actor later
    different | No distinct = Refl
countedFiredHeadDifferent nameEq keyEq (LDivert owner) tag checked actor later
  different with (decEq @{nameEq} owner actor)
  countedFiredHeadDifferent nameEq keyEq (LDivert _) tag checked _ later different |
    Yes same = void (different same)
  countedFiredHeadDifferent nameEq keyEq (LDivert owner) tag checked actor later
    different | No distinct = Refl
countedFiredHeadDifferent nameEq keyEq (LLeave owner) tag checked actor later
  different with (decEq @{nameEq} owner actor)
  countedFiredHeadDifferent nameEq keyEq (LLeave _) tag checked _ later different |
    Yes same = void (different same)
  countedFiredHeadDifferent nameEq keyEq (LLeave owner) tag checked actor later
    different | No distinct = Refl
countedFiredHeadDifferent nameEq keyEq (LUnload owner) tag checked actor later
  different with (decEq @{nameEq} owner actor)
  countedFiredHeadDifferent nameEq keyEq (LUnload _) tag checked _ later different |
    Yes same = void (different same)
  countedFiredHeadDifferent nameEq keyEq (LUnload owner) tag checked actor later
    different | No distinct = Refl

0 firedOwner :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action first =
    Just (tag, middle)) ->
  transitionActor (Fired {before = first} {afterState = middle}
    nameEq keyEq action tag checked) = actionOwner action
firedOwner nameEq keyEq (OInsert owner parent component) tag checked = Refl
firedOwner nameEq keyEq (ORetire owner) tag checked = Refl
firedOwner nameEq keyEq (ORemove owner) tag checked = Refl
firedOwner nameEq keyEq (LBegin owner) tag checked = Refl
firedOwner nameEq keyEq (LAdvance owner) tag checked = Refl
firedOwner nameEq keyEq (LDivert owner) tag checked = Refl
firedOwner nameEq keyEq (LLeave owner) tag checked = Refl
firedOwner nameEq keyEq (LUnload owner) tag checked = Refl

0 stepsTransitionSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, last : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (transition : Transition first middle) ->
  (rest : Transitions middle last) ->
  transitionActor transition = actor ->
  stepsActingOn @{nameEq} actor (MoreTransitions transition rest) =
    S (stepsActingOn @{nameEq} actor rest)
stepsTransitionSame nameEq actor transition rest same with
  (decEq @{nameEq} (transitionActor transition) actor)
  stepsTransitionSame nameEq _ transition rest same | Yes Refl = Refl
  stepsTransitionSame nameEq actor transition rest same | No distinct =
    void (distinct same)

0 stepsTransitionDifferent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, last : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (transition : Transition first middle) ->
  (rest : Transitions middle last) ->
  Not (transitionActor transition = actor) ->
  stepsActingOn @{nameEq} actor (MoreTransitions transition rest) =
    stepsActingOn @{nameEq} actor rest
stepsTransitionDifferent nameEq actor transition rest distinct with
  (decEq @{nameEq} (transitionActor transition) actor)
  stepsTransitionDifferent nameEq _ transition rest distinct | Yes same =
    void (distinct same)
  stepsTransitionDifferent nameEq actor transition rest distinct | No notSame =
    Refl

0 stepsFiredSame :
  {first, middle, last : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action first =
    Just (tag, middle)) -> (actor : name) ->
  (rest : Transitions middle last) -> actionOwner action = actor ->
  stepsActingOn @{nameEq} actor
    (MoreTransitions (Fired {before = first} {afterState = middle}
      nameEq keyEq action tag checked) rest) =
    S (stepsActingOn @{nameEq} actor rest)
stepsFiredSame nameEq keyEq (OInsert owner parent component) tag checked actor rest same with
  (decEq @{nameEq} owner actor)
  stepsFiredSame nameEq keyEq (OInsert _ parent component) tag checked _ rest same | Yes Refl = Refl
  stepsFiredSame nameEq keyEq (OInsert owner parent component) tag checked actor rest same | No distinct =
    void (distinct same)
stepsFiredSame nameEq keyEq (ORetire owner) tag checked actor rest same with
  (decEq @{nameEq} owner actor)
  stepsFiredSame nameEq keyEq (ORetire _) tag checked _ rest same | Yes Refl = Refl
  stepsFiredSame nameEq keyEq (ORetire owner) tag checked actor rest same | No distinct =
    void (distinct same)
stepsFiredSame nameEq keyEq (ORemove owner) tag checked actor rest same with
  (decEq @{nameEq} owner actor)
  stepsFiredSame nameEq keyEq (ORemove _) tag checked _ rest same | Yes Refl = Refl
  stepsFiredSame nameEq keyEq (ORemove owner) tag checked actor rest same | No distinct =
    void (distinct same)
stepsFiredSame nameEq keyEq (LBegin owner) tag checked actor rest same with
  (decEq @{nameEq} owner actor)
  stepsFiredSame nameEq keyEq (LBegin _) tag checked _ rest same | Yes Refl = Refl
  stepsFiredSame nameEq keyEq (LBegin owner) tag checked actor rest same | No distinct =
    void (distinct same)
stepsFiredSame nameEq keyEq (LAdvance owner) tag checked actor rest same with
  (decEq @{nameEq} owner actor)
  stepsFiredSame nameEq keyEq (LAdvance _) tag checked _ rest same | Yes Refl = Refl
  stepsFiredSame nameEq keyEq (LAdvance owner) tag checked actor rest same | No distinct =
    void (distinct same)
stepsFiredSame nameEq keyEq (LDivert owner) tag checked actor rest same with
  (decEq @{nameEq} owner actor)
  stepsFiredSame nameEq keyEq (LDivert _) tag checked _ rest same | Yes Refl = Refl
  stepsFiredSame nameEq keyEq (LDivert owner) tag checked actor rest same | No distinct =
    void (distinct same)
stepsFiredSame nameEq keyEq (LLeave owner) tag checked actor rest same with
  (decEq @{nameEq} owner actor)
  stepsFiredSame nameEq keyEq (LLeave _) tag checked _ rest same | Yes Refl = Refl
  stepsFiredSame nameEq keyEq (LLeave owner) tag checked actor rest same | No distinct =
    void (distinct same)
stepsFiredSame nameEq keyEq (LUnload owner) tag checked actor rest same with
  (decEq @{nameEq} owner actor)
  stepsFiredSame nameEq keyEq (LUnload _) tag checked _ rest same | Yes Refl = Refl
  stepsFiredSame nameEq keyEq (LUnload owner) tag checked actor rest same | No distinct =
    void (distinct same)

0 stepsFiredDifferent :
  {first, middle, last : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action first =
    Just (tag, middle)) -> (actor : name) ->
  (rest : Transitions middle last) -> Not (actionOwner action = actor) ->
  stepsActingOn @{nameEq} actor
    (MoreTransitions (Fired {before = first} {afterState = middle}
      nameEq keyEq action tag checked) rest) =
    stepsActingOn @{nameEq} actor rest
stepsFiredDifferent nameEq keyEq (OInsert owner parent component) tag checked actor rest different with
  (decEq @{nameEq} owner actor)
  stepsFiredDifferent nameEq keyEq (OInsert _ parent component) tag checked _ rest different | Yes same =
    void (different same)
  stepsFiredDifferent nameEq keyEq (OInsert owner parent component) tag checked actor rest different |
    No distinct = Refl
stepsFiredDifferent nameEq keyEq (ORetire owner) tag checked actor rest different with
  (decEq @{nameEq} owner actor)
  stepsFiredDifferent nameEq keyEq (ORetire _) tag checked _ rest different | Yes same =
    void (different same)
  stepsFiredDifferent nameEq keyEq (ORetire owner) tag checked actor rest different |
    No distinct = Refl
stepsFiredDifferent nameEq keyEq (ORemove owner) tag checked actor rest different with
  (decEq @{nameEq} owner actor)
  stepsFiredDifferent nameEq keyEq (ORemove _) tag checked _ rest different | Yes same =
    void (different same)
  stepsFiredDifferent nameEq keyEq (ORemove owner) tag checked actor rest different |
    No distinct = Refl
stepsFiredDifferent nameEq keyEq (LBegin owner) tag checked actor rest different with
  (decEq @{nameEq} owner actor)
  stepsFiredDifferent nameEq keyEq (LBegin _) tag checked _ rest different | Yes same =
    void (different same)
  stepsFiredDifferent nameEq keyEq (LBegin owner) tag checked actor rest different |
    No distinct = Refl
stepsFiredDifferent nameEq keyEq (LAdvance owner) tag checked actor rest different with
  (decEq @{nameEq} owner actor)
  stepsFiredDifferent nameEq keyEq (LAdvance _) tag checked _ rest different | Yes same =
    void (different same)
  stepsFiredDifferent nameEq keyEq (LAdvance owner) tag checked actor rest different |
    No distinct = Refl
stepsFiredDifferent nameEq keyEq (LDivert owner) tag checked actor rest different with
  (decEq @{nameEq} owner actor)
  stepsFiredDifferent nameEq keyEq (LDivert _) tag checked _ rest different | Yes same =
    void (different same)
  stepsFiredDifferent nameEq keyEq (LDivert owner) tag checked actor rest different |
    No distinct = Refl
stepsFiredDifferent nameEq keyEq (LLeave owner) tag checked actor rest different with
  (decEq @{nameEq} owner actor)
  stepsFiredDifferent nameEq keyEq (LLeave _) tag checked _ rest different | Yes same =
    void (different same)
  stepsFiredDifferent nameEq keyEq (LLeave owner) tag checked actor rest different |
    No distinct = Refl
stepsFiredDifferent nameEq keyEq (LUnload owner) tag checked actor rest different with
  (decEq @{nameEq} owner actor)
  stepsFiredDifferent nameEq keyEq (LUnload _) tag checked _ rest different | Yes same =
    void (different same)
  stepsFiredDifferent nameEq keyEq (LUnload owner) tag checked actor rest different |
    No distinct = Refl

||| Strong amortized form of Equation 61: the initial potential pays the first
||| target interval, and every target change contributes one fresh `K + 4`.
public export
0 actorTracePotentialBudget :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (bound : Nat) ->
  (actor : name) ->
  (trace : Transitions first last) ->
  LifecycleOnly trace ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  programsBoundedBy bound first = True ->
  continuationsBoundedBy bound first = True ->
  (turns : Nat) ->
  TargetTurnCount name key world error value nameEq keyEq actor trace turns ->
  LTE (stepsActingOn @{nameEq} actor trace)
    (actorTargetPotential @{nameEq} @{keyEq} bound actor first +
      (bound + 4) * turns)
actorTracePotentialBudget nameEq keyEq bound actor NoTransitions
  LifecycleOnlyEnd AlignedEnd programs continuations Z NoTargetTurns = LTEZero
actorTracePotentialBudget nameEq keyEq bound actor
  (MoreTransitions transition@(Fired {before = first} {afterState = middle}
    nameEq keyEq action tag checked) rest)
  (LifecycleOnlyStep _ rest lifecycle lifecycleRest)
  (AlignedStep action tag checked rest alignedRest)
  programs continuations turns count =
    let raw = checkedActionProjects nameEq keyEq action _ _ tag checked
        programsMiddle = lifecycleTransitionPreservesProgramsBoundedBy nameEq keyEq
          bound action tag _ _ checked lifecycle programs
        continuationsMiddle = transitionPreservesContinuationsBoundedBy nameEq keyEq
          bound action tag _ _ checked programs continuations
    in case count of
      TargetStayed _ rest stayed tailCount =>
        let tailBudget = actorTracePotentialBudget nameEq keyEq bound actor rest
              lifecycleRest alignedRest programsMiddle continuationsMiddle turns
              tailCount
        in case decEq @{nameEq} (actionOwner action) actor of
          Yes same =>
            let actorStep = lifecycleActorPotentialStep nameEq keyEq bound action
                  tag _ _ raw lifecycle programs
                stayedForOwner = replace
                  {p = \selected => sameTarget @{nameEq}
                    (targetProvidersAt @{nameEq} @{keyEq} selected first)
                    (targetProvidersAt @{nameEq} @{keyEq} selected middle) = True}
                  (sym same) stayed
                dropsOwner = stayedPotentialDrops actorStep stayedForOwner
                drops = replace
                  {p = \selected => LTE
                    (S (actorTargetPotential @{nameEq} @{keyEq} bound selected middle))
                    (actorTargetPotential @{nameEq} @{keyEq} bound selected first)}
                  same dropsOwner
                headCount = stepsFiredSame nameEq keyEq action tag checked actor rest same
            in replace
              {p = \steps => LTE steps
                (actorTargetPotential @{nameEq} @{keyEq} bound actor first +
                  (bound + 4) * turns)}
              (sym headCount) (stayedOwnerBudget tailBudget drops)
          No distinct =>
            let samePotential = foreignActorTargetPotentialEqual nameEq keyEq bound
                  actor action tag _ _ (\equal => distinct (sym equal)) checked stayed
                headCount = stepsFiredDifferent nameEq keyEq action tag checked actor rest
                  distinct
                rhsEqual = cong
                  (\potential => potential + (bound + 4) * turns)
                  (sym samePotential)
                tailAtFirst = replace
                  {p = \rhs => LTE (stepsActingOn @{nameEq} actor rest) rhs}
                  rhsEqual tailBudget
            in replace
              {p = \steps => LTE steps
                (actorTargetPotential @{nameEq} @{keyEq} bound actor first +
                  (bound + 4) * turns)}
              (sym headCount) tailAtFirst
      TargetChanged {turns = tailTurns} _ rest changed tailCount =>
        let tailBudget = actorTracePotentialBudget nameEq keyEq bound actor rest
              lifecycleRest alignedRest programsMiddle continuationsMiddle _ tailCount
            middleBound = actorTargetPotentialBounded nameEq keyEq bound actor _
              continuationsMiddle
        in case decEq @{nameEq} (actionOwner action) actor of
          Yes same =>
            let actorStep = lifecycleActorPotentialStep nameEq keyEq bound action
                  tag _ _ raw lifecycle programs
                positive = replace
                  {p = \selected => LTE 1
                    (actorTargetPotential @{nameEq} @{keyEq} bound selected first)}
                  same (sourcePotentialPositive actorStep)
                charged = changedOwnerBudget tailBudget middleBound positive
                headCount = stepsFiredSame nameEq keyEq action tag checked actor rest same
                counted = replace
                  {p = \steps => LTE steps
                    (actorTargetPotential @{nameEq} @{keyEq} bound actor first +
                      ((bound + 4) + (bound + 4) * tailTurns))}
                  (sym headCount) charged
                rhsEqual = cong
                  (\budget => actorTargetPotential @{nameEq} @{keyEq} bound actor
                    first + budget)
                  (sym (multRightSuccPlus (bound + 4) tailTurns))
            in replace
              {p = \rhs => LTE
                (stepsActingOn @{nameEq} actor
                  (MoreTransitions (Fired {before = first} {afterState = middle}
                    nameEq keyEq action tag checked) rest)) rhs}
              rhsEqual counted
          No distinct =>
            let charged = changedForeignBudget tailBudget middleBound
                headCount = stepsFiredDifferent nameEq keyEq action tag checked actor rest
                  distinct
                counted = replace
                  {p = \steps => LTE steps
                    (actorTargetPotential @{nameEq} @{keyEq} bound actor first +
                      ((bound + 4) + (bound + 4) * tailTurns))}
                  (sym headCount) charged
                rhsEqual = cong
                  (\budget => actorTargetPotential @{nameEq} @{keyEq} bound actor
                    first + budget)
                  (sym (multRightSuccPlus (bound + 4) tailTurns))
            in replace
              {p = \rhs => LTE
                (stepsActingOn @{nameEq} actor
                  (MoreTransitions (Fired {before = first} {afterState = middle}
                    nameEq keyEq action tag checked) rest)) rhs}
              rhsEqual counted

0 plusRightOneSucc : (number : Nat) -> number + 1 = S number
plusRightOneSucc number = trans (plusCommutative number 1) (plusOneSucc number)

||| Public Equation-61 count, obtained by bounding the initial potential by one
||| interval and normalizing `turns + 1` to a successor.
public export
0 actorTraceEquation61 :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (bound : Nat) ->
  (actor : name) ->
  (trace : Transitions first last) ->
  LifecycleOnly trace ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  programsBoundedBy bound first = True ->
  continuationsBoundedBy bound first = True ->
  (turns : Nat) ->
  TargetTurnCount name key world error value nameEq keyEq actor trace turns ->
  LTE (stepsActingOn @{nameEq} actor trace)
    ((bound + 4) * (turns + 1))
actorTraceEquation61 nameEq keyEq bound actor trace lifecycle aligned programs
  continuations turns count =
    let budget = actorTracePotentialBudget nameEq keyEq bound actor trace lifecycle
          aligned programs continuations turns count
        initialBound = actorTargetPotentialBounded nameEq keyEq bound actor _
          continuations
        interval = plusLteMonotoneRight ((bound + 4) * turns)
          (actorTargetPotential @{nameEq} @{keyEq} bound actor _)
          (bound + 4) initialBound
        combined = lteTransitive budget interval
    in rewrite plusRightOneSucc turns in
       rewrite multRightSuccPlus (bound + 4) turns in combined
