module DGamma.CP4ProgressPrecedence

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressProgramBound
import Data.List.Elem
import Decidable.Equality

%default total

0 lookupNotElemNothing : DecEq key => (wanted : key) ->
  (entries : List (Binding key value)) ->
  Not (Elem wanted (bindingKeys entries)) -> lookupEntries wanted entries = Nothing
lookupNotElemNothing wanted [] absent = Refl
lookupNotElemNothing wanted (Bind current value :: rest) absent
  with (decEq wanted current)
  lookupNotElemNothing current (Bind current value :: rest) absent | Yes Refl =
    void (absent Here)
  lookupNotElemNothing wanted (Bind current value :: rest) absent | No distinct =
    lookupNotElemNothing wanted rest (\later => absent (There later))

0 lookupDeleteSelf : DecEq key => (removed : key) ->
  (context : CoeffectContext key value) ->
  lookupBinding removed (deleteBinding removed context) = Nothing
lookupDeleteSelf removed (MkCoeffectContext entries unique) =
  lookupNotElemNothing removed (deleteEntries removed entries)
    (deletedKeyNotElem removed entries unique)

record ComponentPreimage
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (selected : name)
  (source, target : Registry name key value world error)
  (targetFiber : Fiber name key value world error) where
  constructor MkComponentPreimage
  sourceFiber : Fiber name key value world error
  sourceFound : lookupFiber @{nameEq} selected source = Just sourceFiber
  sameComponent : fiberComponent targetFiber = fiberComponent sourceFiber

0 componentPreimageUpdate :
  (nameEq : DecEq name) -> (actor, selected : name) ->
  (source, target : Registry name key value world error) ->
  RegistryLocalUpdate name key world error value nameEq actor source target ->
  (actorFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor source = Just actorFiber ->
  (targetFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected target = Just targetFiber ->
  ComponentPreimage name key world error value nameEq selected source target
    targetFiber
componentPreimageUpdate nameEq actor selected source target update actorFiber
  actorPresent targetFiber targetFound with (decEq @{nameEq} selected actor)
  componentPreimageUpdate nameEq actor actor source target update actorFiber
    actorPresent targetFiber targetFound | Yes Refl = case update of
      LocalInsert inserted absent =>
        void (nothingIsNotJust (trans (sym absent) actorPresent))
      LocalReplace next {oldFiber} {oldFound} {staticComponent} =>
        let targetSelf = lookupReplacedFiber actor oldFiber next source oldFound
            sameNext = justInjective (trans (sym targetSelf) targetFound)
        in MkComponentPreimage oldFiber oldFound
          (trans (cong fiberComponent (sym sameNext)) staticComponent)
      LocalDelete => void (nothingIsNotJust
        (trans (sym (lookupDeleteSelf actor source)) targetFound))
  componentPreimageUpdate nameEq actor selected source target update actorFiber
    actorPresent targetFiber targetFound | No distinct =
      let frame = registryLocalUpdateForeign nameEq selected actor distinct source
            update
          found = trans (sym frame) targetFound
      in MkComponentPreimage targetFiber found Refl

0 transportProvision :
  (targetFiber, sourceFiber : Fiber name key value world error) ->
  fiberComponent targetFiber = fiberComponent sourceFiber ->
  Elem wanted (dependencies
    (componentProvisions (fiberComponent targetFiber))) ->
  Elem wanted (dependencies
    (componentProvisions (fiberComponent sourceFiber)))
transportProvision targetFiber sourceFiber same declared =
  replace
    {p = \component => Elem wanted
      (dependencies (componentProvisions component))}
    same declared

0 transportDependency :
  (targetFiber, sourceFiber : Fiber name key value world error) ->
  fiberComponent targetFiber = fiberComponent sourceFiber ->
  Elem wanted (dependencies
    (componentDependencies (fiberComponent targetFiber))) ->
  Elem wanted (dependencies
    (componentDependencies (fiberComponent sourceFiber)))
transportDependency targetFiber sourceFiber same declared =
  replace
    {p = \component => Elem wanted
      (dependencies (componentDependencies component))}
    same declared

0 precedenceEdgeBackUpdate :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (sourceWorld, targetWorld : world) ->
  (source, target : Registry name key value world error) ->
  RegistryLocalUpdate name key world error value nameEq actor source target ->
  (actorFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor source = Just actorFiber ->
  {provider, consumer : name} ->
  PrecedenceEdge nameEq provider consumer (the (SystemState name key value world error) (MkSystemState targetWorld target)) ->
  PrecedenceEdge nameEq provider consumer (the (SystemState name key value world error) (MkSystemState sourceWorld source))
precedenceEdgeBackUpdate nameEq actor sourceWorld targetWorld source target update actorFiber actorPresent
  (MkPrecedenceEdge edgeKey providerFiber consumerFiber providerFound consumerFound
    providerDeclares consumerDeclares) =
  let providerBack = componentPreimageUpdate nameEq actor provider source target
        update actorFiber actorPresent providerFiber providerFound
      consumerBack = componentPreimageUpdate nameEq actor consumer source target
        update actorFiber actorPresent consumerFiber consumerFound
  in MkPrecedenceEdge edgeKey
    (sourceFiber providerBack) (sourceFiber consumerBack)
    (sourceFound providerBack) (sourceFound consumerBack)
    (transportProvision providerFiber (sourceFiber providerBack)
      (sameComponent providerBack) providerDeclares)
    (transportDependency consumerFiber (sourceFiber consumerBack)
      (sameComponent consumerBack) consumerDeclares)

0 precedencePathBackUpdate :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (sourceWorld, targetWorld : world) ->
  (source, target : Registry name key value world error) ->
  RegistryLocalUpdate name key world error value nameEq actor source target ->
  (actorFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor source = Just actorFiber ->
  {from, to : name} ->
  PrecedencePath nameEq (the (SystemState name key value world error) (MkSystemState targetWorld target)) from to ->
  PrecedencePath nameEq (the (SystemState name key value world error) (MkSystemState sourceWorld source)) from to
precedencePathBackUpdate nameEq actor sourceWorld targetWorld source target update actorFiber actorPresent
  (PrecedenceOne edge) = PrecedenceOne
    (precedenceEdgeBackUpdate nameEq actor sourceWorld targetWorld source target update actorFiber
      actorPresent edge)
precedencePathBackUpdate nameEq actor sourceWorld targetWorld source target update actorFiber actorPresent
  (PrecedenceMore edge rest) = PrecedenceMore
    (precedenceEdgeBackUpdate nameEq actor sourceWorld targetWorld source target update actorFiber
      actorPresent edge)
    (precedencePathBackUpdate nameEq actor sourceWorld targetWorld source target update actorFiber
      actorPresent rest)

0 precedencePathBackTransition :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  isLifecycleAction action = True ->
  PrecedencePath nameEq afterState from to ->
  PrecedencePath nameEq before from to
precedencePathBackTransition nameEq keyEq action tag
  (MkSystemState sourceWorld source) (MkSystemState targetWorld target)
  checked lifecycle path =
  let raw = checkedActionProjects nameEq keyEq action
        (the (SystemState name key value world error) (MkSystemState sourceWorld source)) (the (SystemState name key value world error) (MkSystemState targetWorld target))
        tag checked
      (actorFiber ** actorPresent) = lifecycleActorPresent nameEq keyEq action
        (the (SystemState name key value world error) (MkSystemState sourceWorld source)) (the (SystemState name key value world error) (MkSystemState targetWorld target))
        tag raw lifecycle
      update = applyActionLocalUpdate nameEq keyEq action
        (the (SystemState name key value world error) (MkSystemState sourceWorld source)) (the (SystemState name key value world error) (MkSystemState targetWorld target))
        tag raw
  in precedencePathBackUpdate nameEq (actionOwner action) sourceWorld targetWorld source target
    (systemRegistryUpdate update) actorFiber actorPresent path

public export
0 lifecycleTracePrecedencePathBack :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trace : Transitions first last) ->
  LifecycleOnly trace ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  PrecedencePath nameEq last from to -> PrecedencePath nameEq first from to
lifecycleTracePrecedencePathBack nameEq keyEq NoTransitions LifecycleOnlyEnd
  AlignedEnd path = path
lifecycleTracePrecedencePathBack nameEq keyEq
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
  (LifecycleOnlyStep (Fired nameEq keyEq action tag checked) rest lifecycle
    lifecycleRest)
  (AlignedStep action tag checked rest alignedRest) path =
    precedencePathBackTransition nameEq keyEq action tag _ _ checked lifecycle
      (lifecycleTracePrecedencePathBack nameEq keyEq rest lifecycleRest alignedRest
        path)

||| Lifecycle-only traces preserve the initial precedence-acyclicity premise.
public export
0 lifecycleTracePrecedenceAcyclic :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trace : Transitions first last) ->
  LifecycleOnly trace ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  PrecedenceAcyclic nameEq first -> PrecedenceAcyclic nameEq last
lifecycleTracePrecedenceAcyclic nameEq keyEq trace lifecycle aligned acyclic
  selected cycle = acyclic selected
    (lifecycleTracePrecedencePathBack nameEq keyEq trace lifecycle aligned cycle)
