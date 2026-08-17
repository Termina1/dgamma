module DGamma.CP4ProgressReliance

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressFinite
import Control.WellFounded
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

||| A positional witness that one committed dependency was resolved to a given
||| provider. Keeping the position avoids assuming dependency keys are unique.
public export
data ViewProviderOccurrence :
  (provider : name) -> (deps : List key) -> View name deps -> Type where
  ProviderOccursHere :
    ViewProviderOccurrence provider (wanted :: rest)
      (ProviderView provider viewTail)
  ProviderOccursLater :
    ViewProviderOccurrence provider rest viewTail ->
    ViewProviderOccurrence provider (wanted :: rest)
      (ProviderView current viewTail)

0 viewContainsOccurrence :
  (nameEq : DecEq name) -> (provider : name) ->
  (view : View name deps) -> viewContains @{nameEq} provider view = True ->
  ViewProviderOccurrence provider deps view
viewContainsOccurrence nameEq provider EmptyView contains = case contains of
  Refl impossible
viewContainsOccurrence nameEq provider (ProviderView current tail) contains
  with (decEq @{nameEq} provider current)
  viewContainsOccurrence nameEq current (ProviderView current tail) contains |
    Yes Refl = ProviderOccursHere
  viewContainsOccurrence nameEq provider (ProviderView current tail) contains |
    No distinct = ProviderOccursLater
      (viewContainsOccurrence nameEq provider tail contains)

public export
record CommittedProviderUse
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (provider : name) (fibers : Registry name key value world error)
  (deps : List key) (view : View name deps) where
  constructor MkCommittedProviderUse
  usedKey : key
  usedValue : value usedKey
  0 usedDependency : Elem usedKey deps
  0 usedProviderValue :
    valueFromProvider @{nameEq} @{keyEq} {value = value} {world = world}
      {error = error} provider usedKey fibers = Just usedValue

0 committedProviderUse :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider : name) -> (deps : List key) -> (view : View name deps) ->
  (fibers : Registry name key value world error) ->
  ViewProviderOccurrence provider deps view ->
  (capability : DepValues key value deps) ->
  resolveCommittedValues @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} deps view fibers = Just capability ->
  CommittedProviderUse name key world error value nameEq keyEq provider fibers
    deps view
committedProviderUse nameEq keyEq provider (wanted :: rest)
  (ProviderView provider tail) fibers ProviderOccursHere capability resolved
  with (valueFromProvider @{nameEq} @{keyEq} provider wanted fibers) proof found
  committedProviderUse nameEq keyEq provider (wanted :: rest)
    (ProviderView provider tail) fibers ProviderOccursHere capability resolved |
    Nothing = case resolved of Refl impossible
  committedProviderUse nameEq keyEq provider (wanted :: rest)
    (ProviderView provider tail) fibers ProviderOccursHere capability resolved |
    Just used = MkCommittedProviderUse wanted used Here found
committedProviderUse nameEq keyEq provider (wanted :: rest)
  (ProviderView current tail) fibers (ProviderOccursLater later) capability
  resolved
  with (valueFromProvider @{nameEq} @{keyEq} current wanted fibers)
  committedProviderUse nameEq keyEq provider (wanted :: rest)
    (ProviderView current tail) fibers (ProviderOccursLater later) capability
    resolved | Nothing = case resolved of Refl impossible
  committedProviderUse nameEq keyEq provider (wanted :: rest)
    (ProviderView current tail) fibers (ProviderOccursLater later) capability
    resolved | Just currentValue
    with (resolveCommittedValues @{nameEq} @{keyEq} rest tail fibers) proof tailRun
    committedProviderUse nameEq keyEq provider (wanted :: rest)
      (ProviderView current tail) fibers (ProviderOccursLater later) capability
      resolved | Just currentValue | Nothing = case resolved of Refl impossible
    committedProviderUse nameEq keyEq provider (wanted :: rest)
      (ProviderView current tail) fibers (ProviderOccursLater later)
      capability resolved | Just currentValue | Just tailCapability =
        let laterUse = committedProviderUse nameEq keyEq provider rest tail fibers
              later tailCapability tailRun
        in MkCommittedProviderUse (usedKey laterUse) (usedValue laterUse)
          (There (usedDependency laterUse)) (usedProviderValue laterUse)

0 lookupBindingJustElem :
  (keyEq : DecEq key) -> (wanted : key) ->
  (table : CoeffectContext key value) -> (found : value wanted) ->
  lookupBinding @{keyEq} wanted table = Just found ->
  Elem wanted (bindingKeys (bindings table))
lookupBindingJustElem keyEq wanted (MkCoeffectContext entries unique) found
  present = lookupJustElem wanted entries found present

0 valueFromProviderAtFound :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider : name) -> (wanted : key) ->
  (fibers : Registry name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} provider fibers = Just fiber ->
  valueFromProvider @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} provider wanted fibers =
    lookupBinding @{keyEq} wanted (ownedValues (fiberTable fiber))
valueFromProviderAtFound nameEq keyEq provider wanted fibers fiber found =
  rewrite found in Refl

0 bindingElemKey :
  Elem (Bind selected observed) entries -> Elem selected (bindingKeys entries)
bindingElemKey Here = Here
bindingElemKey (There later) = There (bindingElemKey later)

0 lookupEntryFromElem :
  (keyEq : DecEq key) ->
  (entries : List (Binding key value)) ->
  (unique : UniqueKeys (bindingKeys entries)) ->
  Elem (Bind selected observed) entries ->
  lookupEntries @{keyEq} selected entries = Just observed
lookupEntryFromElem keyEq (Bind selected observed :: rest)
  (UniqueCons fresh tailUnique) Here
  with (decEq @{keyEq} selected selected)
  lookupEntryFromElem keyEq (Bind selected observed :: rest)
    (UniqueCons fresh tailUnique) Here | Yes Refl = Refl
  lookupEntryFromElem keyEq (Bind selected observed :: rest)
    (UniqueCons fresh tailUnique) Here | No contra = void (contra Refl)
lookupEntryFromElem keyEq (Bind current currentValue :: rest)
  (UniqueCons fresh tailUnique) (There later)
  with (decEq @{keyEq} selected current)
  lookupEntryFromElem keyEq (Bind current currentValue :: rest)
    (UniqueCons fresh tailUnique) (There later) | Yes same =
      void (fresh (replace
        {p = \candidate => Elem candidate (bindingKeys rest)} same
        (bindingElemKey later)))
  lookupEntryFromElem keyEq (Bind current currentValue :: rest)
    (UniqueCons fresh tailUnique) (There later) | No distinct =
      lookupEntryFromElem keyEq rest tailUnique later

record ReliedEntry
  (name, key, world, error : Type) (value : key -> Type)
  (provider : name)
  (entries : List (Binding name (FiberAt name key value world error))) where
  constructor MkReliedEntry
  reliedConsumerName : name
  reliedConsumerFiber : Fiber name key value world error
  0 reliedConsumerMember :
    Elem (Bind reliedConsumerName reliedConsumerFiber) entries
  0 reliedConsumerDistinct : Not (reliedConsumerName = provider)
  reliedConsumerView : View name (dependencies
    (componentDependencies (fiberComponent reliedConsumerFiber)))
  0 reliedConsumerCommitted :
    committed (fiberLifecycle reliedConsumerFiber) = Just reliedConsumerView
  0 reliedProviderOccurrence : ViewProviderOccurrence provider
    (dependencies (componentDependencies (fiberComponent reliedConsumerFiber)))
    reliedConsumerView

0 reliedHeadEntry :
  (nameEq : DecEq name) -> (provider, consumer : name) ->
  (fiber : Fiber name key value world error) ->
  reliedHead @{nameEq} provider provider (Bind consumer fiber) = True ->
  ReliedEntry name key world error value provider [Bind consumer fiber]
reliedHeadEntry nameEq provider consumer
  (MkFiber component parent retiredFlag table (Inactive outcome)) headTrue
  with (decEq @{nameEq} consumer provider)
  reliedHeadEntry nameEq provider provider
    (MkFiber component parent retiredFlag table (Inactive outcome)) headTrue |
    Yes Refl = case headTrue of Refl impossible
  reliedHeadEntry nameEq provider consumer
    (MkFiber component parent retiredFlag table (Inactive outcome)) headTrue |
    No distinct = case headTrue of Refl impossible
reliedHeadEntry nameEq provider consumer
  (MkFiber component parent retiredFlag table
    (Reloading remaining accumulator view)) headTrue
  with (decEq @{nameEq} consumer provider)
  reliedHeadEntry nameEq provider provider
    (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator view)) headTrue | Yes Refl =
        case headTrue of Refl impossible
  reliedHeadEntry nameEq provider consumer
    (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator view)) headTrue | No distinct =
        MkReliedEntry consumer
          (MkFiber component parent retiredFlag table
            (Reloading remaining accumulator view)) Here distinct view Refl
          (viewContainsOccurrence nameEq provider view headTrue)
reliedHeadEntry nameEq provider consumer
  (MkFiber component parent retiredFlag table (Active accumulator view)) headTrue
  with (decEq @{nameEq} consumer provider)
  reliedHeadEntry nameEq provider provider
    (MkFiber component parent retiredFlag table (Active accumulator view))
    headTrue | Yes Refl = case headTrue of Refl impossible
  reliedHeadEntry nameEq provider consumer
    (MkFiber component parent retiredFlag table (Active accumulator view))
    headTrue | No distinct =
      MkReliedEntry consumer
        (MkFiber component parent retiredFlag table (Active accumulator view))
        Here distinct view Refl
        (viewContainsOccurrence nameEq provider view headTrue)
reliedHeadEntry nameEq provider consumer
  (MkFiber component parent retiredFlag table
    (Unloading accumulator view outcome)) headTrue
  with (decEq @{nameEq} consumer provider)
  reliedHeadEntry nameEq provider provider
    (MkFiber component parent retiredFlag table
      (Unloading accumulator view outcome)) headTrue | Yes Refl =
        case headTrue of Refl impossible
  reliedHeadEntry nameEq provider consumer
    (MkFiber component parent retiredFlag table
      (Unloading accumulator view outcome)) headTrue | No distinct =
        MkReliedEntry consumer
          (MkFiber component parent retiredFlag table
            (Unloading accumulator view outcome)) Here distinct view Refl
          (viewContainsOccurrence nameEq provider view headTrue)

0 reliedOnByEntry :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (provider : name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  reliedOnBy @{nameEq} {key = key} {value = value} {world = world}
    {error = error} provider provider entries = True ->
  ReliedEntry name key world error value provider entries
reliedOnByEntry nameEq provider [] reliedTrue = case reliedTrue of
  Refl impossible
reliedOnByEntry nameEq provider (Bind consumer fiber :: rest) reliedTrue
  with (reliedHead @{nameEq} provider provider (Bind consumer fiber)) proof head
  reliedOnByEntry nameEq provider (Bind consumer fiber :: rest) reliedTrue |
    True = case reliedHeadEntry nameEq provider consumer fiber head of
      MkReliedEntry consumer fiber Here distinct view committed occurrence =>
        MkReliedEntry consumer fiber Here distinct view committed occurrence
  reliedOnByEntry nameEq provider (Bind consumer fiber :: rest) reliedTrue |
    False =
      let later = reliedOnByEntry nameEq provider rest reliedTrue
      in MkReliedEntry (reliedConsumerName later) (reliedConsumerFiber later)
        (There (reliedConsumerMember later)) (reliedConsumerDistinct later)
        (reliedConsumerView later) (reliedConsumerCommitted later)
        (reliedProviderOccurrence later)

public export
record ReliedConsumer
  (nameEq : DecEq name) (provider : name)
  (state : SystemState name key value world error) where
  constructor MkReliedConsumer
  consumerName : name
  consumerFiber : Fiber name key value world error
  0 consumerFound : lookupFiber @{nameEq} consumerName (registry state) =
    Just consumerFiber
  0 consumerDistinct : Not (consumerName = provider)
  consumerView : View name (dependencies
    (componentDependencies (fiberComponent consumerFiber)))
  0 consumerCommitted :
    committed (fiberLifecycle consumerFiber) = Just consumerView
  0 providerOccurrence : ViewProviderOccurrence provider
    (dependencies (componentDependencies (fiberComponent consumerFiber)))
    consumerView
  0 providerPrecedesConsumer :
    PrecedenceEdge nameEq provider consumerName state

||| Reflection of the unloading guard into the exact precedence edge consumed
||| by the well-founded descent.
public export
0 reliedConsumerWitness :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} state = True ->
  (provider : name) -> (providerFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} provider (registry state) = Just providerFiber ->
  relied @{nameEq} {key = key} {value = value} {world = world}
    {error = error} provider (registry state) = True ->
  ReliedConsumer nameEq provider state
reliedConsumerWitness nameEq keyEq
  (MkSystemState ambient (MkCoeffectContext entries unique)) wellFormed
  provider providerFiber providerFound reliedTrue =
    let entry = reliedOnByEntry nameEq provider entries reliedTrue
        consumer : name
        consumer = reliedConsumerName entry
        fiber : Fiber name key value world error
        fiber = reliedConsumerFiber entry
        0 found : lookupFiber @{nameEq} consumer
          (MkCoeffectContext entries unique) = Just fiber
        found = lookupEntryFromElem nameEq entries unique
          (reliedConsumerMember entry)
        0 allViews : viewsInvariant @{nameEq} @{keyEq} {value = value}
          {world = world} {error = error} entries
          (MkCoeffectContext entries unique) = True
        allViews = wellFormedViewsInvariant nameEq keyEq ambient
          (MkCoeffectContext entries unique) wellFormed
        0 selectedView : fiberViewInvariant @{nameEq} @{keyEq} {value = value}
          {world = world} {error = error} fiber
          (MkCoeffectContext entries unique) = True
        selectedView = viewsInvariantLookup nameEq keyEq consumer fiber entries
          (MkCoeffectContext entries unique) found allViews
        0 bindingsValid : viewBindingsInvariant @{nameEq} @{keyEq}
          {value = value} {world = world} {error = error}
          (dependencies (componentDependencies (fiberComponent fiber)))
          (reliedConsumerView entry) (MkCoeffectContext entries unique) = True
        bindingsValid = committedViewBindingsValid nameEq keyEq fiber
          (MkCoeffectContext entries unique) (reliedConsumerView entry) selectedView
          (reliedConsumerCommitted entry)
        0 resolvedIsJust : isJust (resolveCommittedValues @{nameEq} @{keyEq}
          {value = value} {world = world} {error = error}
          (dependencies (componentDependencies (fiberComponent fiber)))
          (reliedConsumerView entry) (MkCoeffectContext entries unique)) = True
        resolvedIsJust = boolAndRight _ _ bindingsValid
        0 resolvedWitness :
          (capability : DepValues key value
            (dependencies
              (componentDependencies (fiberComponent fiber))) **
           resolveCommittedValues @{nameEq} @{keyEq} {value = value}
             {world = world} {error = error}
             (dependencies
               (componentDependencies (fiberComponent fiber)))
             (reliedConsumerView entry) (MkCoeffectContext entries unique) =
               Just capability)
        resolvedWitness = isJustTrueWitness
          (resolveCommittedValues @{nameEq} @{keyEq} {value = value}
            {world = world} {error = error}
            (dependencies (componentDependencies (fiberComponent fiber)))
            (reliedConsumerView entry) (MkCoeffectContext entries unique))
            resolvedIsJust
    in case resolvedWitness of
      (capability ** resolved) =>
        let 0 providerFoundBinding :
              (lookupBinding @{nameEq} provider
                (MkCoeffectContext entries unique) = Just providerFiber)
            providerFoundBinding = providerFound
            0 use : CommittedProviderUse name key world error value nameEq keyEq
              provider (MkCoeffectContext entries unique)
              (dependencies (componentDependencies (fiberComponent fiber)))
              (reliedConsumerView entry)
            use = committedProviderUse nameEq keyEq provider
              (dependencies (componentDependencies (fiberComponent fiber)))
              (reliedConsumerView entry) (MkCoeffectContext entries unique)
              (reliedProviderOccurrence entry) capability resolved
            0 providerLookupValue :
              (lookupBinding @{keyEq} (usedKey use)
                (ownedValues (fiberTable providerFiber)) = Just (usedValue use))
            providerLookupValue = trans
              (sym (valueFromProviderAtFound nameEq keyEq provider
                (usedKey use) (MkCoeffectContext entries unique) providerFiber
                providerFoundBinding))
              (usedProviderValue use)
            0 providerDeclares : Elem (usedKey use)
              (dependencies
                (componentProvisions (fiberComponent providerFiber)))
            providerDeclares = ownedSound (fiberTable providerFiber)
              (usedKey use)
              (lookupBindingJustElem keyEq (usedKey use)
                (ownedValues (fiberTable providerFiber))
                (usedValue use) providerLookupValue)
            0 edge : PrecedenceEdge nameEq provider consumer
              (the (SystemState name key value world error)
                (MkSystemState ambient (MkCoeffectContext entries unique)))
            edge = MkPrecedenceEdge (usedKey use) providerFiber fiber
              providerFound found providerDeclares (usedDependency use)
        in MkReliedConsumer consumer fiber found (reliedConsumerDistinct entry)
          (reliedConsumerView entry) (reliedConsumerCommitted entry)
          (reliedProviderOccurrence entry) edge

public export
0 viewEqTrueEqual :
  (nameEq : DecEq name) -> (left, right : View name deps) ->
  viewEq @{nameEq} left right = True -> left = right
viewEqTrueEqual nameEq EmptyView EmptyView valid = Refl
viewEqTrueEqual nameEq (ProviderView left leftRest)
  (ProviderView right rightRest) valid
  with (decEq @{nameEq} left right)
  viewEqTrueEqual nameEq (ProviderView right leftRest)
    (ProviderView right rightRest) valid | Yes Refl =
      cong (ProviderView right)
        (viewEqTrueEqual nameEq leftRest rightRest valid)
  viewEqTrueEqual nameEq (ProviderView left leftRest)
    (ProviderView right rightRest) valid | No distinct = case valid of
      Refl impossible

public export
0 resolveViewOccurrenceProvider :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider : name) -> (deps : List key) -> (view : View name deps) ->
  (fibers : Registry name key value world error) ->
  ViewProviderOccurrence provider deps view ->
  resolveView @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} deps fibers = Just view ->
  (wanted : key **
    (Elem wanted deps,
     providerOf @{nameEq} @{keyEq} {value = value} {world = world}
       {error = error} wanted fibers = Just provider))
resolveViewOccurrenceProvider nameEq keyEq provider (wanted :: rest)
  (ProviderView provider tail) fibers ProviderOccursHere resolved
  with (providerOf @{nameEq} @{keyEq} wanted fibers) proof providerFound
  resolveViewOccurrenceProvider nameEq keyEq provider (wanted :: rest)
    (ProviderView provider tail) fibers ProviderOccursHere resolved |
    Nothing = case resolved of Refl impossible
  resolveViewOccurrenceProvider nameEq keyEq provider (wanted :: rest)
    (ProviderView provider tail) fibers ProviderOccursHere resolved |
    Just selected
    with (resolveView @{nameEq} @{keyEq} rest fibers)
    resolveViewOccurrenceProvider nameEq keyEq provider (wanted :: rest)
      (ProviderView provider tail) fibers ProviderOccursHere resolved |
      Just selected | Nothing = case resolved of Refl impossible
    resolveViewOccurrenceProvider nameEq keyEq provider (wanted :: rest)
      (ProviderView provider tail) fibers ProviderOccursHere resolved |
      Just selected | Just resolvedTail = case justInjective resolved of
        Refl => (wanted ** (Here, providerFound))
resolveViewOccurrenceProvider nameEq keyEq provider (wanted :: rest)
  (ProviderView current tail) fibers (ProviderOccursLater later) resolved
  with (providerOf @{nameEq} @{keyEq} wanted fibers)
  resolveViewOccurrenceProvider nameEq keyEq provider (wanted :: rest)
    (ProviderView current tail) fibers (ProviderOccursLater later) resolved |
    Nothing = case resolved of Refl impossible
  resolveViewOccurrenceProvider nameEq keyEq provider (wanted :: rest)
    (ProviderView current tail) fibers (ProviderOccursLater later) resolved |
    Just selected
    with (resolveView @{nameEq} @{keyEq} rest fibers) proof tailResolved
    resolveViewOccurrenceProvider nameEq keyEq provider (wanted :: rest)
      (ProviderView current tail) fibers (ProviderOccursLater later) resolved |
      Just selected | Nothing = case resolved of Refl impossible
    resolveViewOccurrenceProvider nameEq keyEq provider (wanted :: rest)
      (ProviderView current tail) fibers (ProviderOccursLater later) resolved |
      Just selected | Just resolvedTail = case justInjective resolved of
        Refl =>
          let (laterKey ** (laterElem, laterProvider)) =
                resolveViewOccurrenceProvider nameEq keyEq provider rest tail
                  fibers later tailResolved
          in (laterKey ** (There laterElem, laterProvider))

||| An Active consumer committed to an Unloading provider necessarily has a
||| stale target, because current target resolution selects Active providers.
public export
0 activeConsumerTargetMismatch :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  (provider, consumer : name) ->
  (providerComponent : Component key value world error) ->
  (providerParent : Parent name) -> (providerRetired : Bool) ->
  (providerTable : OwnedTable key value
    (componentProvisions providerComponent)) ->
  (providerAccumulator : LocalState key value world
      (componentProvisions providerComponent) ->
    LocalState key value world (componentProvisions providerComponent)) ->
  (providerView : View name (dependencies
    (componentDependencies providerComponent))) ->
  (providerOutcome : Maybe error) ->
  lookupFiber @{nameEq} provider (registry state) = Just
    (MkFiber providerComponent providerParent providerRetired providerTable
      (Unloading providerAccumulator providerView providerOutcome)) ->
  (consumerComponent : Component key value world error) ->
  (consumerParent : Parent name) -> (consumerRetired : Bool) ->
  (consumerTable : OwnedTable key value
    (componentProvisions consumerComponent)) ->
  (consumerAccumulator : LocalState key value world
      (componentProvisions consumerComponent) ->
    LocalState key value world (componentProvisions consumerComponent)) ->
  (consumerView : View name (dependencies
    (componentDependencies consumerComponent))) ->
  lookupFiber @{nameEq} consumer (registry state) = Just
    (MkFiber consumerComponent consumerParent consumerRetired consumerTable
      (Active consumerAccumulator consumerView)) ->
  ViewProviderOccurrence provider
    (dependencies (componentDependencies consumerComponent)) consumerView ->
  targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
      (MkFiber consumerComponent consumerParent consumerRetired consumerTable
        (Active consumerAccumulator consumerView)) (registry state))
    consumerView = False
activeConsumerTargetMismatch nameEq keyEq state provider consumer
  providerComponent providerParent providerRetired providerTable
  providerAccumulator providerView providerOutcome providerFound
  consumerComponent consumerParent True consumerTable consumerAccumulator
  consumerView consumerFound occurrence = Refl
activeConsumerTargetMismatch nameEq keyEq state provider consumer
  providerComponent providerParent providerRetired providerTable
  providerAccumulator providerView providerOutcome providerFound
  consumerComponent consumerParent False consumerTable consumerAccumulator
  consumerView consumerFound occurrence
  with (resolveView @{nameEq} @{keyEq}
    (dependencies (componentDependencies consumerComponent)) (registry state))
    proof resolved
  activeConsumerTargetMismatch nameEq keyEq state provider consumer
    providerComponent providerParent providerRetired providerTable
    providerAccumulator providerView providerOutcome providerFound
    consumerComponent consumerParent False consumerTable consumerAccumulator
    consumerView consumerFound occurrence | Nothing = Refl
  activeConsumerTargetMismatch nameEq keyEq state provider consumer
    providerComponent providerParent providerRetired providerTable
    providerAccumulator providerView providerOutcome providerFound
    consumerComponent consumerParent False consumerTable consumerAccumulator
    consumerView consumerFound occurrence | Just target
    with (viewEq @{nameEq} target consumerView) proof same
    activeConsumerTargetMismatch nameEq keyEq state provider consumer
      providerComponent providerParent providerRetired providerTable
      providerAccumulator providerView providerOutcome providerFound
      consumerComponent consumerParent False consumerTable consumerAccumulator
      consumerView consumerFound occurrence | Just target | False = Refl
    activeConsumerTargetMismatch nameEq keyEq state provider consumer
      providerComponent providerParent providerRetired providerTable
      providerAccumulator providerView providerOutcome providerFound
      consumerComponent consumerParent False consumerTable consumerAccumulator
      consumerView consumerFound occurrence | Just target | True =
        let targetEqual = viewEqTrueEqual nameEq target consumerView same
            resolvedCommitted = trans resolved (cong Just targetEqual)
            (wanted ** (dependency, providerSelected)) =
              resolveViewOccurrenceProvider nameEq keyEq provider
                (dependencies (componentDependencies consumerComponent))
                consumerView (registry state) occurrence resolvedCommitted
            providerSound = providerOfSound nameEq keyEq wanted provider
              (registry state) providerSelected
            sameProviderFiber = justInjective
              (trans (sym providerFound) (providerOfLookup providerSound))
            0 impossibleActive : (False = True)
            impossibleActive = replace
              {p = \fiber => isActive (fiberLifecycle fiber) = True}
              (sym sameProviderFiber) (providerOfActive providerSound)
        in case impossibleActive of Refl impossible
