module DGamma.CP4DeletionSelectedForeignLifecycleFrame

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedForeignControlCore
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

0 justInjectiveLifecycleFrame : Just left = Just right -> left = right
justInjectiveLifecycleFrame Refl = Refl

0 exactFiberControlsFromMaybe :
  FiberControlMaybeRelated (Just left) (Just right) ->
  FiberControlRelated left right
exactFiberControlsFromMaybe (SomeControlFibers controls) = controls

0 lookupHeadSelfLifecycleFrame :
  (nameEq : DecEq name) -> (actor : name) ->
  (fiber : Fiber name key value world error) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  lookupEntries @{nameEq} actor (Bind actor fiber :: rest) = Just fiber
lookupHeadSelfLifecycleFrame nameEq actor fiber rest
  with (decEq @{nameEq} actor actor)
  lookupHeadSelfLifecycleFrame nameEq actor fiber rest | Yes Refl = Refl
  lookupHeadSelfLifecycleFrame nameEq actor fiber rest | No contra =
    void (contra Refl)

0 lookupHeadOtherLifecycleFrame :
  (nameEq : DecEq name) -> (wanted, current : name) ->
  Not (wanted = current) ->
  (fiber : Fiber name key value world error) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  lookupEntries @{nameEq} wanted (Bind current fiber :: rest) =
    lookupEntries @{nameEq} wanted rest
lookupHeadOtherLifecycleFrame nameEq wanted current distinct fiber rest
  with (decEq @{nameEq} wanted current)
  lookupHeadOtherLifecycleFrame nameEq current current distinct fiber rest |
    Yes Refl = void (distinct Refl)
  lookupHeadOtherLifecycleFrame nameEq wanted current distinct fiber rest |
    No _ = Refl

0 boolOrFalseLeft : (left, right : Bool) -> left || right = False -> left = False
boolOrFalseLeft False right same = Refl
boolOrFalseLeft True right same = case same of Refl impossible

0 boolOrFalseRight : (left, right : Bool) -> left || right = False -> right = False
boolOrFalseRight False right same = same
boolOrFalseRight True right same = case same of Refl impossible

0 boolOrBothFalse : (left, right : Bool) -> left = False -> right = False ->
  left || right = False
boolOrBothFalse False False Refl Refl = Refl

0 boolAndTrueRight : (left, right : Bool) -> left && right = True ->
  right = True
boolAndTrueRight False right same = case same of Refl impossible
boolAndTrueRight True False same = case same of Refl impossible
boolAndTrueRight True True same = Refl

0 memberKeyTrueElemLifecycleFrame :
  (keyEq : DecEq key) -> (wanted : key) ->
  (table : CoeffectContext key value) ->
  memberKey @{keyEq} wanted table = True ->
  Elem wanted (bindingKeys (bindings table))
memberKeyTrueElemLifecycleFrame keyEq wanted
  (MkCoeffectContext entries unique) present
  with (lookupEntries @{keyEq} wanted entries) proof found
  memberKeyTrueElemLifecycleFrame keyEq wanted
    (MkCoeffectContext entries unique) present | Nothing =
      case present of Refl impossible
  memberKeyTrueElemLifecycleFrame keyEq wanted
    (MkCoeffectContext entries unique) present | Just observed =
      lookupJustElem @{keyEq} wanted entries observed found

0 inactiveReliedHeadFalse :
  (nameEq : DecEq name) -> (provider, self, current : name) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) ->
  reliedHead @{nameEq} provider self
    (Bind current (MkFiber component parent retiredFlag table
      (Inactive outcome))) = False
inactiveReliedHeadFalse nameEq provider self current component parent retiredFlag
  table outcome with (decEq @{nameEq} current self)
  inactiveReliedHeadFalse nameEq provider current current component parent
    retiredFlag table outcome | Yes Refl = Refl
  inactiveReliedHeadFalse nameEq provider self current component parent
    retiredFlag table outcome | No _ = Refl

0 reliedViewObservation :
  (nameEq : DecEq name) -> (provider, self, current : name) ->
  View name deps -> Bool
reliedViewObservation nameEq provider self current view =
  case decEq @{nameEq} current self of
    Yes Refl => False
    No _ => viewContains @{nameEq} provider view

0 reliedHeadReloadingObservation :
  (nameEq : DecEq name) -> (provider, self, current : name) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  reliedHead @{nameEq} provider self
    (Bind current (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator view))) =
    reliedViewObservation nameEq provider self current view
reliedHeadReloadingObservation nameEq provider self current component parent
  retiredFlag table remaining accumulator view
  with (decEq @{nameEq} current self)
  reliedHeadReloadingObservation nameEq provider current current component parent
    retiredFlag table remaining accumulator view | Yes Refl = Refl
  reliedHeadReloadingObservation nameEq provider self current component parent
    retiredFlag table remaining accumulator view | No _ = Refl

0 reliedHeadActiveObservation :
  (nameEq : DecEq name) -> (provider, self, current : name) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  reliedHead @{nameEq} provider self
    (Bind current (MkFiber component parent retiredFlag table
      (Active accumulator view))) =
    reliedViewObservation nameEq provider self current view
reliedHeadActiveObservation nameEq provider self current component parent
  retiredFlag table accumulator view with (decEq @{nameEq} current self)
  reliedHeadActiveObservation nameEq provider current current component parent
    retiredFlag table accumulator view | Yes Refl = Refl
  reliedHeadActiveObservation nameEq provider self current component parent
    retiredFlag table accumulator view | No _ = Refl

0 reliedHeadUnloadingObservation :
  (nameEq : DecEq name) -> (provider, self, current : name) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (outcome : Maybe error) ->
  reliedHead @{nameEq} provider self
    (Bind current (MkFiber component parent retiredFlag table
      (Unloading accumulator view outcome))) =
    reliedViewObservation nameEq provider self current view
reliedHeadUnloadingObservation nameEq provider self current component parent
  retiredFlag table accumulator view outcome with (decEq @{nameEq} current self)
  reliedHeadUnloadingObservation nameEq provider current current component parent
    retiredFlag table accumulator view outcome | Yes Refl = Refl
  reliedHeadUnloadingObservation nameEq provider self current component parent
    retiredFlag table accumulator view outcome | No _ = Refl

0 lifecycleReliedObservation :
  (nameEq : DecEq name) -> (provider, self, current : name) ->
  Lifecycle key value world error name deps provision -> Bool
lifecycleReliedObservation nameEq provider self current (Inactive outcome) = False
lifecycleReliedObservation nameEq provider self current
  (Reloading remaining accumulator view) =
    reliedViewObservation nameEq provider self current view
lifecycleReliedObservation nameEq provider self current
  (Active accumulator view) =
    reliedViewObservation nameEq provider self current view
lifecycleReliedObservation nameEq provider self current
  (Unloading accumulator view outcome) =
    reliedViewObservation nameEq provider self current view

0 lifecycleControlReliedObservationSame :
  (nameEq : DecEq name) -> (provider, self, current : name) ->
  {left, right : Lifecycle key value world error name deps provision} ->
  LifecycleControlRelated left right ->
  lifecycleReliedObservation nameEq provider self current left =
    lifecycleReliedObservation nameEq provider self current right
lifecycleControlReliedObservationSame nameEq provider self current
  (InactiveControls outcomeSame) = Refl
lifecycleControlReliedObservationSame nameEq provider self current
  (ReloadingControls remainingSame accumulatorsSame viewsSame) =
    cong (reliedViewObservation nameEq provider self current) viewsSame
lifecycleControlReliedObservationSame nameEq provider self current
  (ActiveControls accumulatorsSame viewsSame) =
    cong (reliedViewObservation nameEq provider self current) viewsSame
lifecycleControlReliedObservationSame nameEq provider self current
  (UnloadingControls accumulatorsSame viewsSame outcomesSame) =
    cong (reliedViewObservation nameEq provider self current) viewsSame

0 reliedHeadLifecycleObservation :
  (nameEq : DecEq name) -> (provider, self, current : name) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  reliedHead @{nameEq} provider self
    (Bind current (MkFiber component parent retiredFlag table lifecycle)) =
    lifecycleReliedObservation nameEq provider self current lifecycle
reliedHeadLifecycleObservation nameEq provider self current component parent
  retiredFlag table (Inactive outcome) =
    inactiveReliedHeadFalse nameEq provider self current component parent
      retiredFlag table outcome
reliedHeadLifecycleObservation nameEq provider self current component parent
  retiredFlag table (Reloading remaining accumulator view) =
    reliedHeadReloadingObservation nameEq provider self current component parent
      retiredFlag table remaining accumulator view
reliedHeadLifecycleObservation nameEq provider self current component parent
  retiredFlag table (Active accumulator view) =
    reliedHeadActiveObservation nameEq provider self current component parent
      retiredFlag table accumulator view
reliedHeadLifecycleObservation nameEq provider self current component parent
  retiredFlag table (Unloading accumulator view outcome) =
    reliedHeadUnloadingObservation nameEq provider self current component parent
      retiredFlag table accumulator view outcome

0 lifecycleControlReliedHeadSame :
  (nameEq : DecEq name) -> (provider, self, current : name) ->
  {left, right : Fiber name key value world error} ->
  FiberControlRelated left right ->
  reliedHead @{nameEq} provider self (Bind current left) =
    reliedHead @{nameEq} provider self (Bind current right)
lifecycleControlReliedHeadSame nameEq provider self current
  (FibersControlRelated leftParent rightParent leftRetired rightRetired
    leftTable rightTable leftLifecycle rightLifecycle parentSame retiredSame
    lifecycleSame) =
      trans
        (reliedHeadLifecycleObservation nameEq provider self current _ leftParent
          leftRetired leftTable leftLifecycle)
        (trans (lifecycleControlReliedObservationSame nameEq provider self
          current lifecycleSame)
          (sym (reliedHeadLifecycleObservation nameEq provider self current _
            rightParent rightRetired rightTable rightLifecycle)))

||| Trace anchor used to turn one observed overlap at the current quotient
||| boundary into the exact Definition-65 edge forbidden at the consumer's
||| opening.  Later lifecycle reconstruction derives these component-stability
||| fields from the located checked trace; the record does not weaken the edge.
public export
record ForeignLifecyclePrecedenceAnchor
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState)
  (selected, actor : name)
  (currentSelected, currentOwner : Fiber name key value world error) where
  constructor MkForeignLifecyclePrecedenceAnchor
  anchoredConsumerEpisode : LocatedClosedEpisode name key world error value
    nameEq keyEq actor global
  anchoredSelectedFiber : Fiber name key value world error
  anchoredOwnerFiber : Fiber name key value world error
  0 anchoredSelectedFound : lookupFiber @{nameEq} selected
    (registry (closedStartState (locatedEpisode anchoredConsumerEpisode))) =
      Just anchoredSelectedFiber
  0 anchoredOwnerFound : lookupFiber @{nameEq} actor
    (registry (closedStartState (locatedEpisode anchoredConsumerEpisode))) =
      Just anchoredOwnerFiber
  0 anchoredSelectedComponent : fiberComponent anchoredSelectedFiber =
    fiberComponent currentSelected
  0 anchoredOwnerComponent : fiberComponent anchoredOwnerFiber =
    fiberComponent currentOwner

||| A current selected table entry on a dependency key would expose a concrete
||| precedence edge at the anchored consumer opening, contradicting the public
||| no-dependent-closing premise.  The result is the exact Boolean observation
||| consumed by the ordered guard frame.
public export
0 selectedProviderExcludedByNoDependent :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) ->
  (global : Transitions initial finalState) ->
  NoDependentClosingEpisode {nameEq = nameEq} {keyEq = keyEq}
    selected global ->
  (selectedFiber, ownerFiber : Fiber name key value world error) ->
  ForeignLifecyclePrecedenceAnchor name key world error value nameEq keyEq
    global selected actor selectedFiber ownerFiber ->
  (wanted : key) ->
  Elem wanted (dependencies
    (componentDependencies (fiberComponent ownerFiber))) ->
  providerCandidate @{keyEq} wanted selectedFiber = False
selectedProviderExcludedByNoDependent nameEq keyEq selected actor global
  noDependent selectedFiber ownerFiber
  (MkForeignLifecyclePrecedenceAnchor consumerEpisode startSelected startOwner
    selectedFound ownerFound selectedComponent ownerComponent)
  wanted ownerDeclares
  with (providerCandidate @{keyEq} wanted selectedFiber) proof candidate
  selectedProviderExcludedByNoDependent nameEq keyEq selected actor global
    noDependent selectedFiber ownerFiber
    (MkForeignLifecyclePrecedenceAnchor consumerEpisode startSelected startOwner
      selectedFound ownerFound selectedComponent ownerComponent)
    wanted ownerDeclares | False = Refl
  selectedProviderExcludedByNoDependent nameEq keyEq selected actor global
    noDependent selectedFiber ownerFiber
    (MkForeignLifecyclePrecedenceAnchor consumerEpisode startSelected startOwner
      selectedFound ownerFound selectedComponent ownerComponent)
    wanted ownerDeclares | True =
      let 0 memberTrue : (memberKey @{keyEq} wanted
            (ownedValues (fiberTable selectedFiber)) = True)
          memberTrue = boolAndTrueRight
            (isActive (fiberLifecycle selectedFiber))
            (memberKey @{keyEq} wanted
              (ownedValues (fiberTable selectedFiber)))
            candidate
          0 selectedTableMember : Elem wanted
            (bindingKeys (bindings
              (ownedValues (fiberTable selectedFiber))))
          selectedTableMember = memberKeyTrueElemLifecycleFrame keyEq wanted
            (ownedValues (fiberTable selectedFiber)) memberTrue
          0 selectedDeclaresCurrent : Elem wanted
            (dependencies (componentProvisions
              (fiberComponent selectedFiber)))
          selectedDeclaresCurrent = ownedSound (fiberTable selectedFiber)
            wanted selectedTableMember
          0 selectedDeclaresStart : Elem wanted
            (dependencies (componentProvisions
              (fiberComponent startSelected)))
          selectedDeclaresStart = replace
            {p = \component => Elem wanted
              (dependencies (componentProvisions component))}
            (sym selectedComponent) selectedDeclaresCurrent
          0 ownerDeclaresStart : Elem wanted
            (dependencies (componentDependencies
              (fiberComponent startOwner)))
          ownerDeclaresStart = replace
            {p = \component => Elem wanted
              (dependencies (componentDependencies component))}
            (sym ownerComponent) ownerDeclares
          0 edge : PrecedenceEdge nameEq selected actor
            (closedStartState (locatedEpisode consumerEpisode))
          edge = MkPrecedenceEdge wanted startSelected startOwner selectedFound
            ownerFound selectedDeclaresStart ownerDeclaresStart
      in void (noDependent actor consumerEpisode edge)

0 lookupNothingFromNotElemLifecycleFrame :
  (nameEq : DecEq name) -> (wanted : name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  Not (Elem wanted (bindingKeys entries)) ->
  lookupEntries @{nameEq} wanted entries = Nothing
lookupNothingFromNotElemLifecycleFrame nameEq wanted entries absent
  with (lookupEntries @{nameEq} wanted entries) proof found
  lookupNothingFromNotElemLifecycleFrame nameEq wanted entries absent |
    Nothing = Refl
  lookupNothingFromNotElemLifecycleFrame nameEq wanted entries absent |
    Just fiber = void (absent (lookupJustElem @{nameEq} wanted entries fiber
      found))

0 buildForeignOnlyLifecycleSources :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (deps : List key) ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  lookupEntries @{nameEq} selected left = Nothing ->
  lookupEntries @{nameEq} selected right = Nothing ->
  ((current : name) -> Not (current = selected) ->
    {leftFiber, rightFiber : Fiber name key value world error} ->
    FiberControlRelated leftFiber rightFiber ->
    bindings (ownedValues (fiberTable leftFiber)) =
      bindings (ownedValues (fiberTable rightFiber))) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    left right ->
  ForeignLifecycleOrderedSourcesRelated name key world error value nameEq keyEq
    selected deps left right
buildForeignOnlyLifecycleSources nameEq keyEq selected deps [] [] leftAbsent
  rightAbsent foreignTables SelectedOrderedControlsNil =
    ForeignLifecycleSourcesNil
buildForeignOnlyLifecycleSources nameEq keyEq selected deps
  (Bind current leftFiber :: leftRest)
  (Bind current rightFiber :: rightRest) leftAbsent rightAbsent foreignTables
  (SelectedOrderedControlsCons current relation tail)
  with (decEq @{nameEq} selected current)
  buildForeignOnlyLifecycleSources nameEq keyEq current deps
    (Bind current leftFiber :: leftRest)
    (Bind current rightFiber :: rightRest) leftAbsent rightAbsent foreignTables
    (SelectedOrderedControlsCons current relation tail) | Yes Refl =
      case leftAbsent of Refl impossible
  buildForeignOnlyLifecycleSources nameEq keyEq selected deps
    (Bind current leftFiber :: leftRest)
    (Bind current rightFiber :: rightRest) leftAbsent rightAbsent foreignTables
    (SelectedOrderedControlsCons current relation tail) |
    No selectedDistinct =
      let 0 currentDistinct : Not (current = selected)
          currentDistinct same = selectedDistinct (sym same)
          0 tailLeftAbsent : (lookupEntries @{nameEq} selected leftRest = Nothing)
          tailLeftAbsent = leftAbsent
          0 tailRightAbsent : (lookupEntries @{nameEq} selected rightRest = Nothing)
          tailRightAbsent = rightAbsent
      in case relation of
        SelectedFiberControls currentIsSelected static =>
          void (selectedDistinct (sym currentIsSelected))
        ForeignFiberControls relationDistinct controls =>
          ForeignLifecycleSourcesCons current
            (ForeignLifecycleSourceCell currentDistinct controls
              (foreignTables current currentDistinct controls)
              (\provider, self => lifecycleControlReliedHeadSame nameEq provider
                self current controls))
            (buildForeignOnlyLifecycleSources nameEq keyEq selected deps leftRest
              rightRest tailLeftAbsent tailRightAbsent foreignTables tail)

0 buildForeignLifecycleSources :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (deps : List key) ->
  (leftSelected : Fiber name key value world error) ->
  (cleanComponent : Component key value world error) ->
  (cleanParent : Parent name) -> (cleanRetired : Bool) ->
  (cleanTable : OwnedTable key value
    (componentProvisions cleanComponent)) ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  UniqueKeys (bindingKeys left) -> UniqueKeys (bindingKeys right) ->
  lookupEntries @{nameEq} selected left = Just leftSelected ->
  lookupEntries @{nameEq} selected right =
    Just (MkFiber cleanComponent cleanParent cleanRetired cleanTable
      (Inactive Nothing)) ->
  ((wanted : key) -> Elem wanted deps ->
    providerCandidate @{keyEq} wanted leftSelected = False) ->
  ((current : name) -> Not (current = selected) ->
    {leftFiber, rightFiber : Fiber name key value world error} ->
    FiberControlRelated leftFiber rightFiber ->
    bindings (ownedValues (fiberTable leftFiber)) =
      bindings (ownedValues (fiberTable rightFiber))) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    left right ->
  ForeignLifecycleOrderedSourcesRelated name key world error value nameEq keyEq
    selected deps left right
buildForeignLifecycleSources nameEq keyEq selected deps leftSelected
  cleanComponent cleanParent cleanRetired cleanTable [] [] UniqueNil UniqueNil
  leftFound rightFound selectedExcluded foreignTables
  SelectedOrderedControlsNil = case leftFound of Refl impossible
buildForeignLifecycleSources nameEq keyEq selected deps leftSelected
  cleanComponent cleanParent cleanRetired cleanTable
  (Bind current leftFiber :: leftRest)
  (Bind current rightFiber :: rightRest)
  (UniqueCons leftFresh leftUnique) (UniqueCons rightFresh rightUnique)
  leftFound rightFound selectedExcluded foreignTables
  (SelectedOrderedControlsCons current relation tail)
  with (decEq @{nameEq} selected current)
  buildForeignLifecycleSources nameEq keyEq current deps leftSelected
    cleanComponent cleanParent cleanRetired cleanTable
    (Bind current leftFiber :: leftRest)
    (Bind current rightFiber :: rightRest)
    (UniqueCons leftFresh leftUnique) (UniqueCons rightFresh rightUnique)
    leftFound rightFound selectedExcluded foreignTables
    (SelectedOrderedControlsCons current
      (SelectedFiberControls currentIsSelected static) tail) | Yes Refl =
      let 0 leftHeadFound : (lookupEntries @{nameEq} current
            (Bind current leftFiber :: leftRest) = Just leftFiber)
          leftHeadFound = lookupHeadSelfLifecycleFrame nameEq current leftFiber
            leftRest
          0 rightHeadFound : (lookupEntries @{nameEq} current
            (Bind current rightFiber :: rightRest) = Just rightFiber)
          rightHeadFound = lookupHeadSelfLifecycleFrame nameEq current rightFiber
            rightRest
          0 leftSame : leftFiber = leftSelected
          leftSame = justInjectiveLifecycleFrame leftFound
          cleanFiber : Fiber name key value world error
          cleanFiber = MkFiber cleanComponent cleanParent cleanRetired cleanTable
            (Inactive Nothing)
          0 rightSame : rightFiber = cleanFiber
          rightSame = justInjectiveLifecycleFrame rightFound
          0 leftTailAbsent : lookupEntries @{nameEq} current leftRest = Nothing
          leftTailAbsent = lookupNothingFromNotElemLifecycleFrame nameEq current
            leftRest leftFresh
          0 rightTailAbsent : lookupEntries @{nameEq} current rightRest = Nothing
          rightTailAbsent = lookupNothingFromNotElemLifecycleFrame nameEq current
            rightRest rightFresh
      in case leftSame of
        Refl => case rightSame of
          Refl => ForeignLifecycleSourcesCons current
            (SelectedLifecycleSourceCell Refl static Refl Refl
              (\provider, self => inactiveReliedHeadFalse nameEq provider self
                current cleanComponent cleanParent cleanRetired cleanTable
                Nothing)
              selectedExcluded)
            (buildForeignOnlyLifecycleSources nameEq keyEq current deps leftRest
              rightRest leftTailAbsent rightTailAbsent foreignTables tail)
  buildForeignLifecycleSources nameEq keyEq current deps leftSelected
    cleanComponent cleanParent cleanRetired cleanTable
    (Bind current leftFiber :: leftRest)
    (Bind current rightFiber :: rightRest)
    (UniqueCons leftFresh leftUnique) (UniqueCons rightFresh rightUnique)
    leftFound rightFound selectedExcluded foreignTables
    (SelectedOrderedControlsCons current
      (ForeignFiberControls currentDistinct controls) tail) | Yes Refl =
      void (currentDistinct Refl)
  buildForeignLifecycleSources nameEq keyEq selected deps leftSelected
    cleanComponent cleanParent cleanRetired cleanTable
    (Bind current leftFiber :: leftRest)
    (Bind current rightFiber :: rightRest)
    (UniqueCons leftFresh leftUnique) (UniqueCons rightFresh rightUnique)
    leftFound rightFound selectedExcluded foreignTables
    (SelectedOrderedControlsCons current relation tail) |
    No selectedDistinct =
      let 0 tailLeftFound : (lookupEntries @{nameEq} selected leftRest =
            Just leftSelected)
          tailLeftFound = leftFound
          0 tailRightFound : (lookupEntries @{nameEq} selected rightRest =
            Just (MkFiber cleanComponent cleanParent cleanRetired cleanTable
              (Inactive Nothing)))
          tailRightFound = rightFound
      in case relation of
        SelectedFiberControls currentIsSelected static =>
          void (selectedDistinct (sym currentIsSelected))
        ForeignFiberControls relationDistinct controls =>
          ForeignLifecycleSourcesCons current
            (ForeignLifecycleSourceCell
              (\same => selectedDistinct (sym same)) controls
              (foreignTables current (\same => selectedDistinct (sym same))
                controls)
              (\provider, self => lifecycleControlReliedHeadSame nameEq provider
                self current controls))
            (buildForeignLifecycleSources nameEq keyEq selected deps leftSelected
              cleanComponent cleanParent cleanRetired cleanTable leftRest
              rightRest leftUnique rightUnique tailLeftFound tailRightFound
              selectedExcluded foreignTables tail)

||| The selected cell is allowed to carry different installed controls on the
||| plan side.  A false left reliance nevertheless transfers: every foreign
||| head is equal, and the selected survivor head is observably Inactive.
public export
0 foreignLifecycleSourcesPreserveFalseReliance :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {keyEq : DecEq key} -> {selected : name} -> {deps : List key} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  ForeignLifecycleOrderedSourcesRelated name key world error value nameEq keyEq
    selected deps left right ->
  reliedOnBy @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor actor left = False ->
  reliedOnBy @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor actor right = False
foreignLifecycleSourcesPreserveFalseReliance nameEq actor [] []
  ForeignLifecycleSourcesNil leftFalse = Refl
foreignLifecycleSourcesPreserveFalseReliance nameEq actor
  (Bind current leftFiber :: leftRest)
  (Bind current rightFiber :: rightRest)
  (ForeignLifecycleSourcesCons current relation tail) leftFalse =
    let leftHead : Bool
        leftHead = reliedHead @{nameEq} {name = name} {key = key}
          {value = value} {world = world} {error = error} actor actor
          (Bind current leftFiber)
        leftTail : Bool
        leftTail = reliedOnBy @{nameEq} {name = name} {key = key}
          {value = value} {world = world} {error = error} actor actor leftRest
        0 leftHeadFalse : (leftHead = False)
        leftHeadFalse = boolOrFalseLeft leftHead leftTail leftFalse
        0 leftTailFalse : (leftTail = False)
        leftTailFalse = boolOrFalseRight leftHead leftTail leftFalse
        0 rightTailFalse : (reliedOnBy @{nameEq} {name = name} {key = key}
          {value = value} {world = world} {error = error} actor actor
          rightRest = False)
        rightTailFalse = foreignLifecycleSourcesPreserveFalseReliance nameEq
          actor leftRest rightRest tail leftTailFalse
    in case relation of
      SelectedLifecycleSourceCell currentIsSelected static rightUninstalled
        rightInactive rightHeadFalse selectedProviderFalse =>
          boolOrBothFalse
            (reliedHead @{nameEq} actor actor (Bind current rightFiber))
            (reliedOnBy @{nameEq} actor actor rightRest)
            (rightHeadFalse actor actor) rightTailFalse
      ForeignLifecycleSourceCell currentDistinct controls tablesSame
        headSame =>
          let 0 rightHeadFalse :
                (reliedHead @{nameEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error} actor actor
                  (Bind current rightFiber) = False)
              rightHeadFalse = trans (sym (headSame actor actor)) leftHeadFalse
          in boolOrBothFalse
            (reliedHead @{nameEq} actor actor (Bind current rightFiber))
            (reliedOnBy @{nameEq} actor actor rightRest)
            rightHeadFalse rightTailFalse

||| Assemble the exact saturated frame consumed by all five concrete lifecycle
||| replay branches.  No raw registry equality is used: the caller supplies
||| host-observable foreign table equality, while the public no-dependent
||| premise discharges the sole selected-provider exception through the trace
||| anchor above.
public export
0 foreignLifecycleGuardFrameFromNoDependent :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> Not (actor = selected) ->
  (global : Transitions initial finalState) ->
  NoDependentClosingEpisode {nameEq = nameEq} {keyEq = keyEq}
    selected global ->
  (leftOwner, rightOwner, leftSelected : Fiber name key value world error) ->
  (left, right : Registry name key value world error) ->
  lookupFiber @{nameEq} selected left = Just leftSelected ->
  lookupFiber @{nameEq} actor left = Just leftOwner ->
  lookupFiber @{nameEq} actor right = Just rightOwner ->
  ForeignLifecyclePrecedenceAnchor name key world error value nameEq keyEq
    global selected actor leftSelected leftOwner ->
  SelectedSurvivorCleanInactive name key world error value nameEq selected
    (MkSystemState ambient right) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (bindings left) (bindings right) ->
  ((current : name) -> Not (current = selected) ->
    {leftFiber, rightFiber : Fiber name key value world error} ->
    FiberControlRelated leftFiber rightFiber ->
    bindings (ownedValues (fiberTable leftFiber)) =
      bindings (ownedValues (fiberTable rightFiber))) ->
  ForeignLifecycleGuardFrame name key world error value nameEq keyEq selected
    actor (dependencies (componentDependencies (fiberComponent leftOwner)))
    leftOwner rightOwner left right
foreignLifecycleGuardFrameFromNoDependent nameEq keyEq selected actor
  actorDistinct global noDependent leftOwner rightOwner leftSelected left right
  selectedFound ownerLeftFound ownerRightFound anchor
  (SelectedCleanInactiveWitness cleanComponent cleanParent cleanRetired cleanTable
    cleanFound)
  ordered foreignTables =
    let 0 selectedExcluded : (wanted : key) ->
          Elem wanted (dependencies
            (componentDependencies (fiberComponent leftOwner))) ->
          providerCandidate @{keyEq} wanted leftSelected = False
        selectedExcluded = selectedProviderExcludedByNoDependent nameEq keyEq
          selected actor global noDependent leftSelected leftOwner anchor
        0 sources : ForeignLifecycleOrderedSourcesRelated name key world error
          value nameEq keyEq selected
          (dependencies (componentDependencies (fiberComponent leftOwner)))
          (bindings left) (bindings right)
        sources = buildForeignLifecycleSources nameEq keyEq selected
          (dependencies (componentDependencies (fiberComponent leftOwner)))
          leftSelected cleanComponent cleanParent cleanRetired cleanTable
          (bindings left) (bindings right) (uniqueBindings left)
          (uniqueBindings right)
          (trans (sym (lookupFiberAsEntries nameEq selected left)) selectedFound)
          (trans (sym (lookupFiberAsEntries nameEq selected right)) cleanFound)
          selectedExcluded foreignTables ordered
        0 maybeOwnerControls : FiberControlMaybeRelated
          {name = name} {key = key} {value = value} {world = world}
          {error = error}
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
            {world = world} {error = error} actor left)
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
            {world = world} {error = error} actor right)
        maybeOwnerControls = selectedOrderedForeignLookupControls nameEq selected
          actor actorDistinct left right ordered
        0 leftReindexed : FiberControlMaybeRelated
          (Just leftOwner) (lookupFiber @{nameEq} actor right)
        leftReindexed = replace
          {p = \observed => FiberControlMaybeRelated observed
            (lookupFiber @{nameEq} actor right)}
          ownerLeftFound maybeOwnerControls
        0 exactOwnerControls : FiberControlMaybeRelated
          (Just leftOwner) (Just rightOwner)
        exactOwnerControls = replace
          {p = \observed => FiberControlMaybeRelated (Just leftOwner) observed}
          ownerRightFound leftReindexed
        0 controls : FiberControlRelated leftOwner rightOwner
        controls = exactFiberControlsFromMaybe exactOwnerControls
        0 relianceFrame :
          relied @{nameEq} {name = name} {key = key} {value = value}
            {world = world} {error = error} actor left = False ->
          relied @{nameEq} {name = name} {key = key} {value = value}
            {world = world} {error = error} actor right = False
        relianceFrame leftFalse =
          foreignLifecycleSourcesPreserveFalseReliance nameEq actor
            (bindings left) (bindings right) sources leftFalse
    in MkForeignLifecycleGuardFrame sources controls relianceFrame
