module DGamma.CP4DeletionRelationalLifecycleSources

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionRelationalActionCore
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedForeignLifecycleFrame
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

0 lookupAbsentFromFresh :
  (nameEq : DecEq name) -> (wanted : name) ->
  (entries : List (Binding name item)) ->
  Not (Elem wanted (bindingKeys entries)) ->
  lookupEntries @{nameEq} wanted entries = Nothing
lookupAbsentFromFresh nameEq wanted [] fresh = Refl
lookupAbsentFromFresh nameEq wanted (Bind current item :: rest) fresh
  with (decEq @{nameEq} wanted current)
  lookupAbsentFromFresh nameEq current (Bind current item :: rest) fresh |
    Yes Refl = void (fresh Here)
  lookupAbsentFromFresh nameEq wanted (Bind current item :: rest) fresh |
    No distinct = lookupAbsentFromFresh nameEq wanted rest
      (\later => fresh (There later))

0 lookupHead :
  (nameEq : DecEq name) -> (actor : name) -> (fiber : item actor) ->
  (rest : List (Binding name item)) ->
  lookupEntries @{nameEq} actor (Bind actor fiber :: rest) = Just fiber
lookupHead nameEq actor fiber rest with (decEq @{nameEq} actor actor)
  lookupHead nameEq actor fiber rest | Yes Refl = Refl
  lookupHead nameEq actor fiber rest | No contra = void (contra Refl)

0 effectLookupBindings :
  Maybe (Fiber name key value world error) -> List (Binding key value)
effectLookupBindings Nothing = []
effectLookupBindings (Just fiber) = bindings (ownedValues (fiberTable fiber))

0 projectedEffectBindingsViaEntries :
  (nameEq : DecEq name) -> (wanted : name) -> (ambient : world) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (unique : UniqueKeys (bindingKeys entries)) ->
  bindings (effectTables (projectEffectState @{nameEq}
    (the (SystemState name key value world error)
      (MkSystemState ambient (MkCoeffectContext entries unique)))) wanted) =
  effectLookupBindings (lookupEntries @{nameEq} wanted entries)
projectedEffectBindingsViaEntries nameEq wanted ambient entries unique
  with (lookupEntries @{nameEq} wanted entries)
  projectedEffectBindingsViaEntries nameEq wanted ambient entries unique |
    Nothing = Refl
  projectedEffectBindingsViaEntries nameEq wanted ambient entries unique |
    Just fiber = Refl

0 lookupEntriesSkipDifferent :
  (nameEq : DecEq name) -> (wanted, head : name) -> Not (wanted = head) ->
  (headFiber : item head) -> (rest : List (Binding name item)) ->
  lookupEntries @{nameEq} wanted (Bind head headFiber :: rest) =
    lookupEntries @{nameEq} wanted rest
lookupEntriesSkipDifferent nameEq wanted head distinct headFiber rest
  with (decEq @{nameEq} wanted head)
  lookupEntriesSkipDifferent nameEq head head distinct headFiber rest |
    Yes Refl = void (distinct Refl)
  lookupEntriesSkipDifferent nameEq wanted head distinct headFiber rest |
    No other = Refl

0 projectTailTableDifferent :
  (nameEq : DecEq name) -> (wanted, head : name) ->
  Not (wanted = head) -> (ambient : world) ->
  (headFiber : Fiber name key value world error) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  (headFresh : Not (Elem head (bindingKeys rest))) ->
  (restUnique : UniqueKeys (bindingKeys rest)) ->
  bindings (effectTables (projectEffectState @{nameEq}
    (the (SystemState name key value world error)
      (MkSystemState ambient
        (MkCoeffectContext (Bind head headFiber :: rest)
          (UniqueCons headFresh restUnique))))) wanted) =
  bindings (effectTables (projectEffectState @{nameEq}
    (the (SystemState name key value world error)
      (MkSystemState ambient (MkCoeffectContext rest restUnique)))) wanted)
projectTailTableDifferent nameEq wanted head distinct ambient headFiber rest
  headFresh restUnique =
    let 0 observationsSame : (effectLookupBindings
          (lookupEntries @{nameEq} wanted (Bind head headFiber :: rest)) =
          effectLookupBindings (lookupEntries @{nameEq} wanted rest))
        observationsSame = cong effectLookupBindings
          (lookupEntriesSkipDifferent nameEq wanted head distinct headFiber rest)
    in trans (projectedEffectBindingsViaEntries nameEq wanted ambient
      (Bind head headFiber :: rest) (UniqueCons headFresh restUnique))
      (trans observationsSame
        (sym (projectedEffectBindingsViaEntries nameEq wanted ambient rest
          restUnique)))

||| Drop matching ordered heads from the complete effect relation.  The unique
||| domain proofs discharge the sole same-name tail case; every distinct actor
||| is definitionally the old full lookup after skipping the head.
0 tailEffectRelation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (leftWorld, rightWorld : world) -> (actor : name) ->
  (leftFiber, rightFiber : Fiber name key value world error) ->
  (leftRest, rightRest : List
    (Binding name (FiberAt name key value world error))) ->
  (leftUnique : UniqueKeys (bindingKeys leftRest)) ->
  (rightUnique : UniqueKeys (bindingKeys rightRest)) ->
  (leftFresh : Not (Elem actor (bindingKeys leftRest))) ->
  (rightFresh : Not (Elem actor (bindingKeys rightRest))) ->
  EffectStateRelated keyEq
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState leftWorld
          (MkCoeffectContext (Bind actor leftFiber :: leftRest)
            (UniqueCons leftFresh leftUnique)))))
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState rightWorld
          (MkCoeffectContext (Bind actor rightFiber :: rightRest)
            (UniqueCons rightFresh rightUnique))))) ->
  EffectStateRelated keyEq
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState leftWorld (MkCoeffectContext leftRest leftUnique))))
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState rightWorld (MkCoeffectContext rightRest rightUnique))))
tailEffectRelation nameEq keyEq leftWorld rightWorld actor leftFiber rightFiber
  leftRest rightRest leftUnique rightUnique leftFresh rightFresh effects =
    MkEffectStateRelated (ambientExact effects) tables
  where
  0 tables : (wanted : name) ->
    bindings (effectTables
      (projectEffectState @{nameEq}
        (the (SystemState name key value world error)
          (MkSystemState leftWorld
            (MkCoeffectContext leftRest leftUnique)))) wanted) =
    bindings (effectTables
      (projectEffectState @{nameEq}
        (the (SystemState name key value world error)
          (MkSystemState rightWorld
            (MkCoeffectContext rightRest rightUnique)))) wanted)
  tables wanted with (decEq @{nameEq} wanted actor)
    tables wanted | Yes same = case same of
      Refl => rewrite lookupAbsentFromFresh nameEq actor leftRest leftFresh in
        rewrite lookupAbsentFromFresh nameEq actor rightRest rightFresh in Refl
    tables wanted | No distinct =
      trans (sym (projectTailTableDifferent nameEq wanted actor distinct
        leftWorld leftFiber leftRest leftFresh leftUnique))
        (trans (tablesExact effects wanted)
          (projectTailTableDifferent nameEq wanted actor distinct rightWorld
            rightFiber rightRest rightFresh rightUnique))

||| Ordered runtime sources combine the control relation with exact per-cell
||| table bindings.  This is the sufficient executable observation for provider
||| scans, iterator inputs, and reliance guards.
public export
data OrderedRuntimeSourcesRelated :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  List (Binding name (FiberAt name key value world error)) ->
  List (Binding name (FiberAt name key value world error)) -> Type where
  RuntimeSourcesNil : OrderedRuntimeSourcesRelated name key world error value
    [] []
  RuntimeSourcesCons :
    (actor : name) ->
    FiberControlRelated leftFiber rightFiber ->
    bindings (ownedValues (fiberTable leftFiber)) =
      bindings (ownedValues (fiberTable rightFiber)) ->
    OrderedRuntimeSourcesRelated name key world error value leftRest rightRest ->
    OrderedRuntimeSourcesRelated name key world error value
      (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest)

||| Construct the full runtime source relation from the relational suffix
||| boundary's two orthogonal observations.
public export
0 buildOrderedRuntimeSources :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (left, right : SystemState name key value world error) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} left)
    (projectEffectState @{nameEq} right) ->
  OrderedRegistryControlsRelated name key world error value
    (bindings (registry left)) (bindings (registry right)) ->
  OrderedRuntimeSourcesRelated name key world error value
    (bindings (registry left)) (bindings (registry right))
buildOrderedRuntimeSources nameEq keyEq
  (MkSystemState leftWorld (MkCoeffectContext [] UniqueNil))
  (MkSystemState rightWorld (MkCoeffectContext [] UniqueNil)) effects
  OrderedControlsNil = RuntimeSourcesNil
buildOrderedRuntimeSources nameEq keyEq
  left@(MkSystemState leftWorld
    (MkCoeffectContext (Bind actor leftFiber :: leftRest)
      (UniqueCons leftFresh leftUnique)))
  right@(MkSystemState rightWorld
    (MkCoeffectContext (Bind actor rightFiber :: rightRest)
      (UniqueCons rightFresh rightUnique))) effects
  (OrderedControlsCons actor controls tail) =
    let 0 leftFound : (lookupFiber @{nameEq} actor (registry left) =
          Just leftFiber)
        leftFound = lookupHead nameEq actor leftFiber leftRest
        0 rightFound : (lookupFiber @{nameEq} actor (registry right) =
          Just rightFiber)
        rightFound = lookupHead nameEq actor rightFiber rightRest
        0 tablesSame : bindings (ownedValues (fiberTable leftFiber)) =
          bindings (ownedValues (fiberTable rightFiber))
        tablesSame = relatedLocatedFiberTablesSame nameEq actor left right
          leftFiber rightFiber leftFound rightFound effects
        0 tailEffects : EffectStateRelated keyEq
          (projectEffectState @{nameEq}
            (the (SystemState name key value world error)
              (MkSystemState leftWorld
                (MkCoeffectContext leftRest leftUnique))))
          (projectEffectState @{nameEq}
            (the (SystemState name key value world error)
              (MkSystemState rightWorld
                (MkCoeffectContext rightRest rightUnique))))
        tailEffects = tailEffectRelation nameEq keyEq leftWorld rightWorld actor
          leftFiber rightFiber leftRest rightRest leftUnique rightUnique leftFresh
          rightFresh effects
        0 tailSources : OrderedRuntimeSourcesRelated name key world error value
          leftRest rightRest
        tailSources = buildOrderedRuntimeSources nameEq keyEq
          (MkSystemState leftWorld (MkCoeffectContext leftRest leftUnique))
          (MkSystemState rightWorld (MkCoeffectContext rightRest rightUnique))
          tailEffects tail
    in RuntimeSourcesCons actor controls tablesSame tailSources

0 lifecycleActiveSame : LifecycleControlRelated left right ->
  isActive left = isActive right
lifecycleActiveSame (InactiveControls outcome) = Refl
lifecycleActiveSame (ReloadingControls remaining accumulator view) = Refl
lifecycleActiveSame (ActiveControls accumulator view) = Refl
lifecycleActiveSame (UnloadingControls accumulator view outcome) = Refl

0 bindingMemberSame :
  {key : Type} -> {value : key -> Type} ->
  (keyEq : DecEq key) -> (wanted : key) ->
  (left, right : CoeffectContext key value) ->
  bindings left = bindings right ->
  memberKey @{keyEq} wanted left = memberKey @{keyEq} wanted right
bindingMemberSame keyEq wanted
  (MkCoeffectContext leftEntries leftUnique)
  (MkCoeffectContext rightEntries rightUnique) same =
    case same of Refl => Refl

0 runtimeProviderCandidateSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {left, right : Fiber name key value world error} ->
  (keyEq : DecEq key) -> (wanted : key) ->
  FiberControlRelated left right ->
  bindings (ownedValues (fiberTable left)) =
    bindings (ownedValues (fiberTable right)) ->
  (isActive (fiberLifecycle left) &&
    memberKey @{keyEq} wanted (ownedValues (fiberTable left))) =
  (isActive (fiberLifecycle right) &&
    memberKey @{keyEq} wanted (ownedValues (fiberTable right)))
runtimeProviderCandidateSame keyEq wanted
  (FibersControlRelated leftParent rightParent leftRetired rightRetired
    leftTable rightTable leftLifecycle rightLifecycle parentSame retiredSame
    lifecycleSame) tablesSame =
      rewrite lifecycleActiveSame lifecycleSame in
        cong (isActive rightLifecycle &&)
          (bindingMemberSame keyEq wanted (ownedValues leftTable)
            (ownedValues rightTable) tablesSame)

||| Provider selection sees the same first candidate in both ordered registries.
public export
0 orderedRuntimeProviderInSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  OrderedRuntimeSourcesRelated name key world error value left right ->
  providerIn @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} wanted left =
  providerIn @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} wanted right
orderedRuntimeProviderInSame nameEq keyEq wanted [] [] RuntimeSourcesNil = Refl
orderedRuntimeProviderInSame nameEq keyEq wanted
  (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest)
  (RuntimeSourcesCons actor controls tablesSame tail)
  with (isActive (fiberLifecycle rightFiber) &&
    memberKey @{keyEq} wanted (ownedValues (fiberTable rightFiber))) proof right
  orderedRuntimeProviderInSame nameEq keyEq wanted
    (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest)
    (RuntimeSourcesCons actor controls tablesSame tail) | False =
      let 0 same = runtimeProviderCandidateSame keyEq wanted controls tablesSame
          0 leftFalse = trans same right
      in rewrite leftFalse in
        orderedRuntimeProviderInSame nameEq keyEq wanted leftRest rightRest tail
  orderedRuntimeProviderInSame nameEq keyEq wanted
    (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest)
    (RuntimeSourcesCons actor controls tablesSame tail) | True =
      let 0 same = runtimeProviderCandidateSame keyEq wanted controls tablesSame
          0 leftTrue = trans same right
      in rewrite leftTrue in Refl

0 resolveViewRuntimeSubsetSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (requested : List key) ->
  (left, right : Registry name key value world error) ->
  OrderedRuntimeSourcesRelated name key world error value
    (bindings left) (bindings right) ->
  resolveView @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} requested left =
  resolveView @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} requested right
resolveViewRuntimeSubsetSame nameEq keyEq [] left right sources = Refl
resolveViewRuntimeSubsetSame nameEq keyEq (wanted :: rest) left right sources
  with (providerOf @{nameEq} @{keyEq} wanted left) proof leftProvider
  resolveViewRuntimeSubsetSame nameEq keyEq (wanted :: rest) left right sources |
    Nothing with (providerOf @{nameEq} @{keyEq} wanted right) proof rightProvider
    resolveViewRuntimeSubsetSame nameEq keyEq (wanted :: rest) left right sources |
      Nothing | Nothing = Refl
    resolveViewRuntimeSubsetSame nameEq keyEq (wanted :: rest) left right sources |
      Nothing | Just rightName = case trans (sym leftProvider)
        (trans (orderedRuntimeProviderInSame nameEq keyEq wanted
          (bindings left) (bindings right) sources) rightProvider) of Refl impossible
  resolveViewRuntimeSubsetSame nameEq keyEq (wanted :: rest) left right sources |
    Just leftName with (providerOf @{nameEq} @{keyEq} wanted right) proof rightProvider
    resolveViewRuntimeSubsetSame nameEq keyEq (wanted :: rest) left right sources |
      Just leftName | Nothing = case trans (sym leftProvider)
        (trans (orderedRuntimeProviderInSame nameEq keyEq wanted
          (bindings left) (bindings right) sources) rightProvider) of Refl impossible
    resolveViewRuntimeSubsetSame nameEq keyEq (wanted :: rest) left right sources |
      Just leftName | Just rightName =
        case justInjective (trans (sym leftProvider)
          (trans (orderedRuntimeProviderInSame nameEq keyEq wanted
            (bindings left) (bindings right) sources) rightProvider)) of
          Refl => cong (map (ProviderView leftName))
            (resolveViewRuntimeSubsetSame nameEq keyEq rest left right sources)

public export
0 orderedRuntimeResolveViewSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (deps : List key) ->
  (left, right : Registry name key value world error) ->
  OrderedRuntimeSourcesRelated name key world error value
    (bindings left) (bindings right) ->
  resolveView @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} deps left =
  resolveView @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} deps right
orderedRuntimeResolveViewSame = resolveViewRuntimeSubsetSame

||| Related owners and the same ordered provider observations compute the same
||| current target view.  The shared component is explicit so the dependent
||| `View` result has one definitionally common index.
public export
0 orderedRuntimeTargetFiberSame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) ->
  (leftRetired, rightRetired : Bool) ->
  (leftTable, rightTable : OwnedTable key value
    (componentProvisions component)) ->
  (leftLifecycle, rightLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (left, right : Registry name key value world error) ->
  leftRetired = rightRetired ->
  OrderedRuntimeSourcesRelated name key world error value
    (bindings left) (bindings right) ->
  targetFiber @{nameEq} @{keyEq}
    (MkFiber component leftParent leftRetired leftTable leftLifecycle) left =
  targetFiber @{nameEq} @{keyEq}
    (MkFiber component rightParent rightRetired rightTable rightLifecycle) right
orderedRuntimeTargetFiberSame nameEq keyEq component leftParent rightParent
  leftRetired rightRetired leftTable rightTable leftLifecycle rightLifecycle
  left right retiredSame sources =
    rewrite retiredSame in case rightRetired of
      True => Refl
      False => orderedRuntimeResolveViewSame nameEq keyEq
        (dependencies (componentDependencies component)) left right sources

public export
0 orderedRuntimeTargetMatchesSame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) ->
  (leftRetired, rightRetired : Bool) ->
  (leftTable, rightTable : OwnedTable key value
    (componentProvisions component)) ->
  (leftLifecycle, rightLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (left, right : Registry name key value world error) ->
  leftRetired = rightRetired ->
  OrderedRuntimeSourcesRelated name key world error value
    (bindings left) (bindings right) ->
  (leftView, rightView : View name
    (dependencies (componentDependencies component))) ->
  leftView = rightView ->
  targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq}
      (MkFiber component leftParent leftRetired leftTable leftLifecycle) left)
    leftView =
  targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq}
      (MkFiber component rightParent rightRetired rightTable rightLifecycle) right)
    rightView
orderedRuntimeTargetMatchesSame nameEq keyEq component leftParent rightParent
  leftRetired rightRetired leftTable rightTable leftLifecycle rightLifecycle
  left right retiredSame sources leftView rightView viewSame =
    rewrite viewSame in cong (\target => targetMatches @{nameEq} target rightView)
      (orderedRuntimeTargetFiberSame nameEq keyEq component leftParent rightParent
        leftRetired rightRetired leftTable rightTable leftLifecycle rightLifecycle
        left right retiredSame sources)

public export
0 orderedRuntimeReliedOnBySame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (provider, self : name) ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  OrderedRuntimeSourcesRelated name key world error value left right ->
  reliedOnBy @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provider self left =
  reliedOnBy @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provider self right
orderedRuntimeReliedOnBySame nameEq provider self [] [] RuntimeSourcesNil = Refl
orderedRuntimeReliedOnBySame nameEq provider self
  (Bind current leftFiber :: leftRest) (Bind current rightFiber :: rightRest)
  (RuntimeSourcesCons current controls tablesSame tail) =
    rewrite lifecycleControlReliedHeadSame nameEq provider self current controls in
      cong (reliedHead @{nameEq} provider self (Bind current rightFiber) ||)
        (orderedRuntimeReliedOnBySame nameEq provider self leftRest rightRest tail)

public export
0 orderedRuntimeReliedSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (left, right : Registry name key value world error) ->
  OrderedRuntimeSourcesRelated name key world error value
    (bindings left) (bindings right) ->
  relied @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor left =
  relied @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor right
orderedRuntimeReliedSame nameEq actor left right sources =
  orderedRuntimeReliedOnBySame nameEq actor actor (bindings left)
    (bindings right) sources
