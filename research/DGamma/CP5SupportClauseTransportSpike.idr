module DGamma.CP5SupportClauseTransportSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4SupportSolution
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5AllSupportedMetadataSpike
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

public export
supportClauseParent : (name : Type) -> (name -> Bool) -> Parent name -> Bool
supportClauseParent name predicate Root = True
supportClauseParent name predicate (ChildOf parent) = predicate parent

0 clauseAndTrue : (left, right : Bool) -> (left = True) -> (right = True) -> (left && right = True)
clauseAndTrue True True Refl Refl = Refl

0 clauseAndParts : (left, right : Bool) -> (left && right = True) -> (left = True, right = True)
clauseAndParts False right exact = case exact of Refl impossible
clauseAndParts True right exact = (Refl, exact)

0 clauseOrCases : (left, right : Bool) -> (left || right = True) -> Either (left = True) (right = True)
clauseOrCases False right exact = Right exact
clauseOrCases True right exact = Left Refl

0 clauseOrFromEither : (left, right : Bool) -> Either (left = True) (right = True) -> (left || right = True)
clauseOrFromEither left right (Left exact) = rewrite exact in Refl
clauseOrFromEither False right (Right exact) = exact
clauseOrFromEither True right (Right exact) = Refl

0 clauseAllListAt : (element : Type) -> (predicate : element -> Bool) -> (items : List element) ->
  (selected : element) -> Elem selected items -> (allList predicate items = True) -> (predicate selected = True)
clauseAllListAt element predicate (_ :: rest) selected Here exact = fst (clauseAndParts (predicate selected) (allList predicate rest) exact)
clauseAllListAt element predicate (head :: rest) selected (There later) exact =
  clauseAllListAt element predicate rest selected later (snd (clauseAndParts (predicate head) (allList predicate rest) exact))

0 clauseAllListBuild : (element : Type) -> (predicate : element -> Bool) -> (items : List element) ->
  ((selected : element) -> Elem selected items -> (predicate selected = True)) -> (allList predicate items = True)
clauseAllListBuild element predicate [] each = Refl
clauseAllListBuild element predicate (head :: rest) each =
  clauseAndTrue (predicate head) (allList predicate rest) (each head Here)
    (clauseAllListBuild element predicate rest (\selected, member => each selected (There member)))

export
0 actualSupportClauseAtFiber :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) -> (predicate : name -> Bool) -> (selected : name) -> (fiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} selected (registry state) = Just fiber) ->
  (supportClause {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} predicate selected state =
    (not (retired fiber) && supportClauseParent name predicate (fiberParent fiber) &&
     allList (\wanted => providerFromPredicate {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq}
       wanted predicate (registryFibers {name = name} {key = key} {value = value} {world = world} {error = error} (registry state))) (dependencies (componentDependencies (fiberComponent fiber)))))
actualSupportClauseAtFiber name key world error value nameEq keyEq state predicate selected (MkFiber component Root flag table lifecycle) found = rewrite found in Refl
actualSupportClauseAtFiber name key world error value nameEq keyEq state predicate selected (MkFiber component (ChildOf parent) flag table lifecycle) found = rewrite found in Refl

export
0 actualSupportedDependencies :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) -> (selected : name) -> (fiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} selected (registry state) = Just fiber) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected state = True) ->
  (allList (\wanted => providerFromPredicate {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} wanted
    (\actor => isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} actor state)
    (registryFibers {name = name} {key = key} {value = value} {world = world} {error = error} (registry state)))
    (dependencies (componentDependencies (fiberComponent fiber))) = True)
actualSupportedDependencies name key world error value nameEq keyEq state selected fiber found supported =
  snd (clauseAndParts _ _ (snd (clauseAndParts _ _
    (trans (sym (actualSupportClauseAtFiber name key world error value nameEq keyEq state
      (\actor => isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} actor state) selected fiber found))
      (trans (sym (supportSetIsSolution nameEq keyEq state selected)) supported)))))

export
0 actualSupportFromFacts :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) -> (selected : name) -> (fiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} selected (registry state) = Just fiber) ->
  (retired fiber = False) ->
  (supportClauseParent name (\actor => isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} actor state) (fiberParent fiber) = True) ->
  (allList (\wanted => providerFromPredicate {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} wanted
    (\actor => isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} actor state)
    (registryFibers {name = name} {key = key} {value = value} {world = world} {error = error} (registry state)))
    (dependencies (componentDependencies (fiberComponent fiber))) = True) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected state = True)
actualSupportFromFacts name key world error value nameEq keyEq state selected fiber found notRetired parentTrue dependenciesTrue =
  trans (supportSetIsSolution nameEq keyEq state selected)
    (trans (actualSupportClauseAtFiber name key world error value nameEq keyEq state
      (\actor => isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} actor state) selected fiber found)
      (clauseAndTrue _ _ (cong not notRetired) (clauseAndTrue _ _ parentTrue dependenciesTrue)))

0 clauseEntryKeyMember :
  (name, key, world, error : Type) -> (value : key -> Type) -> (selected : name) -> (fiber : Fiber name key value world error) ->
  (entries : List (Binding name (FiberAt name key value world error))) -> Elem (Bind selected fiber) entries -> Elem selected (bindingKeys entries)
clauseEntryKeyMember name key world error value selected fiber (_ :: rest) Here = Here
clauseEntryKeyMember name key world error value selected fiber (head :: rest) (There later) =
  There (clauseEntryKeyMember name key world error value selected fiber rest later)

0 clauseLookupFromEntry :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (entries : List (Binding name (FiberAt name key value world error))) -> UniqueKeys (bindingKeys entries) ->
  (selected : name) -> (fiber : Fiber name key value world error) -> Elem (Bind selected fiber) entries ->
  (lookupEntries {key = name} {value = FiberAt name key value world error} @{nameEq} selected entries = Just fiber)
clauseLookupFromEntry name key world error value nameEq (_ :: rest) unique selected fiber Here =
  case the (choice : Dec (selected = selected) ** (decEq @{nameEq} selected selected = choice)) (decEq @{nameEq} selected selected ** Refl) of
    (Yes same ** observed) => case same of Refl => rewrite observed in Refl
    (No different ** observed) => void (different Refl)
clauseLookupFromEntry name key world error value nameEq (Bind current observedFiber :: rest) (UniqueCons fresh tailUnique) selected fiber (There later) =
  case the (choice : Dec (selected = current) ** (decEq @{nameEq} selected current = choice)) (decEq @{nameEq} selected current ** Refl) of
    (Yes same ** observed) => case same of
      Refl => void (fresh (clauseEntryKeyMember name key world error value selected fiber rest later))
    (No different ** observed) => rewrite observed in clauseLookupFromEntry name key world error value nameEq rest tailUnique selected fiber later

0 clauseProviderEntryWitness :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (predicate : name -> Bool) -> (entries : List (Binding name (FiberAt name key value world error))) ->
  (providerFromPredicate {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} wanted predicate entries = True) ->
  (selected : name ** fiber : Fiber name key value world error **
    (Elem (Bind selected fiber) entries, predicate selected = True,
     listMember @{keyEq} wanted (dependencies (componentProvisions (fiberComponent fiber))) = True))
clauseProviderEntryWitness name key world error value nameEq keyEq wanted predicate [] exact = case exact of Refl impossible
clauseProviderEntryWitness name key world error value nameEq keyEq wanted predicate (Bind current observed :: rest) exact =
  case clauseOrCases (predicate current && listMember @{keyEq} wanted (dependencies (componentProvisions (fiberComponent observed))))
    (providerFromPredicate {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} wanted predicate rest) exact of
    Left headTrue => case clauseAndParts _ _ headTrue of
      (supported, declares) => (current ** observed ** (Here, supported, declares))
    Right tailTrue => case clauseProviderEntryWitness name key world error value nameEq keyEq wanted predicate rest tailTrue of
      (selected ** fiber ** (member, supported, declares)) => (selected ** fiber ** (There member, supported, declares))

export
0 actualProviderWitness :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) -> (wanted : key) -> (predicate : name -> Bool) ->
  (providerFromPredicate {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} wanted predicate
    (registryFibers {name = name} {key = key} {value = value} {world = world} {error = error} (registry state)) = True) ->
  (selected : name ** fiber : Fiber name key value world error **
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} selected (registry state) = Just fiber,
     predicate selected = True, listMember @{keyEq} wanted (dependencies (componentProvisions (fiberComponent fiber))) = True))
actualProviderWitness name key world error value nameEq keyEq (MkSystemState ambient (MkCoeffectContext entries unique)) wanted predicate exact =
  case clauseProviderEntryWitness name key world error value nameEq keyEq wanted predicate entries exact of
    (selected ** fiber ** (member, supported, declares)) =>
      (selected ** fiber ** (clauseLookupFromEntry name key world error value nameEq entries unique selected fiber member, supported, declares))

0 clauseProviderFromLookup :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) -> (wanted : key) -> (predicate : name -> Bool) ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  (lookupEntries {key = name} {value = FiberAt name key value world error} @{nameEq} selected entries = Just fiber) ->
  (predicate selected = True) -> (listMember @{keyEq} wanted (dependencies (componentProvisions (fiberComponent fiber))) = True) ->
  (providerFromPredicate {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} wanted predicate entries = True)
clauseProviderFromLookup name key world error value nameEq keyEq [] wanted predicate selected fiber found supported declares = case found of Refl impossible
clauseProviderFromLookup name key world error value nameEq keyEq (Bind current observedFiber :: rest) wanted predicate selected fiber found supported declares =
  case the (choice : Dec (selected = current) ** (decEq @{nameEq} selected current = choice)) (decEq @{nameEq} selected current ** Refl) of
    (Yes same ** observed) => case same of
      Refl => case justInjective (trans (sym (the
        (lookupEntries {key = name} {value = FiberAt name key value world error} @{nameEq} selected (Bind selected observedFiber :: rest) = Just observedFiber)
        (rewrite observed in Refl))) found) of
        Refl => clauseOrFromEither _ _ (Left (clauseAndTrue _ _ supported declares))
    (No different ** observed) => clauseOrFromEither _ _ (Right
      (clauseProviderFromLookup name key world error value nameEq keyEq rest wanted predicate selected fiber
        (trans (sym (the
          (lookupEntries {key = name} {value = FiberAt name key value world error} @{nameEq} selected (Bind current observedFiber :: rest) =
           lookupEntries {key = name} {value = FiberAt name key value world error} @{nameEq} selected rest)
          (rewrite observed in Refl))) found) supported declares))

export
0 actualProviderFromFacts :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) -> (wanted : key) -> (predicate : name -> Bool) ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} selected (registry state) = Just fiber) ->
  (predicate selected = True) -> (listMember @{keyEq} wanted (dependencies (componentProvisions (fiberComponent fiber))) = True) ->
  (providerFromPredicate {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} wanted predicate
    (registryFibers {name = name} {key = key} {value = value} {world = world} {error = error} (registry state)) = True)
actualProviderFromFacts name key world error value nameEq keyEq (MkSystemState ambient (MkCoeffectContext entries unique)) =
  clauseProviderFromLookup name key world error value nameEq keyEq entries

0 clauseListMemberTrueElem : (element : Type) -> (equal : DecEq element) -> (selected : element) -> (items : List element) ->
  (listMember @{equal} selected items = True) -> Elem selected items
clauseListMemberTrueElem element equal selected [] exact = case exact of Refl impossible
clauseListMemberTrueElem element equal selected (current :: rest) exact =
  case the (choice : Dec (selected = current) ** (decEq @{equal} selected current = choice)) (decEq @{equal} selected current ** Refl) of
    (Yes same ** observed) => case same of Refl => Here
    (No different ** observed) => There (clauseListMemberTrueElem element equal selected rest
      (trans (sym (the (listMember @{equal} selected (current :: rest) = listMember @{equal} selected rest) (rewrite observed in Refl))) exact))

||| INTERNAL proof package for precisely the separately established static and
||| retirement facts. Accepted producers build it; O18 gains NO such premise.
public export
record SupportedClauseTransport
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (0 source, target : SystemState name key value world error)
  (0 renaming : name -> name) where
  constructor MkSupportedClauseTransport
  0 clauseImage : (selected : name) -> (sourceFiber : Fiber name key value world error) ->
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} selected (registry source) = Just sourceFiber) ->
    (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected source = True) ->
    (targetFiber : Fiber name key value world error **
      (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} (renaming selected) (registry target) = Just targetFiber,
       fiberComponent targetFiber = fiberComponent sourceFiber,
       fiberParent targetFiber = supportMapParent name renaming (fiberParent sourceFiber)))
  0 clauseImageNotRetired : (selected : name) ->
    (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected source = True) ->
    (targetFiber : Fiber name key value world error) ->
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} (renaming selected) (registry target) = Just targetFiber) ->
    (retired targetFiber = False)

0 supportedDependencyTransport :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (source, target : SystemState name key value world error) -> (renaming : name -> name) ->
  SupportedClauseTransport name key world error value nameEq keyEq source target renaming ->
  (selected : name) -> (sourceFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} selected (registry source) = Just sourceFiber) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected source = True) ->
  ((lower : name) -> SupportEdge nameEq source lower selected ->
    (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} lower source = True) ->
    (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} (renaming lower) target = True)) ->
  (wanted : key) -> Elem wanted (dependencies (componentDependencies (fiberComponent sourceFiber))) ->
  (providerFromPredicate {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} wanted
    (\actor => isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} actor target)
    (registryFibers {name = name} {key = key} {value = value} {world = world} {error = error} (registry target)) = True)
supportedDependencyTransport name key world error value nameEq keyEq source target renaming transport selected sourceFiber sourceFound supported recursive wanted needed =
  case actualProviderWitness name key world error value nameEq keyEq source wanted
    (\actor => isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} actor source)
    (clauseAllListAt key (\dependency => providerFromPredicate {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} dependency
      (\actor => isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} actor source)
      (registryFibers {name = name} {key = key} {value = value} {world = world} {error = error} (registry source)))
      (dependencies (componentDependencies (fiberComponent sourceFiber))) wanted needed
      (actualSupportedDependencies name key world error value nameEq keyEq source selected sourceFiber sourceFound supported)) of
    (provider ** providerFiber ** (providerFound, providerSupported, providerDeclares)) =>
      case clauseImage transport provider providerFiber providerFound providerSupported of
        (imageFiber ** (imageFound, componentsSame, parentsSame)) =>
          actualProviderFromFacts name key world error value nameEq keyEq target wanted
            (\actor => isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} actor target)
            (renaming provider) imageFiber imageFound
            (recursive provider (SupportPrecedence (MkPrecedenceEdge wanted providerFiber sourceFiber providerFound sourceFound
              (clauseListMemberTrueElem key keyEq wanted (dependencies (componentProvisions (fiberComponent providerFiber))) providerDeclares) needed)) providerSupported)
            (trans (cong (\component => listMember @{keyEq} wanted (dependencies (componentProvisions component))) componentsSame) providerDeclares)
