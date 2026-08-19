module DGamma.CP4DeletionSelectedForeignLifecycleAnchorOpen

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4SupportSolution
import DGamma.CP4SupportQuiescence
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorCore
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

0 falseNotTrueOpenAnchor : False = True -> Void
falseNotTrueOpenAnchor Refl impossible

0 boolAndLeftTrueOpenAnchor :
  (left, right : Bool) -> left && right = True -> left = True
boolAndLeftTrueOpenAnchor False right same = case same of Refl impossible
boolAndLeftTrueOpenAnchor True right same = Refl

0 boolAndRightTrueOpenAnchor :
  (left, right : Bool) -> left && right = True -> right = True
boolAndRightTrueOpenAnchor False right same = case same of Refl impossible
boolAndRightTrueOpenAnchor True False same = case same of Refl impossible
boolAndRightTrueOpenAnchor True True same = Refl

0 boolNotAndTrueOpenAnchor :
  (observed : Bool) -> not observed = True -> observed = True -> Void
boolNotAndTrueOpenAnchor False notTrue observedTrue =
  void (falseNotTrueOpenAnchor observedTrue)
boolNotAndTrueOpenAnchor True notTrue observedTrue =
  void (falseNotTrueOpenAnchor notTrue)

0 boolOrTrueOpenAnchor :
  (left, right : Bool) -> left || right = True ->
  Either (left = True) (right = True)
boolOrTrueOpenAnchor False False same = case same of Refl impossible
boolOrTrueOpenAnchor False True same = Right Refl
boolOrTrueOpenAnchor True right same = Left Refl

0 listMemberFromElemOpenAnchor : DecEq a =>
  (wanted : a) -> (values : List a) -> Elem wanted values ->
  listMember wanted values = True
listMemberFromElemOpenAnchor wanted (wanted :: rest) Here
  with (decEq wanted wanted)
  listMemberFromElemOpenAnchor wanted (wanted :: rest) Here | Yes Refl = Refl
  listMemberFromElemOpenAnchor wanted (wanted :: rest) Here | No contra =
    void (contra Refl)
listMemberFromElemOpenAnchor wanted (current :: rest) (There later)
  with (decEq wanted current)
  listMemberFromElemOpenAnchor current (current :: rest) (There later) |
    Yes Refl = Refl
  listMemberFromElemOpenAnchor wanted (current :: rest) (There later) |
    No distinct = listMemberFromElemOpenAnchor wanted rest later

0 listMemberTrueElemOpenAnchor :
  (dec : DecEq a) -> (wanted : a) -> (values : List a) ->
  listMember @{dec} wanted values = True -> Elem wanted values
listMemberTrueElemOpenAnchor dec wanted [] present =
  case present of Refl impossible
listMemberTrueElemOpenAnchor dec wanted (current :: rest) present
  with (decEq @{dec} wanted current)
  listMemberTrueElemOpenAnchor dec current (current :: rest) present |
    Yes Refl = Here
  listMemberTrueElemOpenAnchor dec wanted (current :: rest) present |
    No distinct = There (listMemberTrueElemOpenAnchor dec wanted rest present)

0 elemDecFromElemOpenAnchor : DecEq a =>
  (wanted : a) -> (values : List a) -> Elem wanted values ->
  elemDec wanted values = True
elemDecFromElemOpenAnchor wanted (wanted :: rest) Here
  with (decEq wanted wanted)
  elemDecFromElemOpenAnchor wanted (wanted :: rest) Here | Yes Refl = Refl
  elemDecFromElemOpenAnchor wanted (wanted :: rest) Here | No contra =
    void (contra Refl)
elemDecFromElemOpenAnchor wanted (current :: rest) (There later)
  with (decEq wanted current)
  elemDecFromElemOpenAnchor current (current :: rest) (There later) |
    Yes Refl = Refl
  elemDecFromElemOpenAnchor wanted (current :: rest) (There later) |
    No distinct = elemDecFromElemOpenAnchor wanted rest later

0 foldlOrTrueOpenAnchor :
  (predicate : a -> Bool) -> (values : List a) ->
  foldl (\accepted, value => accepted || predicate value) True values = True
foldlOrTrueOpenAnchor predicate [] = Refl
foldlOrTrueOpenAnchor predicate (value :: rest) =
  foldlOrTrueOpenAnchor predicate rest

0 sharedAnyOpenAnchor : DecEq key =>
  (wanted : key) -> (left, right : List key) ->
  Elem wanted left -> Elem wanted right ->
  any (\candidate => elemDec candidate right) left = True
sharedAnyOpenAnchor wanted (wanted :: leftRest) right Here rightMember =
  rewrite elemDecFromElemOpenAnchor wanted right rightMember in
    foldlOrTrueOpenAnchor (\candidate => elemDec candidate right) leftRest
sharedAnyOpenAnchor wanted (current :: leftRest) right (There later) rightMember
  with (elemDec current right)
  sharedAnyOpenAnchor wanted (current :: leftRest) right (There later)
    rightMember | True =
      foldlOrTrueOpenAnchor (\candidate => elemDec candidate right) leftRest
  sharedAnyOpenAnchor wanted (current :: leftRest) right (There later)
    rightMember | False = sharedAnyOpenAnchor wanted leftRest right later rightMember

0 sharedProvisionOverlapsOpenAnchor :
  (keyEq : DecEq key) -> (wanted : key) ->
  (left, right : CoeffectSpec key) ->
  Elem wanted (dependencies left) -> Elem wanted (dependencies right) ->
  provisionOverlap @{keyEq} left right = True
sharedProvisionOverlapsOpenAnchor keyEq wanted
  (MkCoeffectSpec left leftUnique) (MkCoeffectSpec right rightUnique)
  leftMember rightMember = sharedAnyOpenAnchor wanted left right leftMember
    rightMember

0 sharedProvisionRejectsDisjointOpenAnchor :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (keyEq : DecEq key) -> (wanted : key) ->
  (provision : CoeffectSpec key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  provisionsDisjointFrom @{keyEq} {value = value} {world = world}
    {error = error} provision entries = True ->
  Elem wanted (dependencies provision) ->
  (providerName : name) ->
  (providerFiber : Fiber name key value world error) ->
  Elem (Bind providerName providerFiber) entries ->
  Elem wanted (dependencies
    (componentProvisions (fiberComponent providerFiber))) -> Void
sharedProvisionRejectsDisjointOpenAnchor keyEq wanted provision
  (Bind providerName providerFiber :: rest) disjoint provisionMember
  providerName providerFiber Here providerMember =
    let 0 headNotOverlap : (not (provisionOverlap @{keyEq} provision
          (componentProvisions (fiberComponent providerFiber))) = True)
        headNotOverlap = boolAndLeftTrueOpenAnchor
          (not (provisionOverlap @{keyEq} provision
            (componentProvisions (fiberComponent providerFiber))))
          (provisionsDisjointFrom @{keyEq} provision rest) disjoint
        0 overlaps : (provisionOverlap @{keyEq} provision
          (componentProvisions (fiberComponent providerFiber)) = True)
        overlaps = sharedProvisionOverlapsOpenAnchor keyEq wanted provision
          (componentProvisions (fiberComponent providerFiber)) provisionMember
          providerMember
    in boolNotAndTrueOpenAnchor
      (provisionOverlap @{keyEq} provision
        (componentProvisions (fiberComponent providerFiber)))
      headNotOverlap overlaps
sharedProvisionRejectsDisjointOpenAnchor keyEq wanted provision
  (Bind current currentFiber :: rest) disjoint provisionMember
  providerName providerFiber (There later) providerMember =
    sharedProvisionRejectsDisjointOpenAnchor keyEq wanted provision rest
      (boolAndRightTrueOpenAnchor
        (not (provisionOverlap @{keyEq} provision
          (componentProvisions (fiberComponent currentFiber))))
        (provisionsDisjointFrom @{keyEq} provision rest) disjoint)
      provisionMember providerName providerFiber later providerMember

public export
0 pairwiseSharedProvisionSameName :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  pairwiseProvisionInvariant @{keyEq} {value = value} {world = world}
    {error = error} entries = True ->
  (leftName, rightName : name) ->
  (leftFiber, rightFiber : Fiber name key value world error) ->
  Elem (Bind leftName leftFiber) entries ->
  Elem (Bind rightName rightFiber) entries ->
  (wanted : key) ->
  Elem wanted (dependencies
    (componentProvisions (fiberComponent leftFiber))) ->
  Elem wanted (dependencies
    (componentProvisions (fiberComponent rightFiber))) ->
  leftName = rightName
pairwiseSharedProvisionSameName keyEq
  (Bind leftName leftFiber :: rest) pairwise leftName leftName leftFiber leftFiber
  Here Here wanted leftDeclares rightDeclares = Refl
pairwiseSharedProvisionSameName keyEq
  (Bind leftName leftFiber :: rest) pairwise leftName rightName leftFiber rightFiber
  Here (There rightLater) wanted leftDeclares rightDeclares =
    void (sharedProvisionRejectsDisjointOpenAnchor keyEq wanted
      (componentProvisions (fiberComponent leftFiber)) rest
      (boolAndLeftTrueOpenAnchor
        (provisionsDisjointFrom @{keyEq}
          (componentProvisions (fiberComponent leftFiber)) rest)
        (pairwiseProvisionInvariant @{keyEq} rest) pairwise)
      leftDeclares rightName rightFiber rightLater rightDeclares)
pairwiseSharedProvisionSameName keyEq
  (Bind rightName rightFiber :: rest) pairwise leftName rightName leftFiber
  rightFiber (There leftLater) Here wanted leftDeclares rightDeclares =
    void (sharedProvisionRejectsDisjointOpenAnchor keyEq wanted
      (componentProvisions (fiberComponent rightFiber)) rest
      (boolAndLeftTrueOpenAnchor
        (provisionsDisjointFrom @{keyEq}
          (componentProvisions (fiberComponent rightFiber)) rest)
        (pairwiseProvisionInvariant @{keyEq} rest) pairwise)
      rightDeclares leftName leftFiber leftLater leftDeclares)
pairwiseSharedProvisionSameName keyEq
  (Bind current currentFiber :: rest) pairwise leftName rightName leftFiber
  rightFiber (There leftLater) (There rightLater) wanted leftDeclares
  rightDeclares = pairwiseSharedProvisionSameName keyEq rest
    (boolAndRightTrueOpenAnchor
      (provisionsDisjointFrom @{keyEq}
        (componentProvisions (fiberComponent currentFiber)) rest)
      (pairwiseProvisionInvariant @{keyEq} rest) pairwise)
    leftName rightName leftFiber rightFiber leftLater rightLater wanted
    leftDeclares rightDeclares

public export
0 lookupEntryElemOpenAnchor :
  (nameEq : DecEq name) -> (selected : name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (fiber : Fiber name key value world error) ->
  lookupEntries @{nameEq} selected entries = Just fiber ->
  Elem (Bind selected fiber) entries
lookupEntryElemOpenAnchor nameEq selected [] fiber found =
  case found of Refl impossible
lookupEntryElemOpenAnchor nameEq selected
  (Bind current observed :: rest) fiber found
  with (decEq @{nameEq} selected current)
  lookupEntryElemOpenAnchor nameEq current
    (Bind current observed :: rest) fiber found | Yes Refl =
      case justInjective found of Refl => Here
  lookupEntryElemOpenAnchor nameEq selected
    (Bind current observed :: rest) fiber found | No distinct =
      There (lookupEntryElemOpenAnchor nameEq selected rest fiber found)

record PredicateProvisionProvider
  (name, key, world, error : Type) (value : key -> Type)
  (predicate : name -> Bool) (wanted : key)
  (entries : List (Binding name (FiberAt name key value world error))) where
  constructor MkPredicateProvisionProvider
  predicateProviderName : name
  predicateProviderFiber : Fiber name key value world error
  predicateProviderEntry : Elem
    (Bind predicateProviderName predicateProviderFiber) entries
  predicateProviderAccepted : predicate predicateProviderName = True
  predicateProviderDeclares : Elem wanted (dependencies
    (componentProvisions (fiberComponent predicateProviderFiber)))

0 providerFromPredicateWitness :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (predicate : name -> Bool) -> (wanted : key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  providerFromPredicate @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} wanted predicate entries = True ->
  PredicateProvisionProvider name key world error value predicate wanted entries
providerFromPredicateWitness nameEq keyEq predicate wanted [] present =
  case present of Refl impossible
providerFromPredicateWitness nameEq keyEq predicate wanted
  (Bind current fiber :: rest) present =
    case boolOrTrueOpenAnchor
      (predicate current && listMember @{keyEq} wanted
        (dependencies (componentProvisions (fiberComponent fiber))))
      (providerFromPredicate @{nameEq} @{keyEq} wanted predicate rest)
      present of
      Left headTrue => MkPredicateProvisionProvider current fiber Here
        (boolAndLeftTrueOpenAnchor (predicate current)
          (listMember @{keyEq} wanted
            (dependencies (componentProvisions (fiberComponent fiber))))
          headTrue)
        (listMemberTrueElemOpenAnchor keyEq wanted
          (dependencies (componentProvisions (fiberComponent fiber)))
          (boolAndRightTrueOpenAnchor (predicate current)
            (listMember @{keyEq} wanted
              (dependencies (componentProvisions (fiberComponent fiber))))
            headTrue))
      Right tailTrue =>
        case providerFromPredicateWitness nameEq keyEq predicate wanted rest
          tailTrue of
          MkPredicateProvisionProvider provider providerFiber entry accepted
            declares => MkPredicateProvisionProvider provider providerFiber
              (There entry) accepted declares

0 allListElemTrueOpenAnchor :
  (predicate : a -> Bool) -> (values : List a) -> (wanted : a) ->
  Elem wanted values -> allList predicate values = True -> predicate wanted = True
allListElemTrueOpenAnchor predicate (wanted :: rest) wanted Here allTrue =
  boolAndLeftTrueOpenAnchor (predicate wanted) (allList predicate rest) allTrue
allListElemTrueOpenAnchor predicate (current :: rest) wanted (There later)
  allTrue = allListElemTrueOpenAnchor predicate rest wanted later
    (boolAndRightTrueOpenAnchor (predicate current) (allList predicate rest)
      allTrue)

0 supportClauseProvidersAtFoundOpenAnchor :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (predicate : name -> Bool) -> (actor : name) ->
  (state : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor (registry state) = Just fiber ->
  supportClause @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} predicate actor state = True ->
  allList (\wanted => providerFromPredicate @{nameEq} @{keyEq}
    {value = value} {world = world} {error = error} wanted predicate
    (registryFibers {value = value} {world = world} {error = error}
      (registry state)))
    (dependencies (componentDependencies (fiberComponent fiber))) = True
supportClauseProvidersAtFoundOpenAnchor {name} {value} {world} {error}
  nameEq keyEq predicate actor
  state@(MkSystemState ambient (MkCoeffectContext entries unique))
  fiber@(MkFiber component Root retiredFlag table lifecycle) found clauseTrue =
    let 0 shape = supportClauseAtFoundQ nameEq keyEq predicate actor ambient
          entries unique component Root retiredFlag table lifecycle found
        0 expanded : (not retiredFlag &&
          (True && providerClausesFor name key world error value nameEq keyEq
            predicate entries
            (dependencies (componentDependencies component))) = True)
        expanded = trans (sym shape) clauseTrue
    in boolAndRightTrueOpenAnchor True
      (providerClausesFor name key world error value nameEq keyEq predicate
        entries (dependencies (componentDependencies component)))
      (boolAndRightTrueOpenAnchor (not retiredFlag)
        (True && providerClausesFor name key world error value nameEq keyEq
          predicate entries (dependencies (componentDependencies component)))
        expanded)
supportClauseProvidersAtFoundOpenAnchor {name} {value} {world} {error}
  nameEq keyEq predicate actor
  state@(MkSystemState ambient (MkCoeffectContext entries unique))
  fiber@(MkFiber component (ChildOf parent) retiredFlag table lifecycle) found
  clauseTrue =
    let 0 shape = supportClauseAtFoundQ nameEq keyEq predicate actor ambient
          entries unique component (ChildOf parent) retiredFlag table lifecycle
          found
        0 expanded : (not retiredFlag &&
          (predicate parent && providerClausesFor name key world error value
            nameEq keyEq predicate entries
            (dependencies (componentDependencies component))) = True)
        expanded = trans (sym shape) clauseTrue
    in boolAndRightTrueOpenAnchor (predicate parent)
      (providerClausesFor name key world error value nameEq keyEq predicate
        entries (dependencies (componentDependencies component)))
      (boolAndRightTrueOpenAnchor (not retiredFlag)
        (predicate parent && providerClausesFor name key world error value
          nameEq keyEq predicate entries
          (dependencies (componentDependencies component))) expanded)

public export
0 registryWellFormedPairwiseOpenAnchor :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} state = True ->
  pairwiseProvisionInvariant @{keyEq} {value = value} {world = world}
    {error = error}
    (registryFibers {value = value} {world = world} {error = error}
      (registry state)) = True
registryWellFormedPairwiseOpenAnchor nameEq keyEq
  state@(MkSystemState ambient fibers) wellFormed =
    boolAndLeftTrueOpenAnchor
      (pairwiseProvisionInvariant @{keyEq} (registryFibers fibers))
      (viewsInvariant @{nameEq} @{keyEq} (registryFibers fibers) fibers)
      (boolAndRightTrueOpenAnchor
        (chainsInvariant (S (length (registryFibers fibers)))
          (registryFibers fibers) fibers)
        (pairwiseProvisionInvariant @{keyEq} (registryFibers fibers) &&
          viewsInvariant @{nameEq} @{keyEq} (registryFibers fibers) fibers)
        (boolAndRightTrueOpenAnchor
          (parentsInvariant @{nameEq} (registryFibers fibers) fibers)
          (chainsInvariant (S (length (registryFibers fibers)))
            (registryFibers fibers) fibers &&
            pairwiseProvisionInvariant @{keyEq} (registryFibers fibers) &&
            viewsInvariant @{nameEq} @{keyEq} (registryFibers fibers) fibers)
          wellFormed))

public export
0 memberKeyTrueElemOpenAnchor :
  (keyEq : DecEq key) -> (wanted : key) ->
  (table : CoeffectContext key value) ->
  memberKey @{keyEq} wanted table = True ->
  Elem wanted (bindingKeys (bindings table))
memberKeyTrueElemOpenAnchor keyEq wanted (MkCoeffectContext entries unique)
  present with (lookupEntries @{keyEq} wanted entries) proof found
  memberKeyTrueElemOpenAnchor keyEq wanted
    (MkCoeffectContext entries unique) present | Nothing =
      case present of Refl impossible
  memberKeyTrueElemOpenAnchor keyEq wanted
    (MkCoeffectContext entries unique) present | Just observed =
      lookupJustElem @{keyEq} wanted entries observed found

0 supportedActiveAtFoundOpenAnchor :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry state) = Just fiber ->
  supportedActiveAt @{nameEq} selected state =
    isActive (fiberLifecycle fiber)
supportedActiveAtFoundOpenAnchor nameEq selected state fiber found =
  rewrite found in Refl

||| Lemma-70 branch of the lifecycle anchor.  If the foreign activation is
||| still open at the quiet endpoint, it is Active and supported.  Its support
||| clause chooses an Active declared provider for every dependency.  Pairwise
||| provision disjointness makes that provider unique, so a current selected
||| table overlap would force the selected endpoint fiber to be Active,
||| contradicting the selected closing episode's Inactive endpoint.
public export
0 openForeignLifecycleProviderExcluded :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) ->
  (global : Transitions initial finalState) ->
  (currentSelected, currentOwner : Fiber name key value world error) ->
  (finalSelected, finalOwner : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry finalState) = Just finalSelected ->
  lookupFiber @{nameEq} actor (registry finalState) = Just finalOwner ->
  fiberComponent finalSelected = fiberComponent currentSelected ->
  fiberComponent finalOwner = fiberComponent currentOwner ->
  isActive (fiberLifecycle finalSelected) = False ->
  isActive (fiberLifecycle finalOwner) = True ->
  registryWellFormed @{nameEq} @{keyEq} finalState = True ->
  SupportMatchesActive nameEq keyEq finalState ->
  (wanted : key) ->
  Elem wanted (dependencies
    (componentDependencies (fiberComponent currentOwner))) ->
  providerCandidate @{keyEq} wanted currentSelected = False
openForeignLifecycleProviderExcluded nameEq keyEq selected actor global
  currentSelected currentOwner finalSelected finalOwner selectedFound ownerFound
  selectedComponent ownerComponent selectedInactive ownerActive finalWellFormed
  supportMatches wanted ownerDeclares
  with (providerCandidate @{keyEq} wanted currentSelected) proof candidate
  openForeignLifecycleProviderExcluded nameEq keyEq selected actor global
    currentSelected currentOwner finalSelected finalOwner selectedFound ownerFound
    selectedComponent ownerComponent selectedInactive ownerActive finalWellFormed
    supportMatches wanted ownerDeclares | False = Refl
  openForeignLifecycleProviderExcluded nameEq keyEq selected actor global
    currentSelected currentOwner finalSelected finalOwner selectedFound ownerFound
    selectedComponent ownerComponent selectedInactive ownerActive finalWellFormed
    supportMatches wanted ownerDeclares | True =
      let 0 currentMember : (memberKey @{keyEq} wanted
            (ownedValues (fiberTable currentSelected)) = True)
          currentMember = boolAndRightTrueOpenAnchor
            (isActive (fiberLifecycle currentSelected))
            (memberKey @{keyEq} wanted
              (ownedValues (fiberTable currentSelected))) candidate
          0 currentTableMember : Elem wanted
            (bindingKeys (bindings
              (ownedValues (fiberTable currentSelected))))
          currentTableMember = memberKeyTrueElemOpenAnchor keyEq wanted
            (ownedValues (fiberTable currentSelected)) currentMember
          0 currentSelectedDeclares : Elem wanted (dependencies
            (componentProvisions (fiberComponent currentSelected)))
          currentSelectedDeclares = ownedSound (fiberTable currentSelected)
            wanted currentTableMember
          0 finalSelectedDeclares : Elem wanted (dependencies
            (componentProvisions (fiberComponent finalSelected)))
          finalSelectedDeclares = replace
            {p = \component => Elem wanted
              (dependencies (componentProvisions component))}
            (sym selectedComponent) currentSelectedDeclares
          0 finalOwnerDeclares : Elem wanted (dependencies
            (componentDependencies (fiberComponent finalOwner)))
          finalOwnerDeclares = replace
            {p = \component => Elem wanted
              (dependencies (componentDependencies component))}
            (sym ownerComponent) ownerDeclares
          0 ownerActiveAt : supportedActiveAt @{nameEq} actor finalState = True
          ownerActiveAt = trans
            (supportedActiveAtFoundOpenAnchor nameEq actor finalState finalOwner
              ownerFound)
            ownerActive
          0 ownerSupported : isSupported @{nameEq} @{keyEq} actor finalState = True
          ownerSupported = trans (supportMatches actor) ownerActiveAt
          0 ownerClause : (supportClause @{nameEq} @{keyEq}
            {value = value} {world = world} {error = error}
            (\current => isSupported @{nameEq} @{keyEq} current finalState)
            actor finalState = True)
          ownerClause = trans
            (sym (supportSetIsSolution nameEq keyEq finalState actor))
            ownerSupported
          0 providerClauses : (allList
            (\dependency => providerFromPredicate @{nameEq} @{keyEq}
              {value = value} {world = world} {error = error} dependency
              (\current => isSupported @{nameEq} @{keyEq} current finalState)
              (registryFibers {value = value} {world = world} {error = error}
                (registry finalState)))
            (dependencies
              (componentDependencies (fiberComponent finalOwner))) = True)
          providerClauses = supportClauseProvidersAtFoundOpenAnchor nameEq keyEq
            (\current => isSupported @{nameEq} @{keyEq} current finalState)
            actor finalState finalOwner ownerFound ownerClause
          0 wantedProvider : (providerFromPredicate @{nameEq} @{keyEq}
            {value = value} {world = world} {error = error} wanted
            (\current => isSupported @{nameEq} @{keyEq} current finalState)
            (registryFibers {value = value} {world = world} {error = error}
              (registry finalState)) = True)
          wantedProvider = allListElemTrueOpenAnchor
            (\dependency => providerFromPredicate @{nameEq} @{keyEq} dependency
              (\current => isSupported @{nameEq} @{keyEq} current finalState)
              (registryFibers (registry finalState)))
            (dependencies
              (componentDependencies (fiberComponent finalOwner))) wanted
            finalOwnerDeclares providerClauses
          0 providerWitness : PredicateProvisionProvider name key world error
            value (\current => isSupported @{nameEq} @{keyEq} current finalState)
            wanted (registryFibers {value = value} {world = world}
              {error = error} (registry finalState))
          providerWitness = providerFromPredicateWitness nameEq keyEq
            (\current => isSupported @{nameEq} @{keyEq} current finalState)
            wanted (registryFibers {value = value} {world = world}
              {error = error} (registry finalState)) wantedProvider
          0 pairwise : (pairwiseProvisionInvariant @{keyEq}
            {value = value} {world = world} {error = error}
            (registryFibers {value = value} {world = world} {error = error}
              (registry finalState)) = True)
          pairwise = registryWellFormedPairwiseOpenAnchor nameEq keyEq
            finalState finalWellFormed
      in case providerWitness of
        MkPredicateProvisionProvider provider providerFiber providerEntry
          providerSupported providerDeclares =>
            let 0 selectedEntry : Elem (Bind selected finalSelected)
                  (registryFibers (registry finalState))
                selectedEntry = lookupEntryElemOpenAnchor nameEq selected
                  (registryFibers (registry finalState)) finalSelected
                  (lookupFiberEntries nameEq selected finalSelected
                    (registry finalState) selectedFound)
                0 providerIsSelected : selected = provider
                providerIsSelected = pairwiseSharedProvisionSameName keyEq
                  (registryFibers (registry finalState)) pairwise selected
                  provider finalSelected providerFiber selectedEntry providerEntry
                  wanted finalSelectedDeclares providerDeclares
                0 selectedSupported : isSupported @{nameEq} @{keyEq} selected
                  finalState = True
                selectedSupported = replace
                  {p = \current => isSupported @{nameEq} @{keyEq} current
                    finalState = True}
                  (sym providerIsSelected) providerSupported
                0 selectedActiveAt : supportedActiveAt @{nameEq} selected
                  finalState = True
                selectedActiveAt = trans (sym (supportMatches selected))
                  selectedSupported
                0 selectedActive : isActive (fiberLifecycle finalSelected) = True
                selectedActive = trans
                  (sym (supportedActiveAtFoundOpenAnchor nameEq selected
                    finalState finalSelected selectedFound)) selectedActiveAt
            in void (falseNotTrueOpenAnchor
              (trans (sym selectedInactive) selectedActive))
