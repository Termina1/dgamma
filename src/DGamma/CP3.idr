module DGamma.CP3

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

public export
listMember : DecEq a => a -> List a -> Bool
listMember wanted [] = False
listMember wanted (current :: rest) = case decEq wanted current of
  Yes Refl => True
  No _ => listMember wanted rest

%default total

public export
0 listMemberEmpty : (nameEq : DecEq name) -> (selected : name) ->
  listMember @{nameEq} selected [] = False
listMemberEmpty nameEq selected = Refl

||| Definition 65. `provider` precedes `consumer` when a key the former may
||| provide is declared by the latter. This is the finite executable graph used
||| by the Progress and Confluence statements.
public export
precedesFiber : DecEq key =>
  Fiber name key value world error -> Fiber name key value world error -> Bool
precedesFiber provider consumer = any declaredByConsumer
  (dependencies (componentProvisions (fiberComponent provider)))
  where
  declaredByConsumer : key -> Bool
  declaredByConsumer k = listMember k
    (dependencies (componentDependencies (fiberComponent consumer)))

public export
precedesAt : DecEq name => DecEq key => name -> name ->
  SystemState name key value world error -> Bool
precedesAt provider consumer state =
  case lookupFiber provider (registry state) of
    Nothing => False
    Just providerFiber => case lookupFiber consumer (registry state) of
      Nothing => False
      Just consumerFiber => precedesFiber providerFiber consumerFiber

||| One concrete edge of Definition 65. Keeping the witnesses makes later
||| acyclicity and transposition lemmas independent of Boolean reflection.
public export
record PrecedenceEdge {name, key, world, error : Type} {value : key -> Type}
  (nameEq : DecEq name) (provider, consumer : name)
  (state : SystemState name key value world error) where
  constructor MkPrecedenceEdge
  edgeKey : key
  providerFiber : Fiber name key value world error
  consumerFiber : Fiber name key value world error
  providerFound : lookupFiber @{nameEq} provider (registry state) = Just providerFiber
  consumerFound : lookupFiber @{nameEq} consumer (registry state) = Just consumerFiber
  providerDeclares : Elem edgeKey
    (dependencies (componentProvisions (fiberComponent providerFiber)))
  consumerDeclares : Elem edgeKey
    (dependencies (componentDependencies (fiberComponent consumerFiber)))

public export
data PrecedencePath : {name, key, world, error : Type} ->
  {value : key -> Type} -> (nameEq : DecEq name) ->
  (state : SystemState name key value world error) -> name -> name -> Type where
  PrecedenceOne : PrecedenceEdge nameEq from to state ->
    PrecedencePath nameEq state from to
  PrecedenceMore : PrecedenceEdge nameEq from middle state ->
    PrecedencePath nameEq state middle to ->
    PrecedencePath nameEq state from to

||| Paper's acyclicity hypothesis, stated directly on the finite registry.
public export
PrecedenceAcyclic : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> SystemState name key value world error -> Type
PrecedenceAcyclic {name} nameEq state =
  (n : name) -> PrecedencePath nameEq state n n -> Void

||| Parent half of paper Equation 62: the parent is immediately below the
||| registered child in the support relation.
public export
record ParentSupportEdge {name, key, world, error : Type} {value : key -> Type}
  (nameEq : DecEq name) (parent, child : name)
  (state : SystemState name key value world error) where
  constructor MkParentSupportEdge
  childFiber : Fiber name key value world error
  childFound : lookupFiber @{nameEq} child (registry state) = Just childFiber
  childParent : fiberParent childFiber = ChildOf parent

||| Definition 67 / Equation 62, including both provision precedence and the
||| immediate parent-registration edge.
public export
data SupportEdge : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (state : SystemState name key value world error) ->
  name -> name -> Type where
  SupportPrecedence : PrecedenceEdge nameEq lower upper state ->
    SupportEdge nameEq state lower upper
  SupportParent : ParentSupportEdge nameEq lower upper state ->
    SupportEdge nameEq state lower upper

||| Nonempty transitive closure of Equation 62.
public export
data SupportPath : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (state : SystemState name key value world error) ->
  name -> name -> Type where
  SupportPathOne : SupportEdge nameEq state from to ->
    SupportPath nameEq state from to
  SupportPathMore : SupportEdge nameEq state from middle ->
    SupportPath nameEq state middle to -> SupportPath nameEq state from to

||| On the finite registry, absence of a cycle is the executable
||| well-foundedness certificate used by Lemma 68.
public export
SupportWellFounded : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> SystemState name key value world error -> Type
SupportWellFounded {name} nameEq state =
  (n : name) -> SupportPath nameEq state n n -> Void

||| Strict occurrence order in a finite trace/action list.
public export
data BeforeIn : a -> a -> List a -> Type where
  BeforeHere : Elem later rest -> BeforeIn earlier later (earlier :: rest)
  BeforeThere : BeforeIn earlier later rest ->
    BeforeIn earlier later (other :: rest)

public export
data ActionOccurs :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  Action name key value world error -> Transitions first finalState -> Type where
  ActionOccursHere :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    transitionAction transition = action ->
    ActionOccurs action (MoreTransitions transition rest)
  ActionOccursLater :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    ActionOccurs action rest ->
    ActionOccurs action (MoreTransitions transition rest)

public export
data ActionBefore :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  Action name key value world error -> Action name key value world error ->
  Transitions first finalState -> Type where
  ActionBeforeHere :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    transitionAction transition = earlier ->
    ActionOccurs later rest ->
    ActionBefore earlier later (MoreTransitions transition rest)
  ActionBeforeLater :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    ActionBefore earlier later rest ->
    ActionBefore earlier later (MoreTransitions transition rest)

||| A deterministic finite-host catalog for the optional registration tag
||| carried by `StepEffect`. Sharing this catalog between traces fixes the child
||| component and continuation while leaving only the fresh name abstract.
public export
record RegistrationProtocol (key : Type) (value : key -> Type)
  (world, error : Type) where
  constructor MkRegistrationProtocol
  registrationCatalog : Nat -> Maybe (Component key value world error)
  ||| Components admitted to a disciplined trace receive a static rank. `Nothing`
  ||| leaves unrelated host components outside this protocol.
  registrationRank : Component key value world error -> Maybe Nat
  0 yieldedRankIncreases :
    (parent, child : Component key value world error) ->
    (step : StepEffect key value world error
      (dependencies (componentDependencies parent))
      (componentProvisions parent)) ->
    (tag, parentRank, childRank : Nat) ->
    Elem step (componentProgram parent) ->
    registrationRank parent = Just parentRank ->
    registrationRank child = Just childRank ->
    registrationYieldTag step = Just tag ->
    registrationCatalog tag = Just child ->
    LT parentRank childRank
  0 precedenceRankIncreases :
    (provider, consumer : Component key value world error) ->
    (providerRank, consumerRank : Nat) ->
    registrationRank provider = Just providerRank ->
    registrationRank consumer = Just consumerRank ->
    (k : key) ->
    Elem k (dependencies (componentProvisions provider)) ->
    Elem k (dependencies (componentDependencies consumer)) ->
    LT providerRank consumerRank

||| Non-vacuous protocol for traces with no inserted components.
public export
emptyRegistrationProtocol : RegistrationProtocol key value world error
emptyRegistrationProtocol = MkRegistrationProtocol
  (\tag => Nothing)
  (\component => Nothing)
  (\parent, child, step, tag, parentRank, childRank,
    sourceInProgram, parentRanked, childRanked, stepTag, cataloged =>
      case parentRanked of Refl impossible)
  (\provider, consumer, providerRank, consumerRank,
    providerRanked, consumerRanked, k, provides, depends =>
      case providerRanked of Refl impossible)

||| A child O-Insert is licensed by the actual next iterator step of its live
||| parent. In particular, `Reloading []` (an empty parent program) cannot
||| register anything, and a shared protocol fixes the yielded component.
public export
record ParentRegistrationYield
  {name, key, world, error : Type} {value : key -> Type}
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (parent : name)
  (childComponent : Component key value world error)
  (state : SystemState name key value world error) where
  constructor MkParentRegistrationYield
  parentFiberAtYield : Fiber name key value world error
  parentFoundAtYield : lookupFiber @{nameEq} parent (registry state) =
    Just parentFiberAtYield
  sourceStep : StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent parentFiberAtYield)))
    (componentProvisions (fiberComponent parentFiberAtYield))
  sourceContinuation : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent parentFiberAtYield)))
    (componentProvisions (fiberComponent parentFiberAtYield)))
  sourceAccumulator : LocalState key value world
    (componentProvisions (fiberComponent parentFiberAtYield)) ->
    LocalState key value world
      (componentProvisions (fiberComponent parentFiberAtYield))
  sourceView : View name
    (dependencies (componentDependencies (fiberComponent parentFiberAtYield)))
  parentAtYield : fiberLifecycle parentFiberAtYield =
    Reloading (sourceStep :: sourceContinuation) sourceAccumulator sourceView
  sourceBelongsToProgram : Elem sourceStep
    (componentProgram (fiberComponent parentFiberAtYield))
  parentRegistrationRank : Nat
  childRegistrationRank : Nat
  parentRanked : registrationRank protocol (fiberComponent parentFiberAtYield) =
    Just parentRegistrationRank
  childRanked : registrationRank protocol childComponent =
    Just childRegistrationRank
  yieldTag : Nat
  stepYieldsTag : registrationYieldTag sourceStep = Just yieldTag
  catalogYieldsComponent : registrationCatalog protocol yieldTag =
    Just childComponent

||| A transition that enters a parent's recovery/unloading path. The stored
||| accumulator itself executes later, at L-Unload.
public export
data ParentRecoveryStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (parent : name) ->
  {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> Type where
  ParentLeaves : transitionAction transition = LLeave parent ->
    ParentRecoveryStep parent transition
  ParentDivertsBefore : transitionAction transition = LDivert parent ->
    ParentRecoveryStep parent transition
  ParentDivertsAfter : transitionAction transition = LAdvance parent ->
    transitionTag transition = LDivertTag ->
    ParentRecoveryStep parent transition
  ParentRaises : transitionAction transition = LAdvance parent ->
    transitionTag transition = LRaiseTag ->
    ParentRecoveryStep parent transition

public export
data NoParentRecovery :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (parent : name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  NoParentRecoveryEnd : NoParentRecovery parent NoTransitions
  NoParentRecoveryStep :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    (ParentRecoveryStep parent transition -> Void) ->
    NoParentRecovery parent rest ->
    NoParentRecovery parent (MoreTransitions transition rest)

||| The explicit O-Retire for a registered child occurs before the first parent
||| recovery transition in the suffix.
public export
data ChildRetiresBeforeRecovery :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (parent, child : name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  ChildRetiresNow :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    transitionAction transition = ORetire child ->
    ChildRetiresBeforeRecovery parent child
      (MoreTransitions transition rest)
  ChildRetiresLater :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    (ParentRecoveryStep parent transition -> Void) ->
    ChildRetiresBeforeRecovery parent child rest ->
    ChildRetiresBeforeRecovery parent child
      (MoreTransitions transition rest)

||| Explicit counterpart of Definition 47's inverse provenance. Either the
||| parent never recovers in this suffix or the yielded child is retired before
||| its first L-Leave/L-Divert/L-Raise recovery boundary.
public export
data ChildRetirementProvenance :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (parent, child : name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  ParentDoesNotRecover : NoParentRecovery parent rest ->
    ChildRetirementProvenance parent child rest
  ChildRetiredBeforeParent : ChildRetiresBeforeRecovery parent child rest ->
    ChildRetirementProvenance parent child rest

||| Lemma-68-only source/rank provenance. Retirement is deliberately excluded:
||| it is needed by Lemma 70, not by the registration-rank argument itself.
public export
RegistrationStepProvenance :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) ->
  (action : Action name key value world error) ->
  (before : SystemState name key value world error) -> Type
RegistrationStepProvenance protocol nameEq
  (OInsert child Root component) before =
    (rank : Nat ** registrationRank protocol component = Just rank)
RegistrationStepProvenance protocol nameEq
  (OInsert child (ChildOf parent) component) before =
    ParentRegistrationYield protocol nameEq parent component before
RegistrationStepProvenance protocol nameEq (ORetire child) before = ()
RegistrationStepProvenance protocol nameEq (ORemove child) before = ()
RegistrationStepProvenance protocol nameEq (LBegin child) before = ()
RegistrationStepProvenance protocol nameEq (LAdvance child) before = ()
RegistrationStepProvenance protocol nameEq (LDivert child) before = ()
RegistrationStepProvenance protocol nameEq (LLeave child) before = ()
RegistrationStepProvenance protocol nameEq (LUnload child) before = ()

public export
data RegistrationProvenance :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  RegistrationProvenanceEnd : RegistrationProvenance protocol nameEq NoTransitions
  RegistrationProvenanceStep :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    RegistrationStepProvenance protocol nameEq
      (transitionAction transition) first ->
    RegistrationProvenance protocol nameEq rest ->
    RegistrationProvenance protocol nameEq (MoreTransitions transition rest)

||| Trace-local Lemma-70/Confluence obligation. Root names may legally be
||| reissued after removal. Child insertion adds inverse-retirement provenance
||| to the exact iterator source and deterministic catalog result above.
public export
RegistrationStepDiscipline :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) ->
  (action : Action name key value world error) ->
  (before : SystemState name key value world error) ->
  {afterState, finalState : SystemState name key value world error} ->
  Transitions afterState finalState -> Type
RegistrationStepDiscipline protocol nameEq
  (OInsert child Root component) before rest =
    (rank : Nat ** registrationRank protocol component = Just rank)
RegistrationStepDiscipline protocol nameEq
  (OInsert child (ChildOf parent) component) before rest =
    (ParentRegistrationYield protocol nameEq parent component before,
     ChildRetirementProvenance parent child rest)
RegistrationStepDiscipline protocol nameEq (ORetire child) before rest = ()
RegistrationStepDiscipline protocol nameEq (ORemove child) before rest = ()
RegistrationStepDiscipline protocol nameEq (LBegin child) before rest = ()
RegistrationStepDiscipline protocol nameEq (LAdvance child) before rest = ()
RegistrationStepDiscipline protocol nameEq (LDivert child) before rest = ()
RegistrationStepDiscipline protocol nameEq (LLeave child) before rest = ()
RegistrationStepDiscipline protocol nameEq (LUnload child) before rest = ()

||| Corrected nested-registration invariant used as an explicit theorem premise;
||| the operational O-Insert rule remains unchanged.
public export
data RegistrationDiscipline :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  RegistrationDisciplineEnd :
    RegistrationDiscipline protocol nameEq NoTransitions
  RegistrationDisciplineStep :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    RegistrationStepDiscipline protocol nameEq
      (transitionAction transition) first rest ->
    RegistrationDiscipline protocol nameEq rest ->
    RegistrationDiscipline protocol nameEq
      (MoreTransitions transition rest)

||| A state reached by checked rules from the paper's empty-registry initial
||| convention. Dictionary alignment avoids an implicit proof-irrelevance axiom.
public export
record ReachedFromEmpty
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (state : SystemState name key value world error) where
  constructor MkReachedFromEmpty
  reachInitial : SystemState name key value world error
  reachTrace : Transitions reachInitial state
  reachAligned : AlignedTransitions name key world error value nameEq keyEq reachTrace
  reachInitialEmpty : bindings (registry reachInitial) = []
  reachInitialWellFormed : registryWellFormed @{nameEq} @{keyEq} reachInitial = True

public export
providerFromPredicate : DecEq name => DecEq key => key -> (name -> Bool) ->
  List (Binding name (FiberAt name key value world error)) -> Bool
providerFromPredicate wanted supported [] = False
providerFromPredicate wanted supported (Bind n fiber :: rest) =
  (supported n && listMember wanted
    (dependencies (componentProvisions (fiberComponent fiber)))) ||
  providerFromPredicate wanted supported rest

public export
allList : (a -> Bool) -> List a -> Bool
allList predicate [] = True
allList predicate (value :: rest) = predicate value && allList predicate rest

||| One unfolding of Definition 67 for an arbitrary candidate support set.
public export
supportClause : DecEq name => DecEq key => (name -> Bool) -> name ->
  SystemState name key value world error -> Bool
supportClause supported selected state =
  case lookupFiber selected (registry state) of
    Nothing => False
    Just fiber =>
      not (retired fiber) &&
      (case fiberParent fiber of
        Root => True
        ChildOf parent => supported parent) &&
      allList (\k => providerFromPredicate k supported
        (registryFibers (registry state)))
        (dependencies (componentDependencies (fiberComponent fiber)))

public export
SupportSolution :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  DecEq name => DecEq key => (name -> Bool) ->
  SystemState name key value world error -> Type
SupportSolution {name} candidate state =
  (n : name) -> candidate n = supportClause candidate n state


public export
providerFromCandidate : DecEq name => DecEq key => key -> List name ->
  List (Binding name (FiberAt name key value world error)) -> Bool
providerFromCandidate wanted supported [] = False
providerFromCandidate wanted supported (Bind n fiber :: rest) =
  (listMember n supported && listMember wanted
    (dependencies (componentProvisions (fiberComponent fiber)))) ||
  providerFromCandidate wanted supported rest

public export
parentFromCandidate : DecEq name => Parent name -> List name -> Bool
parentFromCandidate Root supported = True
parentFromCandidate (ChildOf parent) supported = listMember parent supported

public export
supportCandidate : DecEq name => DecEq key =>
  List (Binding name (FiberAt name key value world error)) ->
  List name -> Binding name (FiberAt name key value world error) -> Bool
supportCandidate entries supported (Bind n fiber) =
  not (retired fiber) &&
  parentFromCandidate (fiberParent fiber) supported &&
  allList (\k => providerFromCandidate k supported entries)
    (dependencies (componentDependencies (fiberComponent fiber)))

public export
supportPassEntries : DecEq name => DecEq key =>
  List (Binding name (FiberAt name key value world error)) ->
  List (Binding name (FiberAt name key value world error)) ->
  List name -> List name
supportPassEntries entries [] supported = supported
supportPassEntries entries (entry@(Bind n fiber) :: rest) supported =
  if listMember n supported then supportPassEntries entries rest supported
  else if supportCandidate entries supported entry
    then supportPassEntries entries rest (n :: supported)
    else supportPassEntries entries rest supported

public export
supportPassEntriesMember :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {auto nameEq : DecEq name} -> {auto keyEq : DecEq key} ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (entry : Binding name (FiberAt name key value world error)) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  (supported : List name) ->
  listMember (bindingKey entry) supported = True ->
  supportPassEntries {value = value} {world = world} {error = error} entries (entry :: rest) supported =
    supportPassEntries {value = value} {world = world} {error = error} entries rest supported
supportPassEntriesMember entries (Bind n fiber) rest supported member =
  rewrite member in Refl

public export
supportPassEntriesAdd :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {auto nameEq : DecEq name} -> {auto keyEq : DecEq key} ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (entry : Binding name (FiberAt name key value world error)) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  (supported : List name) ->
  listMember (bindingKey entry) supported = False ->
  supportCandidate {value = value} {world = world} {error = error} entries supported entry = True ->
  supportPassEntries {value = value} {world = world} {error = error} entries (entry :: rest) supported =
    supportPassEntries {value = value} {world = world} {error = error} entries rest (bindingKey entry :: supported)
supportPassEntriesAdd entries entry@(Bind n fiber) rest supported member candidate =
  rewrite member in rewrite candidate in Refl

public export
supportPassEntriesReject :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {auto nameEq : DecEq name} -> {auto keyEq : DecEq key} ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (entry : Binding name (FiberAt name key value world error)) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  (supported : List name) ->
  listMember (bindingKey entry) supported = False ->
  supportCandidate {value = value} {world = world} {error = error} entries supported entry = False ->
  supportPassEntries {value = value} {world = world} {error = error} entries (entry :: rest) supported =
    supportPassEntries {value = value} {world = world} {error = error} entries rest supported
supportPassEntriesReject entries entry@(Bind n fiber) rest supported member candidate =
  rewrite member in rewrite candidate in Refl

public export
supportPassEntriesRejectElim :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {auto nameEq : DecEq name} -> {auto keyEq : DecEq key} ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (entry : Binding name (FiberAt name key value world error)) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  (supported : List name) ->
  listMember (bindingKey entry) supported = False ->
  supportCandidate {value = value} {world = world} {error = error}
    entries supported entry = False ->
  (property : List name -> Type) ->
  property (supportPassEntries {value = value} {world = world} {error = error}
    entries rest supported) ->
  property (supportPassEntries {value = value} {world = world} {error = error}
    entries (entry :: rest) supported)
supportPassEntriesRejectElim entries entry@(Bind n fiber) rest supported
  member candidate property result =
    rewrite member in rewrite candidate in result

public export
supportPass : DecEq name => DecEq key =>
  List (Binding name (FiberAt name key value world error)) ->
  List name -> List name
supportPass entries supported = supportPassEntries entries entries supported

public export
supportFuel : DecEq name => DecEq key => Nat ->
  List (Binding name (FiberAt name key value world error)) ->
  List name -> List name
supportFuel Z entries supported = supported
supportFuel (S fuel) entries supported =
  supportFuel fuel entries (supportPass entries supported)

||| Definition 67's least support set, computed by bounded fixed-point
||| iteration. A registry has at most `length entries` successful additions.
public export
supportSet : DecEq name => DecEq key =>
  SystemState name key value world error -> List name
supportSet state = let entries = registryFibers (registry state) in
  supportFuel (length entries) entries []

public export
isSupported : DecEq name => DecEq key => name ->
  SystemState name key value world error -> Bool
isSupported n state = listMember n (supportSet state)

bindingKeyFromEntryElemSupport :
  (n : name) -> (fiber : Fiber name key value world error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  Elem (Bind n fiber) entries -> Elem n (bindingKeys entries)
bindingKeyFromEntryElemSupport n fiber (Bind n fiber :: rest) Here = Here
bindingKeyFromEntryElemSupport n fiber (entry :: rest) (There later) =
  There (bindingKeyFromEntryElemSupport n fiber rest later)



listMemberSelfTrue : DecEq name => (selected : name) ->
  (supported : List name) -> listMember selected (selected :: supported) = True
listMemberSelfTrue selected supported with (decEq selected selected)
  listMemberSelfTrue selected supported | Yes Refl = Refl
  listMemberSelfTrue selected supported | No contra = void (contra Refl)

listMemberConsTailTrue : DecEq name =>
  (selected, added : name) -> (supported : List name) ->
  listMember selected supported = True ->
  listMember selected (added :: supported) = True
listMemberConsTailTrue selected added supported present
  with (decEq selected added)
  listMemberConsTailTrue added added supported present | Yes Refl = Refl
  listMemberConsTailTrue selected added supported present | No different = present

listMemberConsOtherFalse : DecEq name =>
  (selected, added : name) -> Not (selected = added) ->
  (supported : List name) -> listMember selected supported = False ->
  listMember selected (added :: supported) = False
listMemberConsOtherFalse selected added different supported missing
  with (decEq selected added)
  listMemberConsOtherFalse added added different supported missing | Yes Refl =
    void (different Refl)
  listMemberConsOtherFalse selected added different supported missing | No _ = missing

supportPassEntriesPreservesMember :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (scan : List (Binding name (FiberAt name key value world error))) ->
  (supported : List name) -> (selected : name) ->
  listMember @{nameEq} selected supported = True ->
  listMember @{nameEq} selected
    (supportPassEntries @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries scan supported) = True
supportPassEntriesPreservesMember nameEq keyEq entries [] supported selected
  present = present
supportPassEntriesPreservesMember nameEq keyEq entries (Bind current fiber :: rest)
  supported selected present with (listMember @{nameEq} current supported)
  supportPassEntriesPreservesMember nameEq keyEq entries
    (Bind current fiber :: rest) supported selected present | True =
      supportPassEntriesPreservesMember nameEq keyEq entries rest supported selected
        present
  supportPassEntriesPreservesMember nameEq keyEq entries
    (Bind current fiber :: rest) supported selected present | False
    with (supportCandidate @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries supported
      (Bind current fiber))
    supportPassEntriesPreservesMember nameEq keyEq entries
      (Bind current fiber :: rest) supported selected present | False | True =
        supportPassEntriesPreservesMember nameEq keyEq entries rest
          (current :: supported) selected
          (listMemberConsTailTrue selected current supported present)
    supportPassEntriesPreservesMember nameEq keyEq entries
      (Bind current fiber :: rest) supported selected present | False | False =
        supportPassEntriesPreservesMember nameEq keyEq entries rest supported
          selected present

public export
supportPassEntriesEligible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (scan : List (Binding name (FiberAt name key value world error))) ->
  UniqueKeys (bindingKeys scan) ->
  (supported : List name) ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  Elem (Bind selected fiber) scan ->
  listMember @{nameEq} selected supported = False ->
  supportCandidate @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries supported
    (Bind selected fiber) = True ->
  ((added : name) -> (current : List name) ->
    supportCandidate @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries current
      (Bind selected fiber) = True ->
    supportCandidate @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries (added :: current)
      (Bind selected fiber) = True) ->
  listMember @{nameEq} selected
    (supportPassEntries @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries scan supported) = True
supportPassEntriesEligible nameEq keyEq entries [] UniqueNil supported selected
  fiber present missing candidate monotone impossible
supportPassEntriesEligible nameEq keyEq entries
  (Bind selected fiber :: rest) (UniqueCons headFresh tailUnique) supported
  selected fiber Here missing candidate monotone
  with (listMember @{nameEq} selected supported)
  supportPassEntriesEligible nameEq keyEq entries
    (Bind selected fiber :: rest) (UniqueCons headFresh tailUnique) supported
    selected fiber Here missing candidate monotone | True =
      case missing of Refl impossible
  supportPassEntriesEligible nameEq keyEq entries
    (Bind selected fiber :: rest) (UniqueCons headFresh tailUnique) supported
    selected fiber Here missing candidate monotone | False
    with (supportCandidate @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries supported
      (Bind selected fiber))
    supportPassEntriesEligible nameEq keyEq entries
      (Bind selected fiber :: rest) (UniqueCons headFresh tailUnique) supported
      selected fiber Here missing candidate monotone | False | True =
        supportPassEntriesPreservesMember nameEq keyEq entries rest
          (selected :: supported) selected (listMemberSelfTrue selected supported)
    supportPassEntriesEligible nameEq keyEq entries
      (Bind selected fiber :: rest) (UniqueCons headFresh tailUnique) supported
      selected fiber Here missing candidate monotone | False | False =
        case candidate of Refl impossible
supportPassEntriesEligible nameEq keyEq entries
  (Bind current observed :: rest) (UniqueCons headFresh tailUnique) supported
  selected fiber (There later) missing candidate monotone
  with (listMember @{nameEq} current supported)
  supportPassEntriesEligible nameEq keyEq entries
    (Bind current observed :: rest) (UniqueCons headFresh tailUnique) supported
    selected fiber (There later) missing candidate monotone | True =
      supportPassEntriesEligible nameEq keyEq entries rest tailUnique supported
        selected fiber later missing candidate monotone
  supportPassEntriesEligible nameEq keyEq entries
    (Bind current observed :: rest) (UniqueCons headFresh tailUnique) supported
    selected fiber (There later) missing candidate monotone | False
    with (supportCandidate @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries supported
      (Bind current observed))
    supportPassEntriesEligible nameEq keyEq entries
      (Bind current observed :: rest) (UniqueCons headFresh tailUnique) supported
      selected fiber (There later) missing candidate monotone | False | False =
        supportPassEntriesEligible nameEq keyEq entries rest tailUnique supported
          selected fiber later missing candidate monotone
    supportPassEntriesEligible nameEq keyEq entries
      (Bind current observed :: rest) (UniqueCons headFresh tailUnique) supported
      selected fiber (There later) missing candidate monotone | False | True =
        let different : Not (selected = current)
            different same = headFresh
              (replace {p = \n => Elem n (bindingKeys rest)} same
                (bindingKeyFromEntryElemSupport selected fiber rest later))
            nextMissing = listMemberConsOtherFalse selected current different
              supported missing
            nextCandidate = monotone current supported candidate
        in supportPassEntriesEligible nameEq keyEq entries rest tailUnique
          (current :: supported) selected fiber later nextMissing nextCandidate
          monotone

public export
record SupportWellFoundedResult
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (state : SystemState name key value world error) where
  constructor MkSupportWellFoundedResult
  combinedWellFounded : SupportWellFounded nameEq state
  uniqueSupportSolution : (candidate : name -> Bool) ->
    SupportSolution @{nameEq} @{keyEq} candidate state ->
    (n : name) -> candidate n = isSupported @{nameEq} @{keyEq} n state

||| Paper Lemma 68 with the missing nested-registration invariant exposed as a
||| premise. Reachability alone is insufficient under Table-1 O-Insert; see
||| Erratum #3 in NOTES.md.
||| Constructively implemented by `supportWellFoundedTheoremProof` in
||| `DGamma.CP4SupportSolution`; no postulate or escape hatch is used.
public export
supportWellFoundedTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
supportWellFoundedTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (state : SystemState name key value world error) ->
  (reached : ReachedFromEmpty name key world error value nameEq keyEq state) ->
  RegistrationProvenance protocol nameEq (reachTrace reached) ->
  PrecedenceAcyclic nameEq state ->
  SupportWellFoundedResult name key world error value nameEq keyEq state


||| An uninterrupted execution of a finite component program. CP3 originally
||| used this object as Definition 69. That reading is too weak for the actual
||| interleaving LTS: a foreign step may change the ambient world between two
||| iterations. It remains public only to state the committed CP4 countermodel.
public export
data ProgramFinishes :
  (program : List (StepEffect key value world error deps provision)) ->
  DepValues key value deps ->
  LocalState key value world provision ->
  LocalState key value world provision -> Type where
  ProgramFinished : ProgramFinishes [] capability state state
  ProgramAdvanced :
    (step : StepEffect key value world error deps provision) ->
    (rest : List (StepEffect key value world error deps provision)) ->
    (before, after, finalState : LocalState key value world provision) ->
    (undo : LocalState key value world provision ->
      LocalState key value world provision) ->
    runStepEffect step capability before = Right (after, undo) ->
    ProgramFinishes rest capability after finalState ->
    ProgramFinishes (step :: rest) capability before finalState

||| The rejected CP3 interpretation of Definition 69. It quantifies only
||| uninterrupted executions and is retained as an explicit regression target,
||| not as a premise of Lemmas 70/72 or Theorem 73.
public export
UninterruptedComponentTotalOnProvision :
  {key, world, error : Type} -> {value : key -> Type} -> DecEq key =>
  (component : Component key value world error) -> Type
UninterruptedComponentTotalOnProvision {key} {value} {world} {error} component =
  (capability : DepValues key value
    (dependencies (componentDependencies component))) ->
  (before, finalState : LocalState key value world
    (componentProvisions component)) ->
  ProgramFinishes (componentProgram component) capability before finalState ->
  (k : key) -> Elem k (dependencies (componentProvisions component)) ->
  isJust (lookupBinding k (ownedValues (localTable finalState))) = True

||| Every declared provision of one currently Active fiber is installed in its
||| actual runtime table.
public export
ActiveFiberProvidesAll :
  {key, world, error, name : Type} -> {value : key -> Type} ->
  (keyEq : DecEq key) -> Fiber name key value world error -> Type
ActiveFiberProvidesAll {key} {value} keyEq fiber =
  (k : key) -> Elem k
    (dependencies (componentProvisions (fiberComponent fiber))) ->
  isJust (lookupBinding @{keyEq} k
    (ownedValues (fiberTable fiber))) = True

||| Endpoint form derived from repaired trace totality. It is not independently
||| assumed by Lemma 70.
public export
ActiveFibersProvideAll :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  SystemState name key value world error -> Type
ActiveFibersProvideAll {name} nameEq keyEq state =
  (n : name) -> (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} n (registry state) = Just fiber ->
  isActive (fiberLifecycle fiber) = True ->
  ActiveFiberProvidesAll keyEq fiber

||| Repaired Definition 69 obligation at one actual checked scheduling boundary.
||| Sampling the acting fiber after every action is a preserved strengthening of
||| sampling only L-Finish: a checked action can first make its actor Active only
||| at L-Finish, and foreign actions leave that fiber's table unchanged.
public export
TransitionComponentTotal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> Type
TransitionComponentTotal {name} nameEq keyEq {afterState} transition =
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} (actionOwner (transitionAction transition))
    (registry afterState) = Just fiber ->
  isActive (fiberLifecycle fiber) = True ->
  ActiveFiberProvidesAll keyEq fiber

||| Paper Definition 69 repaired to range over actual interleaved checked
||| activations. Every actor boundary in the supplied trace certifies its actual
||| Active table, so in particular every activation that finishes is total on
||| its provision. Unlike the old `ProgramFinishes` reading, foreign ambient
||| changes between iterations are observed.
public export
data TraceComponentsTotal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  TraceComponentsTotalEnd : TraceComponentsTotal nameEq keyEq NoTransitions
  TraceComponentsTotalStep :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    TransitionComponentTotal nameEq keyEq transition ->
    TraceComponentsTotal nameEq keyEq rest ->
    TraceComponentsTotal nameEq keyEq
      (MoreTransitions transition rest)

||| The old endpoint collection of uninterrupted component predicates. It is a
||| diagnostic for the CP4 countermodel only and no longer represents paper
||| Definition 69.
public export
UninterruptedComponentsTotalOnProvision :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  DecEq name => DecEq key => SystemState name key value world error -> Type
UninterruptedComponentsTotalOnProvision {name} {key} {value} {world} {error}
  state =
    (n : name) -> (fiber : Fiber name key value world error) ->
    lookupFiber n (registry state) = Just fiber ->
    UninterruptedComponentTotalOnProvision (fiberComponent fiber)

||| Executable current-state consequence used by runtime diagnostics: every
||| Active instance currently has every provision key installed. It is weaker
||| than Definition 69 and intentionally vacuous outside Active.
public export
fiberTotalOnProvision : DecEq key =>
  Fiber name key value world error -> Bool
fiberTotalOnProvision fiber = case fiberLifecycle fiber of
  Active accumulator view => allList
    (\k => isJust (lookupBinding k (ownedValues (fiberTable fiber))))
    (dependencies (componentProvisions (fiberComponent fiber)))
  _ => True

public export
allFibersTotalOnProvision : DecEq key =>
  SystemState name key value world error -> Bool
allFibersTotalOnProvision state = all totalEntry
  (registryFibers (registry state))
  where
  totalEntry : Binding name (FiberAt name key value world error) -> Bool
  totalEntry (Bind n fiber) = fiberTotalOnProvision fiber

public export
fiberNotFailed : Fiber name key value world error -> Bool
fiberNotFailed fiber = case fiberLifecycle fiber of
  Inactive (Just errorValue) => False
  _ => True

public export
notFailedEntry : Binding name (FiberAt name key value world error) -> Bool
notFailedEntry (Bind n fiber) = fiberNotFailed fiber

public export
noFailedFibers : SystemState name key value world error -> Bool
noFailedFibers state = allList notFailedEntry
  (registryFibers (registry state))

public export
programBoundedEntry : Nat ->
  Binding name (FiberAt name key value world error) -> Bool
programBoundedEntry bound (Bind n fiber) =
  length (componentProgram (fiberComponent fiber)) <= bound

public export
programsBoundedBy : Nat -> SystemState name key value world error -> Bool
programsBoundedBy bound state = allList (programBoundedEntry bound)
  (registryFibers (registry state))

public export
0 programsBoundedByEquation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (bound : Nat) -> (state : SystemState name key value world error) ->
  programsBoundedBy bound state =
    allList (programBoundedEntry {name = name} {key = key} {value = value}
      {world = world} {error = error} bound)
      (registryFibers {value = value} {world = world} {error = error}
        (registry state))
programsBoundedByEquation bound state = Refl

public export
continuationLengthCheck : Nat -> Maybe Nat -> Bool
continuationLengthCheck bound Nothing = True
continuationLengthCheck bound (Just remainingLength) = remainingLength <= bound

public export
fiberContinuationBoundedBy : Nat -> Fiber name key value world error -> Bool
fiberContinuationBoundedBy bound fiber =
  continuationLengthCheck bound (fiberContinuationLength fiber)

public export
0 fiberContinuationBoundedByEquation :
  (bound : Nat) -> (fiber : Fiber name key value world error) ->
  fiberContinuationBoundedBy bound fiber =
    continuationLengthCheck bound (fiberContinuationLength fiber)
fiberContinuationBoundedByEquation bound fiber = Refl

public export
continuationBoundedEntry : Nat ->
  Binding name (FiberAt name key value world error) -> Bool
continuationBoundedEntry bound (Bind n fiber) =
  fiberContinuationBoundedBy bound fiber

||| CP4 repair premise for Theorem 66: the paper's reached-state convention
||| makes every current Reloading continuation a suffix of its declared program.
||| The finite alias exposes exactly the length consequence needed by Equation 61.
public export
continuationsBoundedBy : Nat ->
  SystemState name key value world error -> Bool
continuationsBoundedBy bound state = allList (continuationBoundedEntry bound)
  (registryFibers (registry state))

public export
0 continuationsBoundedByEquation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (bound : Nat) -> (state : SystemState name key value world error) ->
  continuationsBoundedBy bound state =
    allList (continuationBoundedEntry {name = name} {key = key}
      {value = value} {world = world} {error = error} bound)
      (registryFibers {value = value} {world = world} {error = error}
        (registry state))
continuationsBoundedByEquation bound state = Refl

||| A concrete host lifecycle rule applicable at one state. `LAdvance` covers
||| the landing L-Iter/L-Finish/L-Raise/L-Divert alternatives; the separate
||| `LDivert` constructor is the optional aborting rule.
public export
data LifecycleMove :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  SystemState name key value world error -> Type where
  CanBegin : (actor : name) -> (after : SystemState name key value world error) ->
    applyAction @{nameEq} @{keyEq} (LBegin actor) before = Just (LBeginTag, after) ->
    LifecycleMove nameEq keyEq before
  CanAdvance : (actor : name) -> (tag : RuleTag) ->
    (after : SystemState name key value world error) ->
    applyAction @{nameEq} @{keyEq} (LAdvance actor) before = Just (tag, after) ->
    LifecycleMove nameEq keyEq before
  CanDivert : (actor : name) -> (after : SystemState name key value world error) ->
    applyAction @{nameEq} @{keyEq} (LDivert actor) before = Just (LDivertTag, after) ->
    LifecycleMove nameEq keyEq before
  CanLeave : (actor : name) -> (after : SystemState name key value world error) ->
    applyAction @{nameEq} @{keyEq} (LLeave actor) before = Just (LLeaveTag, after) ->
    LifecycleMove nameEq keyEq before
  CanUnload : (actor : name) -> (after : SystemState name key value world error) ->
    applyAction @{nameEq} @{keyEq} (LUnload actor) before = Just (LUnloadTag, after) ->
    LifecycleMove nameEq keyEq before

tryUnload : DecEq name => DecEq key => (actor : name) ->
  (state : SystemState name key value world error) -> Maybe (LifecycleMove %search %search state)
tryUnload actor state with (applyAction (LUnload actor) state) proof result
  tryUnload actor state | Just (LUnloadTag, after) =
    Just (CanUnload actor after result)
  tryUnload actor state | Just (tag, after) = Nothing
  tryUnload actor state | Nothing = Nothing

tryLeave : DecEq name => DecEq key => (actor : name) ->
  (state : SystemState name key value world error) -> Maybe (LifecycleMove %search %search state)
tryLeave actor state with (applyAction (LLeave actor) state) proof result
  tryLeave actor state | Just (LLeaveTag, after) =
    Just (CanLeave actor after result)
  tryLeave actor state | Just (tag, after) = tryUnload actor state
  tryLeave actor state | Nothing = tryUnload actor state

tryDivert : DecEq name => DecEq key => (actor : name) ->
  (state : SystemState name key value world error) -> Maybe (LifecycleMove %search %search state)
tryDivert actor state with (applyAction (LDivert actor) state) proof result
  tryDivert actor state | Just (LDivertTag, after) =
    Just (CanDivert actor after result)
  tryDivert actor state | Just (tag, after) = tryLeave actor state
  tryDivert actor state | Nothing = tryLeave actor state

tryAdvance : DecEq name => DecEq key => (actor : name) ->
  (state : SystemState name key value world error) -> Maybe (LifecycleMove %search %search state)
tryAdvance actor state with (applyAction (LAdvance actor) state) proof result
  tryAdvance actor state | Just (tag, after) =
    Just (CanAdvance actor tag after result)
  tryAdvance actor state | Nothing = tryDivert actor state

tryLifecycleActor : DecEq name => DecEq key => (actor : name) ->
  (state : SystemState name key value world error) -> Maybe (LifecycleMove %search %search state)
tryLifecycleActor actor state with (applyAction (LBegin actor) state) proof result
  tryLifecycleActor actor state | Just (LBeginTag, after) =
    Just (CanBegin actor after result)
  tryLifecycleActor actor state | Just (tag, after) = tryAdvance actor state
  tryLifecycleActor actor state | Nothing = tryAdvance actor state

firstApplicableFrom : DecEq name => DecEq key =>
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (state : SystemState name key value world error) -> Maybe (LifecycleMove %search %search state)
firstApplicableFrom [] state = Nothing
firstApplicableFrom (Bind actor fiber :: rest) state =
  case tryLifecycleActor actor state of
    Just move => Just move
    Nothing => firstApplicableFrom rest state

||| Executable witness search over exactly the lifecycle rules required by the
||| paper's Progress theorem.
public export
firstApplicableLifecycle : DecEq name => DecEq key =>
  (state : SystemState name key value world error) -> Maybe (LifecycleMove %search %search state)
firstApplicableLifecycle state =
  firstApplicableFrom (registryFibers (registry state)) state

public export
LifecycleMaximal : (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  SystemState name key value world error -> Type
LifecycleMaximal nameEq keyEq state =
  LifecycleMove nameEq keyEq state -> Void

public export
isLifecycleAction : Action name key value world error -> Bool
isLifecycleAction (OInsert n parent component) = False
isLifecycleAction (ORetire n) = False
isLifecycleAction (ORemove n) = False
isLifecycleAction _ = True

public export
data LifecycleOnly :
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  LifecycleOnlyEnd : LifecycleOnly NoTransitions
  LifecycleOnlyStep :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    isLifecycleAction (transitionAction transition) = True ->
    LifecycleOnly rest -> LifecycleOnly (MoreTransitions transition rest)

public export
0 stepsActingOn : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, last : SystemState name key value world error} ->
  DecEq name => name -> Transitions first last -> Nat
stepsActingOn actor NoTransitions = Z
stepsActingOn actor (MoreTransitions transition rest) =
  let later = stepsActingOn actor rest in
  case decEq (transitionActor transition) actor of
    Yes Refl => S later
    No _ => later

public export
sameNameList : DecEq name => List name -> List name -> Bool
sameNameList [] [] = True
sameNameList [] (_ :: _) = False
sameNameList (_ :: _) [] = False
sameNameList (x :: xs) (y :: ys) = case decEq x y of
  Yes Refl => sameNameList xs ys
  No _ => False

public export
targetProvidersAt : DecEq name => DecEq key => name ->
  SystemState name key value world error -> Maybe (List name)
targetProvidersAt actor state = case lookupFiber actor (registry state) of
  Nothing => Nothing
  Just fiber => map viewProviders (targetFiber fiber (registry state))

public export
sameTarget : DecEq name => Maybe (List name) -> Maybe (List name) -> Bool
sameTarget Nothing Nothing = True
sameTarget Nothing (Just _) = False
sameTarget (Just _) Nothing = False
sameTarget (Just left) (Just right) = sameNameList left right

||| Equation 61 as an exact indexed count. Transition endpoint states live in
||| erased indices, so the count is evidence rather than a runtime traversal;
||| `sameTarget` itself remains executable on explicit endpoints.
public export
data TargetTurnCount :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {first, last : SystemState name key value world error} ->
  Transitions first last -> Nat -> Type where
  NoTargetTurns : TargetTurnCount name key world error value nameEq keyEq actor
    NoTransitions Z
  TargetStayed :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    sameTarget @{nameEq}
      (targetProvidersAt @{nameEq} @{keyEq} actor first)
      (targetProvidersAt @{nameEq} @{keyEq} actor middle) = True ->
    TargetTurnCount name key world error value nameEq keyEq actor rest turns ->
    TargetTurnCount name key world error value nameEq keyEq actor
      (MoreTransitions transition rest) turns
  TargetChanged :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    sameTarget @{nameEq}
      (targetProvidersAt @{nameEq} @{keyEq} actor first)
      (targetProvidersAt @{nameEq} @{keyEq} actor middle) = False ->
    TargetTurnCount name key world error value nameEq keyEq actor rest turns ->
    TargetTurnCount name key world error value nameEq keyEq actor
      (MoreTransitions transition rest) (S turns)

public export
record ProgressResult
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (bound : Nat)
  {first, last : SystemState name key value world error}
  (trace : Transitions first last) where
  constructor MkProgressResult
  noDeadlock : quiet @{nameEq} @{keyEq} last = False -> LifecycleMove nameEq keyEq last
  perFiberBound : (actor : name) -> (turns : Nat) ->
    TargetTurnCount name key world error value nameEq keyEq actor trace turns ->
    LTE (stepsActingOn @{nameEq} actor trace)
      ((bound + 4) * (turns + 1))
  maximalIsQuiet : LifecycleMaximal nameEq keyEq last ->
    quiet @{nameEq} @{keyEq} last = True

||| Candidate finite-trace/static-list specialization of Theorem 66.
||| Finiteness of N is intrinsic in the registry representation.
||| CP4 Finding #5 repairs the arbitrary-first-state encoding by exposing the
||| paper-implicit bound on every current Reloading continuation. CP4 Finding #6
||| restores the global equality discipline already used by sibling trace
||| theorems: every checked step is aligned with these equality witnesses.
||| Constructively implemented by `DGamma.CP4ProgressProof.progressTheoremProof`.
public export
progressTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
progressTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (bound : Nat) ->
  (first, last : SystemState name key value world error) ->
  (trace : Transitions first last) ->
  LifecycleOnly trace ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  registryWellFormed @{nameEq} @{keyEq} first = True ->
  PrecedenceAcyclic nameEq first ->
  programsBoundedBy bound first = True ->
  continuationsBoundedBy bound first = True ->
  ProgressResult name key world error value nameEq keyEq bound trace

||| Tractable executable core: a successful search result is already the exact
||| indexed applicability witness needed by the no-deadlock conclusion.
public export
0 searchedLifecycleMove :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  (move : LifecycleMove nameEq keyEq state) ->
  firstApplicableLifecycle @{nameEq} @{keyEq} state = Just move ->
  LifecycleMove nameEq keyEq state
searchedLifecycleMove nameEq keyEq state move equation = move

||| The logical consequence in the last sentence of Theorem 66: no-deadlock
||| turns lifecycle maximality into quiescence without an additional axiom.
public export
0 maximalQuietFromNoDeadlock :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  (noDeadlock : quiet @{nameEq} @{keyEq} state = False ->
    LifecycleMove nameEq keyEq state) ->
  LifecycleMaximal nameEq keyEq state ->
  quiet @{nameEq} @{keyEq} state = True
maximalQuietFromNoDeadlock nameEq keyEq state noDeadlock maximal
  with (quiet @{nameEq} @{keyEq} state) proof quietResult
  maximalQuietFromNoDeadlock nameEq keyEq state noDeadlock maximal | True = Refl
  maximalQuietFromNoDeadlock nameEq keyEq state noDeadlock maximal | False =
    void (maximal (noDeadlock Refl))

||| The lifecycle/control observation retained by Section 4's `simeq`. Effect
||| tables and ambient state are deliberately excluded here and compared by
||| `EffectStateRelated` instead.
public export
data LifecycleShape = InactiveCleanShape | InactiveFailedShape |
  ReloadingShape | ActiveShape | UnloadingCleanShape | UnloadingFailedShape

public export
lifecycleShape : Lifecycle key value world error name deps provision -> LifecycleShape
lifecycleShape (Inactive Nothing) = InactiveCleanShape
lifecycleShape (Inactive (Just _)) = InactiveFailedShape
lifecycleShape (Reloading _ _ _) = ReloadingShape
lifecycleShape (Active _ _) = ActiveShape
lifecycleShape (Unloading _ _ Nothing) = UnloadingCleanShape
lifecycleShape (Unloading _ _ (Just _)) = UnloadingFailedShape

public export
record ControlObservation (name : Type) where
  constructor MkControlObservation
  observedRetired : Bool
  observedShape : LifecycleShape
  observedProviders : Maybe (List name)

public export
controlObservationAt : DecEq name => name ->
  SystemState name key value world error -> Maybe (ControlObservation name)
controlObservationAt n state = case lookupFiber n (registry state) of
  Nothing => Nothing
  Just fiber => Just (MkControlObservation (retired fiber)
    (lifecycleShape (fiberLifecycle fiber))
    (map viewProviders (committed (fiberLifecycle fiber))))

||| Runtime observation on proof-bearing local states.  Ambient values and the
||| complete ordered binding list are observable; erased `OwnedTable`
||| certificates are not (CP4 Finding #12).
public export
record LocalStateRuntimeRelated
  {key, world : Type} {value : key -> Type}
  {provision : CoeffectSpec key}
  (left, right : LocalState key value world provision) where
  constructor MkLocalStateRuntimeRelated
  0 localAmbientExact : localWorld left = localWorld right
  0 localBindingsExact :
    bindings (ownedValues (localTable left)) =
    bindings (ownedValues (localTable right))

public export
0 localStateRuntimeReflexive :
  (state : LocalState key value world provision) ->
  LocalStateRuntimeRelated state state
localStateRuntimeReflexive state = MkLocalStateRuntimeRelated Refl Refl

public export
0 localStateRuntimeSymmetric :
  LocalStateRuntimeRelated left right -> LocalStateRuntimeRelated right left
localStateRuntimeSymmetric (MkLocalStateRuntimeRelated ambient tables) =
  MkLocalStateRuntimeRelated (sym ambient) (sym tables)

public export
0 localStateRuntimeTransitive :
  LocalStateRuntimeRelated first middle ->
  LocalStateRuntimeRelated middle finalState ->
  LocalStateRuntimeRelated first finalState
localStateRuntimeTransitive
  (MkLocalStateRuntimeRelated firstAmbient firstTables)
  (MkLocalStateRuntimeRelated secondAmbient secondTables) =
    MkLocalStateRuntimeRelated (trans firstAmbient secondAmbient)
      (trans firstTables secondTables)

||| Pointwise runtime relation on accumulator functions carried inside
||| lifecycle control state (paper Equation 53 / Definition 36).  This compares
||| exactly what a plugin can observe and never asks for equality of erased
||| certificate terms in function outputs.
public export
AccumulatorRelated :
  {key, world : Type} -> {value : key -> Type} ->
  {provision : CoeffectSpec key} ->
  (LocalState key value world provision -> LocalState key value world provision) ->
  (LocalState key value world provision -> LocalState key value world provision) ->
  Type
AccumulatorRelated {key} {value} {world} {provision} left right =
  (input : LocalState key value world provision) ->
  LocalStateRuntimeRelated (left input) (right input)

||| Equal runtime observations normalize to one exact canonical local state.
||| This is the proof-term boundary used when composed accumulator callbacks
||| exchange values.
public export
0 localStateRuntimeNormalizationEqual :
  (keyEq : DecEq key) -> (provision : CoeffectSpec key) ->
  {left, right : LocalState key value world provision} ->
  LocalStateRuntimeRelated left right ->
  normalizeLocal @{keyEq} provision left = normalizeLocal @{keyEq} provision right
localStateRuntimeNormalizationEqual keyEq provision
  {left = MkLocalState leftAmbient leftTable}
  {right = MkLocalState rightAmbient rightTable}
  (MkLocalStateRuntimeRelated ambientSame bindingsSame) =
    case ambientSame of
      Refl => cong (MkLocalState rightAmbient)
        (canonicalNormalizationFromEqualBindings @{keyEq} provision
          (ownedValues leftTable) (ownedValues rightTable) bindingsSame)

||| Finding-12 composition keystone.  Each newly yielded inverse receives the
||| canonicalized input promised by `IteratorYieldAgreement`; its runtime-related
||| outputs normalize to one exact argument for the already-related older
||| accumulators.
public export
0 pushLocalUndoRuntimeRelated :
  (keyEq : DecEq key) -> (provision : CoeffectSpec key) ->
  (leftAccumulator, rightAccumulator :
    LocalState key value world provision -> LocalState key value world provision) ->
  (leftUndo, rightUndo :
    LocalState key value world provision -> LocalState key value world provision) ->
  AccumulatorRelated leftAccumulator rightAccumulator ->
  ((input : LocalState key value world provision) ->
    LocalStateRuntimeRelated
      (leftUndo (normalizeLocal @{keyEq} provision input))
      (rightUndo (normalizeLocal @{keyEq} provision input))) ->
  AccumulatorRelated
    (pushLocalUndo @{keyEq} provision leftAccumulator leftUndo)
    (pushLocalUndo @{keyEq} provision rightAccumulator rightUndo)
pushLocalUndoRuntimeRelated keyEq provision leftAccumulator rightAccumulator
  leftUndo rightUndo older undos input =
    let 0 normalizedSame : (
          normalizeLocal @{keyEq} provision
            (leftUndo (normalizeLocal @{keyEq} provision input)) =
          normalizeLocal @{keyEq} provision
            (rightUndo (normalizeLocal @{keyEq} provision input)))
        normalizedSame = localStateRuntimeNormalizationEqual keyEq provision
          (undos input)
        0 olderAtLeft : LocalStateRuntimeRelated
          (leftAccumulator (normalizeLocal @{keyEq} provision
            (leftUndo (normalizeLocal @{keyEq} provision input))))
          (rightAccumulator (normalizeLocal @{keyEq} provision
            (leftUndo (normalizeLocal @{keyEq} provision input))))
        olderAtLeft = older (normalizeLocal @{keyEq} provision
          (leftUndo (normalizeLocal @{keyEq} provision input)))
    in replace
      {p = \rightInput => LocalStateRuntimeRelated
        (leftAccumulator (normalizeLocal @{keyEq} provision
          (leftUndo (normalizeLocal @{keyEq} provision input))))
        (rightAccumulator rightInput)}
      normalizedSame olderAtLeft

||| Full lifecycle-control relation. Unlike `LifecycleShape`, this retains the
||| remaining iterator, accumulator, committed view, and failure outcome.
public export
data LifecycleControlRelated :
  {key : Type} -> {value : key -> Type} ->
  {world, error, name : Type} -> {deps : List key} ->
  {provision : CoeffectSpec key} ->
  Lifecycle key value world error name deps provision ->
  Lifecycle key value world error name deps provision -> Type where
  InactiveControls :
    {key : Type} -> {value : key -> Type} ->
    {world, error, name : Type} -> {deps : List key} ->
    {provision : CoeffectSpec key} ->
    {leftOutcome, rightOutcome : Maybe error} ->
    leftOutcome = rightOutcome ->
    LifecycleControlRelated
      (Inactive {key = key} {value = value} {world = world} {error = error}
        {name = name} {deps = deps} {provision = provision} leftOutcome)
      (Inactive {key = key} {value = value} {world = world} {error = error}
        {name = name} {deps = deps} {provision = provision} rightOutcome)
  ReloadingControls :
    {key : Type} -> {value : key -> Type} ->
    {world, error, name : Type} -> {deps : List key} ->
    {provision : CoeffectSpec key} ->
    {leftRemaining, rightRemaining : List
      (StepEffect key value world error deps provision)} ->
    {leftAccumulator, rightAccumulator : LocalState key value world provision ->
      LocalState key value world provision} ->
    {leftView, rightView : View name deps} ->
    leftRemaining = rightRemaining ->
    AccumulatorRelated leftAccumulator rightAccumulator ->
    leftView = rightView ->
    LifecycleControlRelated
      (Reloading leftRemaining leftAccumulator leftView)
      (Reloading rightRemaining rightAccumulator rightView)
  ActiveControls :
    {key : Type} -> {value : key -> Type} ->
    {world, error, name : Type} -> {deps : List key} ->
    {provision : CoeffectSpec key} ->
    {leftAccumulator, rightAccumulator : LocalState key value world provision ->
      LocalState key value world provision} ->
    {leftView, rightView : View name deps} ->
    AccumulatorRelated leftAccumulator rightAccumulator ->
    leftView = rightView ->
    LifecycleControlRelated (Active leftAccumulator leftView)
      (Active rightAccumulator rightView)
  UnloadingControls :
    {key : Type} -> {value : key -> Type} ->
    {world, error, name : Type} -> {deps : List key} ->
    {provision : CoeffectSpec key} ->
    {leftAccumulator, rightAccumulator : LocalState key value world provision ->
      LocalState key value world provision} ->
    {leftView, rightView : View name deps} ->
    {leftOutcome, rightOutcome : Maybe error} ->
    AccumulatorRelated leftAccumulator rightAccumulator ->
    leftView = rightView -> leftOutcome = rightOutcome ->
    LifecycleControlRelated (Unloading leftAccumulator leftView leftOutcome)
      (Unloading rightAccumulator rightView rightOutcome)

||| Full per-fiber control relation. The shared `component` index keeps the
||| immutable dependency/provision/program triple exactly; parent and retired
||| status are explicit, and dynamic tables remain on the effect side.
public export
data FiberControlRelated :
  Fiber name key value world error -> Fiber name key value world error -> Type where
  FibersControlRelated :
    {component : Component key value world error} ->
    (leftParent, rightParent : Parent name) ->
    (leftRetired, rightRetired : Bool) ->
    (leftTable, rightTable : OwnedTable key value
      (componentProvisions component)) ->
    (leftLifecycle, rightLifecycle : Lifecycle key value world error name
      (dependencies (componentDependencies component))
      (componentProvisions component)) ->
    leftParent = rightParent -> leftRetired = rightRetired ->
    LifecycleControlRelated leftLifecycle rightLifecycle ->
    FiberControlRelated
      (MkFiber component leftParent leftRetired leftTable leftLifecycle)
      (MkFiber component rightParent rightRetired rightTable rightLifecycle)

public export
data FiberControlMaybeRelated :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  Maybe (Fiber name key value world error) ->
  Maybe (Fiber name key value world error) -> Type where
  NoControlFibers :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    FiberControlMaybeRelated
      {name = name} {key = key} {value = value} {world = world} {error = error}
      Nothing Nothing
  SomeControlFibers : FiberControlRelated left right ->
    FiberControlMaybeRelated (Just left) (Just right)

public export
0 lifecycleControlReflexive :
  {key : Type} -> {value : key -> Type} -> {world, error, name : Type} ->
  {deps : List key} -> {provision : CoeffectSpec key} ->
  (lifecycle : Lifecycle key value world error name deps provision) ->
  LifecycleControlRelated lifecycle lifecycle
lifecycleControlReflexive (Inactive outcome) = InactiveControls Refl
lifecycleControlReflexive (Reloading remaining accumulator view) =
  ReloadingControls Refl (\input => localStateRuntimeReflexive _) Refl
lifecycleControlReflexive {error} (Active accumulator view) =
  ActiveControls {error = error} (\input => localStateRuntimeReflexive _) Refl
lifecycleControlReflexive (Unloading accumulator view outcome) =
  UnloadingControls (\input => localStateRuntimeReflexive _) Refl Refl

public export
0 lifecycleControlSymmetric :
  {key : Type} -> {value : key -> Type} -> {world, error, name : Type} ->
  {deps : List key} -> {provision : CoeffectSpec key} ->
  {left, right : Lifecycle key value world error name deps provision} ->
  LifecycleControlRelated left right -> LifecycleControlRelated right left
lifecycleControlSymmetric (InactiveControls outcome) = InactiveControls (sym outcome)
lifecycleControlSymmetric (ReloadingControls remaining accumulator view) =
  ReloadingControls (sym remaining)
    (\input => localStateRuntimeSymmetric (accumulator input)) (sym view)
lifecycleControlSymmetric {error} (ActiveControls accumulator view) =
  ActiveControls {error = error}
    (\input => localStateRuntimeSymmetric (accumulator input)) (sym view)
lifecycleControlSymmetric (UnloadingControls accumulator view outcome) =
  UnloadingControls
    (\input => localStateRuntimeSymmetric (accumulator input))
    (sym view) (sym outcome)

public export
0 lifecycleControlTransitive :
  {key : Type} -> {value : key -> Type} -> {world, error, name : Type} ->
  {deps : List key} -> {provision : CoeffectSpec key} ->
  {first, middle, finalState : Lifecycle key value world error name deps provision} ->
  LifecycleControlRelated first middle -> LifecycleControlRelated middle finalState ->
  LifecycleControlRelated first finalState
lifecycleControlTransitive (InactiveControls left) (InactiveControls right) =
  InactiveControls (trans left right)
lifecycleControlTransitive (ReloadingControls leftRemaining leftAccumulator leftView)
  (ReloadingControls rightRemaining rightAccumulator rightView) =
    ReloadingControls (trans leftRemaining rightRemaining)
      (\input => localStateRuntimeTransitive
        (leftAccumulator input) (rightAccumulator input))
      (trans leftView rightView)
lifecycleControlTransitive {error} (ActiveControls leftAccumulator leftView)
  (ActiveControls rightAccumulator rightView) =
    ActiveControls {error = error}
      (\input => localStateRuntimeTransitive
        (leftAccumulator input) (rightAccumulator input))
      (trans leftView rightView)
lifecycleControlTransitive (UnloadingControls leftAccumulator leftView leftOutcome)
  (UnloadingControls rightAccumulator rightView rightOutcome) =
    UnloadingControls
      (\input => localStateRuntimeTransitive
        (leftAccumulator input) (rightAccumulator input))
      (trans leftView rightView) (trans leftOutcome rightOutcome)

public export
0 fiberControlReflexive : (fiber : Fiber name key value world error) ->
  FiberControlRelated fiber fiber
fiberControlReflexive (MkFiber component parent retiredFlag table lifecycle) =
  FibersControlRelated parent parent retiredFlag retiredFlag table table lifecycle
    lifecycle Refl Refl (lifecycleControlReflexive lifecycle)

public export
0 fiberControlSymmetric :
  FiberControlRelated left right -> FiberControlRelated right left
fiberControlSymmetric
  (FibersControlRelated leftParent rightParent leftRetired rightRetired leftTable
    rightTable leftLifecycle rightLifecycle parentEq retiredEq lifecycleEq) =
      FibersControlRelated rightParent leftParent rightRetired leftRetired rightTable
        leftTable rightLifecycle leftLifecycle (sym parentEq) (sym retiredEq)
        (lifecycleControlSymmetric lifecycleEq)

public export
0 fiberControlTransitive :
  FiberControlRelated first middle -> FiberControlRelated middle finalState ->
  FiberControlRelated first finalState
fiberControlTransitive
  (FibersControlRelated firstParent middleParent firstRetired middleRetired
    firstTable middleTable firstLifecycle middleLifecycle firstParentEq
    firstRetiredEq firstLifecycleEq)
  (FibersControlRelated middleParent finalParent middleRetired finalRetired
    middleTable finalTable middleLifecycle finalLifecycle secondParentEq
    secondRetiredEq secondLifecycleEq) =
      FibersControlRelated firstParent finalParent firstRetired finalRetired
        firstTable finalTable firstLifecycle finalLifecycle
        (trans firstParentEq secondParentEq) (trans firstRetiredEq secondRetiredEq)
        (lifecycleControlTransitive firstLifecycleEq secondLifecycleEq)

public export
0 fiberControlMaybeReflexive : (fiber : Maybe (Fiber name key value world error)) ->
  FiberControlMaybeRelated fiber fiber
fiberControlMaybeReflexive Nothing = NoControlFibers
fiberControlMaybeReflexive (Just fiber) = SomeControlFibers (fiberControlReflexive fiber)

public export
0 fiberControlMaybeSymmetric :
  FiberControlMaybeRelated left right -> FiberControlMaybeRelated right left
fiberControlMaybeSymmetric NoControlFibers = NoControlFibers
fiberControlMaybeSymmetric (SomeControlFibers relation) =
  SomeControlFibers (fiberControlSymmetric relation)

public export
0 fiberControlMaybeTransitive :
  FiberControlMaybeRelated first middle ->
  FiberControlMaybeRelated middle finalState ->
  FiberControlMaybeRelated first finalState
fiberControlMaybeTransitive NoControlFibers NoControlFibers = NoControlFibers
fiberControlMaybeTransitive (SomeControlFibers first)
  (SomeControlFibers second) = SomeControlFibers (fiberControlTransitive first second)

||| Section 4's control-field side of Equation 53, pointwise to avoid function
||| extensionality. Domain, component program/specification, parent, retirement,
||| iterator, accumulator, view, and outcome are all retained.
public export
record ControlEquivalent
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name)
  (left, right : SystemState name key value world error) where
  constructor MkControlEquivalent
  0 controlPointwise : (n : name) -> FiberControlMaybeRelated
    (lookupFiber @{nameEq} {key = key} {value = value} {world = world}
      {error = error} n (registry left))
    (lookupFiber @{nameEq} {key = key} {value = value} {world = world}
      {error = error} n (registry right))

||| Effect/control conjunction used by Lemma 72 and Theorem 73. This finite
||| mechanization uses exact full-effect agreement, which is stronger than the
||| paper's open observational equivalence, and the full Equation-53 control
||| relation above.
public export
record SystemEquivalent
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (left, right : SystemState name key value world error) where
  constructor MkSystemEquivalent
  0 effectsEquivalent : EffectStateRelated keyEq
    (projectEffectState @{nameEq} left) (projectEffectState @{nameEq} right)
  0 controlsEquivalent : ControlEquivalent name key world error value nameEq
    left right

||| Paper Lemma 56: a bijection between fresh-name choices. External root names
||| are constrained separately to fixed points.
public export
record NameBijection (name : Type) where
  constructor MkNameBijection
  renameForward : name -> name
  renameBackward : name -> name
  0 renameLeftInverse : (n : name) -> renameBackward (renameForward n) = n
  0 renameRightInverse : (n : name) -> renameForward (renameBackward n) = n

public export
identityNameBijection : NameBijection name
identityNameBijection = MkNameBijection id id (\n => Refl) (\n => Refl)

public export
data ParentRelatedBy : NameBijection name -> Parent name -> Parent name -> Type where
  RootsRelated : ParentRelatedBy renaming Root Root
  ChildrenRelated : renameForward renaming leftParent = rightParent ->
    ParentRelatedBy renaming (ChildOf leftParent) (ChildOf rightParent)

public export
ViewRelatedBy : NameBijection name -> View name deps -> View name deps -> Type
ViewRelatedBy renaming left right =
  map (renameForward renaming) (viewProviders left) = viewProviders right

||| Full Equation-53 lifecycle relation transported through a name bijection.
public export
data LifecycleRelatedBy :
  {key : Type} -> {value : key -> Type} ->
  {world, error, name : Type} -> {deps : List key} ->
  {provision : CoeffectSpec key} ->
  (renaming : NameBijection name) ->
  Lifecycle key value world error name deps provision ->
  Lifecycle key value world error name deps provision -> Type where
  RenamedInactive :
    {key : Type} -> {value : key -> Type} ->
    {world, error, name : Type} -> {deps : List key} ->
    {provision : CoeffectSpec key} -> {renaming : NameBijection name} ->
    {leftOutcome, rightOutcome : Maybe error} ->
    leftOutcome = rightOutcome ->
    LifecycleRelatedBy renaming
      (Inactive {key = key} {value = value} {world = world} {error = error}
        {name = name} {deps = deps} {provision = provision} leftOutcome)
      (Inactive {key = key} {value = value} {world = world} {error = error}
        {name = name} {deps = deps} {provision = provision} rightOutcome)
  RenamedReloading :
    {key : Type} -> {value : key -> Type} ->
    {world, error, name : Type} -> {deps : List key} ->
    {provision : CoeffectSpec key} -> {renaming : NameBijection name} ->
    {leftRemaining, rightRemaining : List
      (StepEffect key value world error deps provision)} ->
    {leftAccumulator, rightAccumulator : LocalState key value world provision ->
      LocalState key value world provision} ->
    {leftView, rightView : View name deps} ->
    leftRemaining = rightRemaining ->
    AccumulatorRelated leftAccumulator rightAccumulator ->
    ViewRelatedBy renaming leftView rightView ->
    LifecycleRelatedBy renaming
      (Reloading leftRemaining leftAccumulator leftView)
      (Reloading rightRemaining rightAccumulator rightView)
  RenamedActive :
    {key : Type} -> {value : key -> Type} ->
    {world, error, name : Type} -> {deps : List key} ->
    {provision : CoeffectSpec key} -> {renaming : NameBijection name} ->
    {leftAccumulator, rightAccumulator : LocalState key value world provision ->
      LocalState key value world provision} ->
    {leftView, rightView : View name deps} ->
    AccumulatorRelated leftAccumulator rightAccumulator ->
    ViewRelatedBy renaming leftView rightView ->
    LifecycleRelatedBy renaming (Active leftAccumulator leftView)
      (Active rightAccumulator rightView)
  RenamedUnloading :
    {key : Type} -> {value : key -> Type} ->
    {world, error, name : Type} -> {deps : List key} ->
    {provision : CoeffectSpec key} -> {renaming : NameBijection name} ->
    {leftAccumulator, rightAccumulator : LocalState key value world provision ->
      LocalState key value world provision} ->
    {leftView, rightView : View name deps} ->
    {leftOutcome, rightOutcome : Maybe error} ->
    AccumulatorRelated leftAccumulator rightAccumulator ->
    ViewRelatedBy renaming leftView rightView ->
    leftOutcome = rightOutcome ->
    LifecycleRelatedBy renaming
      (Unloading leftAccumulator leftView leftOutcome)
      (Unloading rightAccumulator rightView rightOutcome)

public export
data FiberRelatedBy :
  (renaming : NameBijection name) ->
  Fiber name key value world error -> Fiber name key value world error -> Type where
  RenamedFibers :
    {component : Component key value world error} ->
    (leftParent, rightParent : Parent name) ->
    (leftRetired, rightRetired : Bool) ->
    (leftTable, rightTable : OwnedTable key value
      (componentProvisions component)) ->
    (leftLifecycle, rightLifecycle : Lifecycle key value world error name
      (dependencies (componentDependencies component))
      (componentProvisions component)) ->
    ParentRelatedBy renaming leftParent rightParent ->
    leftRetired = rightRetired ->
    LifecycleRelatedBy renaming leftLifecycle rightLifecycle ->
    FiberRelatedBy renaming
      (MkFiber component leftParent leftRetired leftTable leftLifecycle)
      (MkFiber component rightParent rightRetired rightTable rightLifecycle)

public export
data MaybeFiberRelatedBy :
  (renaming : NameBijection name) ->
  Maybe (Fiber name key value world error) ->
  Maybe (Fiber name key value world error) -> Type where
  RenamedAbsent : MaybeFiberRelatedBy renaming Nothing Nothing
  RenamedPresent : FiberRelatedBy renaming left right ->
    MaybeFiberRelatedBy renaming (Just left) (Just right)

public export
record SystemEquivalentByRenaming
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (renaming : NameBijection name)
  (left, right : SystemState name key value world error) where
  constructor MkSystemEquivalentByRenaming
  0 renamedAmbient : worldState left = worldState right
  0 renamedTables : (n : name) -> (k : key) ->
    lookupBinding {key = key} {value = value} k
      (effectTables (projectEffectState @{nameEq} left) n) =
    lookupBinding {key = key} {value = value} k
      (effectTables (projectEffectState @{nameEq} right)
        (renameForward renaming n))
  0 renamedControls : (n : name) -> MaybeFiberRelatedBy renaming
    (lookupFiber @{nameEq} {key = key} {value = value} {world = world}
      {error = error} n (registry left))
    (lookupFiber @{nameEq} {key = key} {value = value} {world = world}
      {error = error} (renameForward renaming n) (registry right))

||| A shared orchestration subsequence. Lifecycle steps may be inserted or
||| deleted independently, while O-Insert/O-Retire/O-Remove actions must occur
||| in the same order and carry the very same runtime component values.
public export
data SameOrchestration :
  {leftFirst, leftLast, rightFirst, rightLast :
    SystemState name key value world error} ->
  Transitions leftFirst leftLast -> Transitions rightFirst rightLast -> Type where
  SameOrchestrationEnd : SameOrchestration NoTransitions NoTransitions
  SkipLeftLifecycle :
    (transition : Transition leftFirst leftMiddle) ->
    (leftRest : Transitions leftMiddle leftLast) ->
    isLifecycleAction (transitionAction transition) = True ->
    SameOrchestration leftRest rightTrace ->
    SameOrchestration (MoreTransitions transition leftRest) rightTrace
  SkipRightLifecycle :
    (transition : Transition rightFirst rightMiddle) ->
    (rightRest : Transitions rightMiddle rightLast) ->
    isLifecycleAction (transitionAction transition) = True ->
    SameOrchestration leftTrace rightRest ->
    SameOrchestration leftTrace (MoreTransitions transition rightRest)
  MatchOrchestration :
    (action : Action name key value world error) ->
    (leftTransition : Transition leftFirst leftMiddle) ->
    (leftRest : Transitions leftMiddle leftLast) ->
    (rightTransition : Transition rightFirst rightMiddle) ->
    (rightRest : Transitions rightMiddle rightLast) ->
    isLifecycleAction action = False ->
    transitionAction leftTransition = action ->
    transitionAction rightTransition = action ->
    SameOrchestration leftRest rightRest ->
    SameOrchestration (MoreTransitions leftTransition leftRest)
      (MoreTransitions rightTransition rightRest)

||| A unique enumeration of the support set that linearizes the transitive
||| closure of both halves of Equation 62.
public export
record LinearizesSupport
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (state : SystemState name key value world error)
  (order : List name) where
  constructor MkLinearizesSupport
  0 orderUnique : UniqueKeys order
  0 orderSound : (n : name) -> Elem n order ->
    isSupported @{nameEq} @{keyEq} n state = True
  0 orderComplete : (n : name) ->
    isSupported @{nameEq} @{keyEq} n state = True -> Elem n order
  0 supportPathsOrdered : (lower, upper : name) ->
    SupportPath nameEq state lower upper ->
    Elem lower order -> Elem upper order ->
    BeforeIn lower upper order

public export
supportedActiveAt : DecEq name => name -> SystemState name key value world error -> Bool
supportedActiveAt n state = case lookupFiber n (registry state) of
  Nothing => False
  Just fiber => isActive (fiberLifecycle fiber)

||| Every transition of a contiguous canonical episode block is either a
||| lifecycle action of its selected actor or an explicit child registration
||| yielded within that actor's Reloading phase. The schedule-wide discipline
||| supplies the tag/catalog provenance for the latter.
public export
data ActorLifecycleOnly :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (selected : name) -> Transitions first finalState -> Type where
  ActorLifecycleEnd : ActorLifecycleOnly selected NoTransitions
  ActorLifecycleStep :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    isLifecycleAction (transitionAction transition) = True ->
    transitionActor transition = selected ->
    ActorLifecycleOnly selected rest ->
    ActorLifecycleOnly selected (MoreTransitions transition rest)
  ActorYieldedRegistrationStep :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    transitionAction transition =
      OInsert child (ChildOf selected) childComponent ->
    ActorLifecycleOnly selected rest ->
    ActorLifecycleOnly selected (MoreTransitions transition rest)

||| No lifecycle step of the selected actor occurs in a trace segment.
public export
data NoLifecycleBy :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (selected : name) -> Transitions first finalState -> Type where
  NoLifecycleByEnd : NoLifecycleBy selected NoTransitions
  NoLifecycleByStep :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    (isLifecycleAction (transitionAction transition) = True ->
      Not (transitionActor transition = selected)) ->
    NoLifecycleBy selected rest ->
    NoLifecycleBy selected (MoreTransitions transition rest)

||| A single open final episode represented as one contiguous actor-only block.
||| The no-earlier/no-later fields exclude a second episode of the same fiber.
public export
record LocatedOpenEpisodeBlock
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState) where
  constructor MkLocatedOpenEpisodeBlock
  blockPreStart : SystemState name key value world error
  blockStart : SystemState name key value world error
  blockEnd : SystemState name key value world error
  traceBeforeBlock : Transitions initial blockPreStart
  blockOpening : BeginStep nameEq keyEq selected blockPreStart blockStart
  blockBody : Transitions blockStart blockEnd
  blockBodyInstalled : InstalledTrace name key world error value nameEq keyEq
    selected blockBody
  blockActorOnly : ActorLifecycleOnly selected blockBody
  traceAfterBlock : Transitions blockEnd finalState
  noEarlierLifecycle : NoLifecycleBy selected traceBeforeBlock
  noLaterLifecycle : NoLifecycleBy selected traceAfterBlock
  blockActiveAtFinal : supportedActiveAt @{nameEq} selected finalState = True
  0 blockDecomposition : appendTransitions traceBeforeBlock
    (MoreTransitions (beginTransition blockOpening)
      (appendTransitions blockBody traceAfterBlock)) = global

public export
prefixToBlockOpening :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {initial, finalState : SystemState name key value world error} ->
  {global : Transitions initial finalState} ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
    selected global) ->
  Transitions initial (blockStart block)
prefixToBlockOpening {initial} block = appendTransitions (traceBeforeBlock block)
  (MoreTransitions (beginTransition (blockOpening block)) NoTransitions)

public export
prefixThroughBlock :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {initial, finalState : SystemState name key value world error} ->
  {global : Transitions initial finalState} ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
    selected global) ->
  Transitions initial (blockEnd block)
prefixThroughBlock {initial} block = appendTransitions (prefixToBlockOpening block)
  (blockBody block)

||| Same-trace ordering of two contiguous blocks.
public export
record BlockBefore
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState)
  (earlierName, laterName : name)
  (earlier : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
    earlierName global)
  (later : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
    laterName global) where
  constructor MkBlockBefore
  betweenBlocks : Transitions (blockEnd earlier) (blockPreStart later)
  0 blocksOrderedInGlobal : prefixToBlockOpening later =
    appendTransitions (prefixThroughBlock earlier)
      (appendTransitions betweenBlocks
        (MoreTransitions (beginTransition (blockOpening later)) NoTransitions))

||| Every lifecycle action in the canonical trace acts on a supported name.
public export
data LifecycleActorsCovered :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (supportNames : List name) -> Transitions first finalState -> Type where
  LifecycleActorsCoveredEnd : LifecycleActorsCovered supportNames NoTransitions
  CoveredLifecycleStep :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    isLifecycleAction (transitionAction transition) = True ->
    Elem (transitionActor transition) supportNames ->
    LifecycleActorsCovered supportNames rest ->
    LifecycleActorsCovered supportNames (MoreTransitions transition rest)
  CoveredOrchestrationStep :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    isLifecycleAction (transitionAction transition) = False ->
    LifecycleActorsCovered supportNames rest ->
    LifecycleActorsCovered supportNames (MoreTransitions transition rest)

||| Stable accounting key for one registration birth within a trace. Raw names
||| may be reused after O-Remove, so a name alone does not identify the
||| generation that canonical deletion retained or withdrew.
public export
record RegistrationGeneration (name : Type) where
  constructor MkRegistrationGeneration
  generationName : name
  generationBirthOrdinal : Nat

public export
implementation DecEq name => DecEq (RegistrationGeneration name) where
  decEq (MkRegistrationGeneration leftName leftOrdinal)
    (MkRegistrationGeneration rightName rightOrdinal) =
      case decEq leftName rightName of
        No different => No (\Refl => different Refl)
        Yes Refl => case decEq leftOrdinal rightOrdinal of
          No different => No (\Refl => different Refl)
          Yes Refl => Yes Refl

||| Paper's registered-name endpoint alternatives: a name may be a vestigial
||| original entry withdrawn from the survivor, or it may already have been
||| O-Removed in the original and remain absent in the survivor.
public export
data WithdrawnNameResult :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (child : name) ->
  (originalFinal, survivingFinal : SystemState name key value world error) -> Type where
  VestigialNameWithdrawn :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {child : name} ->
    {originalFinal, survivingFinal : SystemState name key value world error} ->
    (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} {key = key} {value = value} {world = world}
      {error = error} child (registry originalFinal) = Just fiber ->
    retired fiber = True ->
    installed (fiberLifecycle fiber) = False ->
    bindings (ownedValues (fiberTable fiber)) = [] ->
    lookupFiber @{nameEq} {key = key} {value = value} {world = world}
      {error = error} child (registry survivingFinal) = Nothing ->
    WithdrawnNameResult nameEq child originalFinal survivingFinal
  NameAlreadyAbsent :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {child : name} ->
    {originalFinal, survivingFinal : SystemState name key value world error} ->
    lookupFiber @{nameEq} {key = key} {value = value} {world = world}
      {error = error} child (registry originalFinal) = Nothing ->
    lookupFiber @{nameEq} {key = key} {value = value} {world = world}
      {error = error} child (registry survivingFinal) = Nothing ->
    WithdrawnNameResult nameEq child originalFinal survivingFinal

public export
RawNamesWithdrawn :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (registered : List name) ->
  SystemState name key value world error ->
  SystemState name key value world error -> Type
RawNamesWithdrawn {name} nameEq registered originalFinal survivingFinal =
  (child : name) -> Elem child registered ->
  WithdrawnNameResult nameEq child originalFinal survivingFinal

||| Equation-53 agreement outside the names R withdrawn by deletion.
public export
ControlEquivalentOutside :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (registered : List name) ->
  SystemState name key value world error ->
  SystemState name key value world error -> Type
ControlEquivalentOutside {name} {key} {value} {world} {error} nameEq registered originalFinal survivingFinal =
  (n : name) -> Not (Elem n registered) -> FiberControlMaybeRelated
    (lookupFiber @{nameEq} n (registry originalFinal))
    (lookupFiber @{nameEq} n (registry survivingFinal))

||| A transition at a fiber inserted by the orchestrator: root O-Insert, or a
||| later O-Retire/O-Remove while that live root entry is present.
public export
data RootOrchestrationStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> Type where
  RootInsertStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} ->
    {before, afterState : SystemState name key value world error} ->
    {transition : Transition before afterState} -> {n : name} ->
    {component : Component key value world error} ->
    transitionAction transition = OInsert n Root component ->
    RootOrchestrationStep nameEq transition
  RootRetireStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} ->
    {before, afterState : SystemState name key value world error} ->
    {transition : Transition before afterState} -> {n : name} ->
    (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} n (registry before) = Just fiber ->
    fiberParent fiber = Root ->
    transitionAction transition = ORetire n ->
    RootOrchestrationStep nameEq transition
  RootRemoveStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} ->
    {before, afterState : SystemState name key value world error} ->
    {transition : Transition before afterState} -> {n : name} ->
    (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} n (registry before) = Just fiber ->
    fiberParent fiber = Root ->
    transitionAction transition = ORemove n ->
    RootOrchestrationStep nameEq transition

public export
data NoRootOrchestration :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  NoRootOrchestrationEnd : NoRootOrchestration nameEq NoTransitions
  NoRootOrchestrationStep :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    (RootOrchestrationStep nameEq transition -> Void) ->
    NoRootOrchestration nameEq rest ->
    NoRootOrchestration nameEq (MoreTransitions transition rest)

||| Every orchestration step at every root fiber—including unsupported roots
||| and O-Retire/O-Remove—precedes every lifecycle transition in the trace.
public export
data RootInputsBeforeLifecycle :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  RootInputsBeforeLifecycleEnd : RootInputsBeforeLifecycle nameEq NoTransitions
  RootInputsBeforeLifecycleStep :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    (isLifecycleAction (transitionAction transition) = True ->
      NoRootOrchestration nameEq rest) ->
    RootInputsBeforeLifecycle nameEq rest ->
    RootInputsBeforeLifecycle nameEq (MoreTransitions transition rest)

||| Same external orchestration inputs under the explicit-registration
||| specialization. Root inputs must match in order; lifecycle steps and
||| provenance-disciplined child insert/retire/remove steps are internal and may
||| be removed by canonical deletion.
public export
data SameExternalOrchestration :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {leftFirst, leftLast, rightFirst, rightLast :
    SystemState name key value world error} ->
  Transitions leftFirst leftLast -> Transitions rightFirst rightLast -> Type where
  SameExternalOrchestrationEnd :
    SameExternalOrchestration nameEq NoTransitions NoTransitions
  SkipLeftInternal :
    (transition : Transition leftFirst leftMiddle) ->
    (leftRest : Transitions leftMiddle leftLast) ->
    (RootOrchestrationStep nameEq transition -> Void) ->
    SameExternalOrchestration nameEq leftRest rightTrace ->
    SameExternalOrchestration nameEq
      (MoreTransitions transition leftRest) rightTrace
  SkipRightInternal :
    (transition : Transition rightFirst rightMiddle) ->
    (rightRest : Transitions rightMiddle rightLast) ->
    (RootOrchestrationStep nameEq transition -> Void) ->
    SameExternalOrchestration nameEq leftTrace rightRest ->
    SameExternalOrchestration nameEq leftTrace
      (MoreTransitions transition rightRest)
  MatchExternalInput :
    (action : Action name key value world error) ->
    (leftTransition : Transition leftFirst leftMiddle) ->
    (leftRest : Transitions leftMiddle leftLast) ->
    RootOrchestrationStep nameEq leftTransition ->
    (rightTransition : Transition rightFirst rightMiddle) ->
    (rightRest : Transitions rightMiddle rightLast) ->
    RootOrchestrationStep nameEq rightTransition ->
    transitionAction leftTransition = action ->
    transitionAction rightTransition = action ->
    SameExternalOrchestration nameEq leftRest rightRest ->
    SameExternalOrchestration nameEq
      (MoreTransitions leftTransition leftRest)
      (MoreTransitions rightTransition rightRest)

public export
transitionCount : Transitions first finalState -> Nat
transitionCount NoTransitions = 0
transitionCount (MoreTransitions transition rest) = S (transitionCount rest)

||| One action occurrence located by its dependent prefix. Canonical placement
||| uses these locations rather than raw action membership so two births of the
||| same raw name remain distinct.
public export
record LocatedActionOccurrence
  {initial, finalState : SystemState name key value world error}
  (action : Action name key value world error)
  (global : Transitions initial finalState) where
  constructor MkLocatedActionOccurrence
  actionBeforeState : SystemState name key value world error
  actionAfterState : SystemState name key value world error
  beforeActionOccurrence : Transitions initial actionBeforeState
  locatedTransition : Transition actionBeforeState actionAfterState
  afterActionOccurrence : Transitions actionAfterState finalState
  0 locatedAction : transitionAction locatedTransition = action
  0 actionOccurrenceDecomposition :
    appendTransitions beforeActionOccurrence
      (MoreTransitions locatedTransition afterActionOccurrence) = global

public export
locatedActionOrdinal : LocatedActionOccurrence action global -> Nat
locatedActionOrdinal occurrence = transitionCount (beforeActionOccurrence occurrence)

||| One occurrence/generation of an explicit child registration, identified by
||| its dependent prefix rather than only by its raw action value.
public export
record LocatedGeneratedRegistration
  {initial, finalState : SystemState name key value world error}
  (child, parent : name)
  (component : Component key value world error)
  (global : Transitions initial finalState) where
  constructor MkLocatedGeneratedRegistration
  registrationBefore : SystemState name key value world error
  registrationAfter : SystemState name key value world error
  beforeRegistration : Transitions initial registrationBefore
  registrationTransition : Transition registrationBefore registrationAfter
  afterRegistration : Transitions registrationAfter finalState
  0 registrationAction : transitionAction registrationTransition =
    OInsert child (ChildOf parent) component
  0 registrationDecomposition :
    appendTransitions beforeRegistration
      (MoreTransitions registrationTransition afterRegistration) = global

public export
registrationOrdinal : LocatedGeneratedRegistration child parent component global -> Nat
registrationOrdinal occurrence = transitionCount (beforeRegistration occurrence)

||| Stamp a located child-registration occurrence by its raw name and birth
||| ordinal in the containing trace.
public export
registrationGeneration :
  {child, parent : name} ->
  {component : Component key value world error} ->
  {global : Transitions initial finalState} ->
  LocatedGeneratedRegistration child parent component global ->
  RegistrationGeneration name
registrationGeneration {child} occurrence =
  MkRegistrationGeneration child (registrationOrdinal occurrence)

||| Stamp any located O-Insert, including an external root birth. The checked
||| transition at `actionBeforeState` supplies that generation's operational
||| freshness; later reuse receives a different ordinal.
public export
locatedRegistrationGeneration :
  {registered : name} -> {parent : Parent name} ->
  {component : Component key value world error} ->
  {global : Transitions initial finalState} ->
  LocatedActionOccurrence (OInsert registered parent component) global ->
  RegistrationGeneration name
locatedRegistrationGeneration {registered} occurrence =
  MkRegistrationGeneration registered (locatedActionOrdinal occurrence)

||| A bijection of registration *generations*, not of raw names.  The birth
||| ordinal is part of the key, so a raw name may be transported differently
||| at two distinct births.  This is the finite trace form of paper Lemma 56
||| needed when O-Remove permits later raw-name reuse.
public export
record RegistrationGenerationBijection (name : Type) where
  constructor MkRegistrationGenerationBijection
  generationForward : RegistrationGeneration name -> RegistrationGeneration name
  generationBackward : RegistrationGeneration name -> RegistrationGeneration name
  0 generationLeftInverse : (generation : RegistrationGeneration name) ->
    generationBackward (generationForward generation) = generation
  0 generationRightInverse : (generation : RegistrationGeneration name) ->
    generationForward (generationBackward generation) = generation

public export
identityRegistrationGenerationBijection : RegistrationGenerationBijection name
identityRegistrationGenerationBijection =
  MkRegistrationGenerationBijection id id (\generation => Refl)
    (\generation => Refl)

public export
isExternalRootBirthAction : Action name key value world error -> Bool
isExternalRootBirthAction (OInsert root Root component) = True
isExternalRootBirthAction action = False

||| Every historical external root birth is coupled to the same exact root
||| O-Insert occurrence on the other trace.  Root births retain their global
||| input order (as required by `SameExternalOrchestration`); internal actions
||| may interleave independently.  In particular, removed root generations
||| cannot be permuted to reassign their generated subtrees.
public export
data ExternalRootBirthCorrespondence :
  (renaming : RegistrationGenerationBijection name) ->
  (leftOrdinal : Nat) ->
  {leftFirst, leftFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) ->
  (rightOrdinal : Nat) ->
  {rightFirst, rightFinal : SystemState name key value world error} ->
  (right : Transitions rightFirst rightFinal) -> Type where
  ExternalRootBirthCorrespondenceEnd :
    ExternalRootBirthCorrespondence renaming leftOrdinal NoTransitions
      rightOrdinal NoTransitions
  SkipLeftNonExternalRootBirth :
    (action : Action name key value world error) ->
    (transition : Transition leftFirst leftMiddle) ->
    (leftRest : Transitions leftMiddle leftFinal) ->
    transitionAction transition = action ->
    isExternalRootBirthAction action = False ->
    ExternalRootBirthCorrespondence renaming (S leftOrdinal) leftRest
      rightOrdinal right ->
    ExternalRootBirthCorrespondence renaming leftOrdinal
      (MoreTransitions transition leftRest) rightOrdinal right
  SkipRightNonExternalRootBirth :
    (action : Action name key value world error) ->
    (transition : Transition rightFirst rightMiddle) ->
    (rightRest : Transitions rightMiddle rightFinal) ->
    transitionAction transition = action ->
    isExternalRootBirthAction action = False ->
    ExternalRootBirthCorrespondence renaming leftOrdinal left
      (S rightOrdinal) rightRest ->
    ExternalRootBirthCorrespondence renaming leftOrdinal left rightOrdinal
      (MoreTransitions transition rightRest)
  MatchExternalRootBirth :
    (leftTransition : Transition leftFirst leftMiddle) ->
    (leftRest : Transitions leftMiddle leftFinal) ->
    (rightTransition : Transition rightFirst rightMiddle) ->
    (rightRest : Transitions rightMiddle rightFinal) ->
    transitionAction leftTransition = OInsert root Root component ->
    transitionAction rightTransition = OInsert root Root component ->
    generationForward renaming
      (MkRegistrationGeneration root leftOrdinal) =
      MkRegistrationGeneration root rightOrdinal ->
    ExternalRootBirthCorrespondence renaming (S leftOrdinal) leftRest
      (S rightOrdinal) rightRest ->
    ExternalRootBirthCorrespondence renaming leftOrdinal
      (MoreTransitions leftTransition leftRest) rightOrdinal
      (MoreTransitions rightTransition rightRest)

||| Projection used by rejection regressions: the first exact external root
||| birth cannot map to another historical root generation.
public export
0 firstExternalRootBirthMapped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {leftFirst, leftMiddle, leftFinal, rightFirst, rightMiddle, rightFinal :
    SystemState name key value world error} ->
  {leftTransition : Transition leftFirst leftMiddle} ->
  {leftRest : Transitions leftMiddle leftFinal} ->
  {rightTransition : Transition rightFirst rightMiddle} ->
  {rightRest : Transitions rightMiddle rightFinal} ->
  {renaming : RegistrationGenerationBijection name} ->
  {leftOrdinal, rightOrdinal : Nat} -> {root : name} ->
  {component : Component key value world error} ->
  ExternalRootBirthCorrespondence renaming leftOrdinal
    (MoreTransitions leftTransition leftRest) rightOrdinal
    (MoreTransitions rightTransition rightRest) ->
  transitionAction leftTransition = OInsert root Root component ->
  transitionAction rightTransition = OInsert root Root component ->
  generationForward renaming
    (MkRegistrationGeneration root leftOrdinal) =
    MkRegistrationGeneration root rightOrdinal
firstExternalRootBirthMapped
  (MatchExternalRootBirth leftTransition leftRest rightTransition rightRest
    leftAction rightAction mapped tail) requestedLeft requestedRight =
      case trans (sym leftAction) requestedLeft of
        Refl => mapped
firstExternalRootBirthMapped
  (SkipLeftNonExternalRootBirth action transition rest transitionAction nonRoot tail)
  requestedLeft requestedRight =
    let observed = trans (sym (cong isExternalRootBirthAction transitionAction))
          (cong isExternalRootBirthAction requestedLeft) in
      case trans (sym nonRoot) observed of Refl impossible
firstExternalRootBirthMapped
  (SkipRightNonExternalRootBirth action transition rest transitionAction nonRoot tail)
  requestedLeft requestedRight =
    let observed = trans (sym (cong isExternalRootBirthAction transitionAction))
          (cong isExternalRootBirthAction requestedRight) in
      case trans (sym nonRoot) observed of Refl impossible

||| The generation environment carried by the correspondence scanner.  Its
||| entries are the last O-Insert births not followed by O-Remove in the
||| processed prefix.  The checked LTS guarantees at most one current entry per
||| raw name; replacement keeps the definition executable on arbitrary traces.
public export
GenerationEnvironment : Type -> Type
GenerationEnvironment name = List (name, RegistrationGeneration name)

public export
putCurrentGeneration : DecEq name => name -> RegistrationGeneration name ->
  GenerationEnvironment name -> GenerationEnvironment name
putCurrentGeneration selected generation [] = [(selected, generation)]
putCurrentGeneration selected generation ((candidate, current) :: rest) =
  case decEq selected candidate of
    Yes Refl => (selected, generation) :: rest
    No different => (candidate, current) ::
      putCurrentGeneration selected generation rest

public export
deleteCurrentGeneration : DecEq name => name -> GenerationEnvironment name ->
  GenerationEnvironment name
deleteCurrentGeneration selected [] = []
deleteCurrentGeneration selected ((candidate, current) :: rest) =
  case decEq selected candidate of
    Yes Refl => rest
    No different => (candidate, current) :: deleteCurrentGeneration selected rest

public export
lookupCurrentGeneration : DecEq name => name -> GenerationEnvironment name ->
  Maybe (RegistrationGeneration name)
lookupCurrentGeneration selected [] = Nothing
lookupCurrentGeneration selected ((candidate, current) :: rest) =
  case decEq selected candidate of
    Yes Refl => Just current
    No different => lookupCurrentGeneration selected rest

public export
advanceGenerationEnvironment : DecEq name => Nat ->
  Action name key value world error -> GenerationEnvironment name ->
  GenerationEnvironment name
advanceGenerationEnvironment ordinal (OInsert registered parent component) live =
  putCurrentGeneration registered
    (MkRegistrationGeneration registered ordinal) live
advanceGenerationEnvironment ordinal (ORemove removed) live =
  deleteCurrentGeneration removed live
advanceGenerationEnvironment ordinal action live = live

public export
isGeneratedRegistrationAction : Action name key value world error -> Bool
isGeneratedRegistrationAction (OInsert child (ChildOf parent) component) = True
isGeneratedRegistrationAction action = False

||| One activation episode of an exact parent registration generation.  The
||| opening ordinal distinguishes repeated L-Begin episodes of one long-lived
||| parent; it is an indexing stamp, not a globally compared schedule position.
public export
record RegistrationActivation (name : Type) where
  constructor MkRegistrationActivation
  activationParentGeneration : RegistrationGeneration name
  activationBeginOrdinal : Nat

||| Executable indexing state for one trace.  Live generations serve current
||| endpoint coupling.  Parent activations start at L-Begin and end at L-Unload,
||| and surviving-child counts are keyed by that activation, so an iterator's
||| position restarts when a parent reactivates.  Counts include only births
||| retained by the surviving-registration relation below.  Discarded
||| generations are stamped separately: this is the trace-derived evidence
||| that an unremoved current entry came from a deleted closing episode.
public export
record RegistrationIndexState (name : Type) where
  constructor MkRegistrationIndexState
  indexedLiveGenerations : GenerationEnvironment name
  indexedParentActivations : List (name, RegistrationActivation name)
  indexedSurvivingChildCounts : List (RegistrationActivation name, Nat)
  indexedDeletedGenerations : List (RegistrationGeneration name)

public export
emptyRegistrationIndex : RegistrationIndexState name
emptyRegistrationIndex = MkRegistrationIndexState [] [] [] []

public export
sameRegistrationGeneration : DecEq name =>
  RegistrationGeneration name -> RegistrationGeneration name -> Bool
sameRegistrationGeneration
  (MkRegistrationGeneration leftName leftOrdinal)
  (MkRegistrationGeneration rightName rightOrdinal) =
    case decEq leftName rightName of
      No different => False
      Yes Refl => leftOrdinal == rightOrdinal

public export
sameRegistrationActivation : DecEq name =>
  RegistrationActivation name -> RegistrationActivation name -> Bool
sameRegistrationActivation
  (MkRegistrationActivation leftParent leftBegin)
  (MkRegistrationActivation rightParent rightBegin) =
    sameRegistrationGeneration leftParent rightParent && leftBegin == rightBegin

public export
putParentActivation : DecEq name => name -> RegistrationActivation name ->
  List (name, RegistrationActivation name) ->
  List (name, RegistrationActivation name)
putParentActivation selected activation [] = [(selected, activation)]
putParentActivation selected activation ((candidate, current) :: rest) =
  case decEq selected candidate of
    Yes Refl => (selected, activation) :: rest
    No different => (candidate, current) ::
      putParentActivation selected activation rest

public export
deleteParentActivation : DecEq name => name ->
  List (name, RegistrationActivation name) ->
  List (name, RegistrationActivation name)
deleteParentActivation selected [] = []
deleteParentActivation selected ((candidate, current) :: rest) =
  case decEq selected candidate of
    Yes Refl => rest
    No different => (candidate, current) :: deleteParentActivation selected rest

public export
lookupParentActivation : DecEq name => name ->
  List (name, RegistrationActivation name) ->
  Maybe (RegistrationActivation name)
lookupParentActivation selected [] = Nothing
lookupParentActivation selected ((candidate, current) :: rest) =
  case decEq selected candidate of
    Yes Refl => Just current
    No different => lookupParentActivation selected rest

public export
childrenBornInActivation : DecEq name => RegistrationActivation name ->
  List (RegistrationActivation name, Nat) -> Nat
childrenBornInActivation activation [] = 0
childrenBornInActivation activation ((candidate, count) :: rest) =
  if sameRegistrationActivation activation candidate
     then count
     else childrenBornInActivation activation rest

public export
incrementChildrenBornInActivation : DecEq name => RegistrationActivation name ->
  List (RegistrationActivation name, Nat) ->
  List (RegistrationActivation name, Nat)
incrementChildrenBornInActivation activation [] = [(activation, 1)]
incrementChildrenBornInActivation activation ((candidate, count) :: rest) =
  if sameRegistrationActivation activation candidate
     then (candidate, S count) :: rest
     else (candidate, count) :: incrementChildrenBornInActivation activation rest

||| Advance the trace index without declaring a generated birth canonical.
||| In particular, child O-Insert updates the live-generation environment but
||| does not consume a surviving iterator position until the correspondence
||| classifies that birth as retained.
public export
advanceRegistrationIndex : DecEq name => Nat ->
  Action name key value world error -> RegistrationIndexState name ->
  RegistrationIndexState name
advanceRegistrationIndex ordinal (OInsert child (ChildOf parent) component)
  (MkRegistrationIndexState live activations counts deleted) =
    MkRegistrationIndexState
      (putCurrentGeneration child (MkRegistrationGeneration child ordinal) live)
      activations counts deleted
advanceRegistrationIndex ordinal (OInsert root Root component)
  (MkRegistrationIndexState live activations counts deleted) =
    MkRegistrationIndexState
      (putCurrentGeneration root (MkRegistrationGeneration root ordinal) live)
      activations counts deleted
advanceRegistrationIndex ordinal (ORemove removed)
  (MkRegistrationIndexState live activations counts deleted) =
    MkRegistrationIndexState (deleteCurrentGeneration removed live)
      (deleteParentActivation removed activations) counts deleted
advanceRegistrationIndex ordinal (LBegin parent)
  index@(MkRegistrationIndexState live activations counts deleted) =
    case lookupCurrentGeneration parent live of
      Nothing => index
      Just generation => MkRegistrationIndexState live
        (putParentActivation parent
          (MkRegistrationActivation generation ordinal) activations) counts deleted
advanceRegistrationIndex ordinal (LUnload parent)
  (MkRegistrationIndexState live activations counts deleted) =
    MkRegistrationIndexState live (deleteParentActivation parent activations) counts
      deleted
advanceRegistrationIndex ordinal action index = index

||| Advance over a generated birth classified as belonging to a closing parent
||| episode.  The birth remains in the live environment until an actual
||| O-Remove, but its exact generation stamp is recorded as discarded.
public export
advanceDeletedRegistrationIndex : DecEq name => Nat ->
  (child, parent : name) -> Component key value world error ->
  RegistrationIndexState name -> RegistrationIndexState name
advanceDeletedRegistrationIndex ordinal child parent component index =
  let advanced = advanceRegistrationIndex ordinal
        (OInsert child (ChildOf parent) component) index in
    MkRegistrationIndexState
      (indexedLiveGenerations advanced)
      (indexedParentActivations advanced)
      (indexedSurvivingChildCounts advanced)
      (MkRegistrationGeneration child ordinal :: indexedDeletedGenerations advanced)

||| Advance over a generated birth retained in the surviving registration
||| tree.  Only such births consume an activation-local iterator position.
public export
advanceSurvivingRegistrationIndex : DecEq name => Nat ->
  (child, parent : name) -> Component key value world error ->
  RegistrationIndexState name -> RegistrationIndexState name
advanceSurvivingRegistrationIndex ordinal child parent component
  index@(MkRegistrationIndexState live activations counts deleted) =
    let advanced = advanceRegistrationIndex ordinal
          (OInsert child (ChildOf parent) component) index in
    case lookupParentActivation parent activations of
      Nothing => advanced
      Just activation => MkRegistrationIndexState
        (indexedLiveGenerations advanced)
        (indexedParentActivations advanced)
        (incrementChildrenBornInActivation activation counts)
        (indexedDeletedGenerations advanced)

||| One executable generated-birth descriptor.  Parent generation and position
||| are scoped by the L-Begin activation live at the birth.  `Nothing` is
||| retained for malformed raw traces; every retained/deleted classification
||| below requires `Just`, so no child outside an activation can be matched.
public export
record RegistrationEvent
  (name, key, world, error : Type) (value : key -> Type) where
  constructor MkRegistrationEvent
  eventChild : name
  eventParent : name
  eventComponent : Component key value world error
  eventChildGeneration : RegistrationGeneration name
  eventParentActivation : Maybe (RegistrationActivation name)
  eventChildPosition : Nat

public export
registrationEventAt : DecEq name => Nat -> RegistrationIndexState name ->
  (child, parent : name) -> Component key value world error ->
  RegistrationEvent name key world error value
registrationEventAt ordinal
  (MkRegistrationIndexState live activations counts deleted)
  child parent component =
    let activation = lookupParentActivation parent activations
        position = case activation of
          Nothing => 0
          Just current => childrenBornInActivation current counts in
      MkRegistrationEvent child parent component
        (MkRegistrationGeneration child ordinal) activation position

||| No L-Unload of this raw parent occurs in the remaining trace.  Together
||| with the activation stamp at the birth, this identifies a registration in
||| the one parent episode that survives canonical deletion.
public export
data NoParentUnload :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (parent : name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  NoParentUnloadEnd : NoParentUnload parent NoTransitions
  NoParentUnloadStep :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    (transitionAction transition = LUnload parent -> Void) ->
    NoParentUnload parent rest ->
    NoParentUnload parent (MoreTransitions transition rest)

||| A retained birth is in the activation live at the event and that activation
||| never reaches L-Unload in the original trace.  These, and only these, enter
||| the surviving registration-tree bijection.
public export
record SurvivingRegistration
  (event : RegistrationEvent name key world error value)
  {first, finalState : SystemState name key value world error}
  (rest : Transitions first finalState) where
  constructor MkSurvivingRegistration
  survivingActivation : RegistrationActivation name
  0 survivingActivationPresent : eventParentActivation event =
    Just survivingActivation
  0 survivingParentEpisodeOpen : NoParentUnload (eventParent event) rest

||| An unmatched historical birth must carry the dual evidence: it occurred in
||| the activation stamped at the event and that activation later closes at an
||| L-Unload.  Checked lifecycle transitions ensure the first such L-Unload is
||| the right boundary of the activation current at the birth.  This is the
||| explicit proof obligation that excludes closing-episode births before the
||| surviving registration trees are compared.
public export
record DeletedClosingRegistration
  (event : RegistrationEvent name key world error value)
  {first, finalState : SystemState name key value world error}
  (rest : Transitions first finalState) where
  constructor MkDeletedClosingRegistration
  deletedActivation : RegistrationActivation name
  0 deletedActivationPresent : eventParentActivation event = Just deletedActivation
  0 deletedParentEpisodeCloses : ActionOccurs (LUnload (eventParent event)) rest

||| Two retained births represent the same iterator position in their respective
||| surviving parent activations.  Activation opening ordinals may differ with
||| scheduling; mapped parent generations, exact components, and positions must
||| agree.  There is no global child-birth ordering constraint.
public export
record RegistrationEventMatch
  (renaming : RegistrationGenerationBijection name)
  (left, right : RegistrationEvent name key world error value) where
  constructor MkRegistrationEventMatch
  0 matchedComponent : eventComponent left = eventComponent right
  leftMatchedActivation : RegistrationActivation name
  rightMatchedActivation : RegistrationActivation name
  0 leftActivationPresent : eventParentActivation left = Just leftMatchedActivation
  0 rightActivationPresent : eventParentActivation right = Just rightMatchedActivation
  0 matchedChildGeneration : generationForward renaming
    (eventChildGeneration left) = eventChildGeneration right
  0 matchedParentGeneration : generationForward renaming
    (activationParentGeneration leftMatchedActivation) =
    activationParentGeneration rightMatchedActivation
  0 matchedPerActivationPosition : eventChildPosition left = eventChildPosition right

||| Parent-local matching of canonical surviving generated births.  Births in
||| parent activations that later L-Unload are discarded with explicit
||| `DeletedClosingRegistration` evidence and never enter pending lists or
||| consume positions.  Retained births may be held pending while either trace
||| advances, so independent parents may interleave in any order.
public export
data RegistrationTraceCorrespondence :
  (nameEq : DecEq name) ->
  (renaming : RegistrationGenerationBijection name) ->
  (leftOrdinal : Nat) -> (leftIndex : RegistrationIndexState name) ->
  {leftFirst, leftFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) ->
  (leftFinalIndex : RegistrationIndexState name) ->
  (rightOrdinal : Nat) -> (rightIndex : RegistrationIndexState name) ->
  {rightFirst, rightFinal : SystemState name key value world error} ->
  (right : Transitions rightFirst rightFinal) ->
  (rightFinalIndex : RegistrationIndexState name) ->
  (pendingLeft, pendingRight :
    List (RegistrationEvent name key world error value)) -> Type where
  RegistrationCorrespondenceEnd :
    RegistrationTraceCorrespondence nameEq renaming
      leftOrdinal leftIndex NoTransitions leftIndex
      rightOrdinal rightIndex NoTransitions rightIndex [] []
  SkipLeftNonRegistration :
    (action : Action name key value world error) ->
    (transition : Transition leftFirst leftMiddle) ->
    (leftRest : Transitions leftMiddle leftFinal) ->
    transitionAction transition = action ->
    isGeneratedRegistrationAction action = False ->
    RegistrationTraceCorrespondence nameEq renaming
      (S leftOrdinal)
      (advanceRegistrationIndex @{nameEq} leftOrdinal action leftIndex)
      leftRest leftFinalIndex rightOrdinal rightIndex right rightFinalIndex
      pendingLeft pendingRight ->
    RegistrationTraceCorrespondence nameEq renaming
      leftOrdinal leftIndex (MoreTransitions transition leftRest) leftFinalIndex
      rightOrdinal rightIndex right rightFinalIndex pendingLeft pendingRight
  SkipRightNonRegistration :
    (action : Action name key value world error) ->
    (transition : Transition rightFirst rightMiddle) ->
    (rightRest : Transitions rightMiddle rightFinal) ->
    transitionAction transition = action ->
    isGeneratedRegistrationAction action = False ->
    RegistrationTraceCorrespondence nameEq renaming
      leftOrdinal leftIndex left leftFinalIndex
      (S rightOrdinal)
      (advanceRegistrationIndex @{nameEq} rightOrdinal action rightIndex)
      rightRest rightFinalIndex pendingLeft pendingRight ->
    RegistrationTraceCorrespondence nameEq renaming
      leftOrdinal leftIndex left leftFinalIndex rightOrdinal rightIndex
      (MoreTransitions transition rightRest) rightFinalIndex
      pendingLeft pendingRight
  DiscardLeftDeletedRegistration :
    (transition : Transition leftFirst leftMiddle) ->
    (leftRest : Transitions leftMiddle leftFinal) ->
    transitionAction transition = OInsert child (ChildOf parent) component ->
    DeletedClosingRegistration
      (registrationEventAt @{nameEq} leftOrdinal leftIndex child parent component)
      leftRest ->
    RegistrationTraceCorrespondence nameEq renaming
      (S leftOrdinal)
      (advanceDeletedRegistrationIndex @{nameEq} leftOrdinal child parent
        component leftIndex)
      leftRest leftFinalIndex rightOrdinal rightIndex right rightFinalIndex
      pendingLeft pendingRight ->
    RegistrationTraceCorrespondence nameEq renaming
      leftOrdinal leftIndex (MoreTransitions transition leftRest) leftFinalIndex
      rightOrdinal rightIndex right rightFinalIndex pendingLeft pendingRight
  DiscardRightDeletedRegistration :
    (transition : Transition rightFirst rightMiddle) ->
    (rightRest : Transitions rightMiddle rightFinal) ->
    transitionAction transition = OInsert child (ChildOf parent) component ->
    DeletedClosingRegistration
      (registrationEventAt @{nameEq} rightOrdinal rightIndex child parent component)
      rightRest ->
    RegistrationTraceCorrespondence nameEq renaming
      leftOrdinal leftIndex left leftFinalIndex
      (S rightOrdinal)
      (advanceDeletedRegistrationIndex @{nameEq} rightOrdinal child parent
        component rightIndex)
      rightRest rightFinalIndex pendingLeft pendingRight ->
    RegistrationTraceCorrespondence nameEq renaming
      leftOrdinal leftIndex left leftFinalIndex rightOrdinal rightIndex
      (MoreTransitions transition rightRest) rightFinalIndex
      pendingLeft pendingRight
  QueueLeftGeneratedRegistration :
    (transition : Transition leftFirst leftMiddle) ->
    (leftRest : Transitions leftMiddle leftFinal) ->
    transitionAction transition = OInsert child (ChildOf parent) component ->
    SurvivingRegistration
      (registrationEventAt @{nameEq} leftOrdinal leftIndex child parent component)
      leftRest ->
    RegistrationTraceCorrespondence nameEq renaming
      (S leftOrdinal)
      (advanceSurvivingRegistrationIndex @{nameEq} leftOrdinal
        child parent component leftIndex)
      leftRest leftFinalIndex rightOrdinal rightIndex right rightFinalIndex
      (registrationEventAt @{nameEq} leftOrdinal leftIndex child parent component ::
        pendingLeft) pendingRight ->
    RegistrationTraceCorrespondence nameEq renaming
      leftOrdinal leftIndex (MoreTransitions transition leftRest) leftFinalIndex
      rightOrdinal rightIndex right rightFinalIndex pendingLeft pendingRight
  QueueRightGeneratedRegistration :
    (transition : Transition rightFirst rightMiddle) ->
    (rightRest : Transitions rightMiddle rightFinal) ->
    transitionAction transition = OInsert child (ChildOf parent) component ->
    SurvivingRegistration
      (registrationEventAt @{nameEq} rightOrdinal rightIndex child parent component)
      rightRest ->
    RegistrationTraceCorrespondence nameEq renaming
      leftOrdinal leftIndex left leftFinalIndex
      (S rightOrdinal)
      (advanceSurvivingRegistrationIndex @{nameEq} rightOrdinal
        child parent component rightIndex)
      rightRest rightFinalIndex pendingLeft
      (registrationEventAt @{nameEq} rightOrdinal rightIndex child parent component ::
        pendingRight) ->
    RegistrationTraceCorrespondence nameEq renaming
      leftOrdinal leftIndex left leftFinalIndex rightOrdinal rightIndex
      (MoreTransitions transition rightRest) rightFinalIndex
      pendingLeft pendingRight
  MatchLeftWithPendingRight :
    (transition : Transition leftFirst leftMiddle) ->
    (leftRest : Transitions leftMiddle leftFinal) ->
    transitionAction transition = OInsert child (ChildOf parent) component ->
    SurvivingRegistration
      (registrationEventAt @{nameEq} leftOrdinal leftIndex child parent component)
      leftRest ->
    (rightPrefix : List (RegistrationEvent name key world error value)) ->
    (rightEvent : RegistrationEvent name key world error value) ->
    (rightSuffix : List (RegistrationEvent name key world error value)) ->
    RegistrationEventMatch renaming
      (registrationEventAt @{nameEq} leftOrdinal leftIndex child parent component)
      rightEvent ->
    RegistrationTraceCorrespondence nameEq renaming
      (S leftOrdinal)
      (advanceSurvivingRegistrationIndex @{nameEq} leftOrdinal
        child parent component leftIndex)
      leftRest leftFinalIndex rightOrdinal rightIndex right rightFinalIndex
      pendingLeft (rightPrefix ++ rightSuffix) ->
    RegistrationTraceCorrespondence nameEq renaming
      leftOrdinal leftIndex (MoreTransitions transition leftRest) leftFinalIndex
      rightOrdinal rightIndex right rightFinalIndex pendingLeft
      (rightPrefix ++ (rightEvent :: rightSuffix))
  MatchRightWithPendingLeft :
    (transition : Transition rightFirst rightMiddle) ->
    (rightRest : Transitions rightMiddle rightFinal) ->
    transitionAction transition = OInsert child (ChildOf parent) component ->
    SurvivingRegistration
      (registrationEventAt @{nameEq} rightOrdinal rightIndex child parent component)
      rightRest ->
    (leftPrefix : List (RegistrationEvent name key world error value)) ->
    (leftEvent : RegistrationEvent name key world error value) ->
    (leftSuffix : List (RegistrationEvent name key world error value)) ->
    RegistrationEventMatch renaming leftEvent
      (registrationEventAt @{nameEq} rightOrdinal rightIndex child parent component) ->
    RegistrationTraceCorrespondence nameEq renaming
      leftOrdinal leftIndex left leftFinalIndex
      (S rightOrdinal)
      (advanceSurvivingRegistrationIndex @{nameEq} rightOrdinal
        child parent component rightIndex)
      rightRest rightFinalIndex (leftPrefix ++ leftSuffix) pendingRight ->
    RegistrationTraceCorrespondence nameEq renaming
      leftOrdinal leftIndex left leftFinalIndex rightOrdinal rightIndex
      (MoreTransitions transition rightRest) rightFinalIndex
      (leftPrefix ++ (leftEvent :: leftSuffix)) pendingRight

||| Lemma-56 correspondence of generated registration trees, indexed by
||| generation rather than raw name.  The scanner can advance either trace and
||| holds generated events pending, so it imposes order only through the
||| per-parent positions in `RegistrationEventMatch`.
public export
record RegistrationCorrespondenceByGeneration
  (nameEq : DecEq name) (renaming : RegistrationGenerationBijection name)
  {leftFirst, leftFinal, rightFirst, rightFinal :
    SystemState name key value world error}
  (left : Transitions leftFirst leftFinal)
  (right : Transitions rightFirst rightFinal) where
  constructor MkRegistrationCorrespondenceByGeneration
  leftFinalIndex : RegistrationIndexState name
  rightFinalIndex : RegistrationIndexState name
  generationTraceCorrespondence : RegistrationTraceCorrespondence nameEq renaming
    0 (the (RegistrationIndexState name) DGamma.CP3.emptyRegistrationIndex)
    left leftFinalIndex
    0 (the (RegistrationIndexState name) DGamma.CP3.emptyRegistrationIndex)
    right rightFinalIndex [] []

public export
leftFinalGenerations :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {leftFirst, leftFinal, rightFirst, rightFinal :
    SystemState name key value world error} ->
  {nameEq : DecEq name} ->
  {renaming : RegistrationGenerationBijection name} ->
  {left : Transitions leftFirst leftFinal} ->
  {right : Transitions rightFirst rightFinal} ->
  RegistrationCorrespondenceByGeneration nameEq renaming left right ->
  GenerationEnvironment name
leftFinalGenerations registrations =
  indexedLiveGenerations (leftFinalIndex registrations)

public export
rightFinalGenerations :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {leftFirst, leftFinal, rightFirst, rightFinal :
    SystemState name key value world error} ->
  {nameEq : DecEq name} ->
  {renaming : RegistrationGenerationBijection name} ->
  {left : Transitions leftFirst leftFinal} ->
  {right : Transitions rightFirst rightFinal} ->
  RegistrationCorrespondenceByGeneration nameEq renaming left right ->
  GenerationEnvironment name
rightFinalGenerations registrations =
  indexedLiveGenerations (rightFinalIndex registrations)

public export
leftDeletedGenerations :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {leftFirst, leftFinal, rightFirst, rightFinal :
    SystemState name key value world error} ->
  {nameEq : DecEq name} ->
  {renaming : RegistrationGenerationBijection name} ->
  {left : Transitions leftFirst leftFinal} ->
  {right : Transitions rightFirst rightFinal} ->
  RegistrationCorrespondenceByGeneration nameEq renaming left right ->
  List (RegistrationGeneration name)
leftDeletedGenerations registrations =
  indexedDeletedGenerations (leftFinalIndex registrations)

public export
rightDeletedGenerations :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {leftFirst, leftFinal, rightFirst, rightFinal :
    SystemState name key value world error} ->
  {nameEq : DecEq name} ->
  {renaming : RegistrationGenerationBijection name} ->
  {left : Transitions leftFirst leftFinal} ->
  {right : Transitions rightFirst rightFinal} ->
  RegistrationCorrespondenceByGeneration nameEq renaming left right ->
  List (RegistrationGeneration name)
rightDeletedGenerations registrations =
  indexedDeletedGenerations (rightFinalIndex registrations)

||| Lemma 57's exact endpoint condition, augmented with the generation stamp
||| produced by the surviving-tree scanner.  A vestigial endpoint is not merely
||| unsupported: its current birth was classified as belonging to a deleted
||| closing parent episode, its fiber is retired and cleanly inactive, its
||| installed table is empty, it has no child, and it provides/supports nothing.
public export
record VestigialEndpointGeneration
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (currentGenerations : GenerationEnvironment name)
  (discardedGenerations : List (RegistrationGeneration name))
  (selected : name)
  (state : SystemState name key value world error) where
  constructor MkVestigialEndpointGeneration
  vestigialGeneration : RegistrationGeneration name
  0 vestigialGenerationCurrent : lookupCurrentGeneration @{nameEq} selected
    currentGenerations = Just vestigialGeneration
  0 vestigialBirthDiscarded : Elem vestigialGeneration discardedGenerations
  vestigialFiber : Fiber name key value world error
  0 vestigialFiberPresent : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} selected (registry state) = Just vestigialFiber
  0 vestigialRetired : retired vestigialFiber = True
  0 vestigialInactiveClean : fiberLifecycle vestigialFiber = Inactive Nothing
  0 vestigialInstalledKeysEmpty :
    bindings (ownedValues (fiberTable vestigialFiber)) = []
  0 vestigialHasNoChild : hasChild @{nameEq} {key = key} {value = value}
    {world = world} {error = error} selected (registry state) = False
  0 vestigialUnsupported : isSupported @{nameEq} @{keyEq} {key = key}
    {value = value} {world = world} {error = error} selected state = False

||| Executable checker for the full paper-Lemma-57 fiber shape. The discarded
||| generation arguments remain proofs from the trace scanner; all endpoint
||| inertness fields are checked from runtime state rather than asserted.
public export
vestigialEndpointGeneration :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (currentGenerations : GenerationEnvironment name) ->
  (discardedGenerations : List (RegistrationGeneration name)) ->
  (selected : name) -> (state : SystemState name key value world error) ->
  (generation : RegistrationGeneration name) ->
  (0 current : lookupCurrentGeneration @{nameEq} selected currentGenerations =
    Just generation) ->
  (0 discarded : Elem generation discardedGenerations) ->
  Maybe (VestigialEndpointGeneration name key world error value nameEq keyEq
    currentGenerations discardedGenerations selected state)
vestigialEndpointGeneration nameEq keyEq currentGenerations discardedGenerations
  selected state generation current discarded
  with (lookupFiber @{nameEq} selected (registry state)) proof found
  vestigialEndpointGeneration nameEq keyEq currentGenerations discardedGenerations
    selected state generation current discarded | Nothing = Nothing
  vestigialEndpointGeneration nameEq keyEq currentGenerations discardedGenerations
    selected state generation current discarded |
      Just fiber@(MkFiber component parent False table lifecycle) = Nothing
  vestigialEndpointGeneration nameEq keyEq currentGenerations discardedGenerations
    selected state generation current discarded |
      Just fiber@(MkFiber component parent True table (Inactive (Just failure))) =
        Nothing
  vestigialEndpointGeneration nameEq keyEq currentGenerations discardedGenerations
    selected state generation current discarded |
      Just fiber@(MkFiber component parent True table (Reloading remaining accumulator view)) =
        Nothing
  vestigialEndpointGeneration nameEq keyEq currentGenerations discardedGenerations
    selected state generation current discarded |
      Just fiber@(MkFiber component parent True table (Active accumulator view)) =
        Nothing
  vestigialEndpointGeneration nameEq keyEq currentGenerations discardedGenerations
    selected state generation current discarded |
      Just fiber@(MkFiber component parent True table
        (Unloading accumulator view outcome)) = Nothing
  vestigialEndpointGeneration nameEq keyEq currentGenerations discardedGenerations
    selected state generation current discarded |
      Just fiber@(MkFiber component parent True
        table@(MkOwnedTable (MkCoeffectContext (binding :: rest) unique) sound)
        (Inactive Nothing)) = Nothing
  vestigialEndpointGeneration nameEq keyEq currentGenerations discardedGenerations
    selected state generation current discarded |
      Just fiber@(MkFiber component parent True
        table@(MkOwnedTable (MkCoeffectContext [] unique) sound)
        (Inactive Nothing))
    with (hasChild @{nameEq} selected (registry state)) proof children
    vestigialEndpointGeneration nameEq keyEq currentGenerations discardedGenerations
      selected state generation current discarded |
        Just fiber@(MkFiber component parent True
          table@(MkOwnedTable (MkCoeffectContext [] unique) sound)
          (Inactive Nothing)) | True = Nothing
    vestigialEndpointGeneration nameEq keyEq currentGenerations discardedGenerations
      selected state generation current discarded |
        Just fiber@(MkFiber component parent True
          table@(MkOwnedTable (MkCoeffectContext [] unique) sound)
          (Inactive Nothing)) | False
      with (isSupported @{nameEq} @{keyEq} selected state) proof supported
      vestigialEndpointGeneration nameEq keyEq currentGenerations discardedGenerations
        selected state generation current discarded |
          Just fiber@(MkFiber component parent True
            table@(MkOwnedTable (MkCoeffectContext [] unique) sound)
            (Inactive Nothing)) | False | True = Nothing
      vestigialEndpointGeneration nameEq keyEq currentGenerations discardedGenerations
        selected state generation current discarded |
          Just fiber@(MkFiber component parent True
            table@(MkOwnedTable (MkCoeffectContext [] unique) sound)
            (Inactive Nothing)) | False | False =
              Just (MkVestigialEndpointGeneration generation current discarded
                (MkFiber component parent True
                  (MkOwnedTable (MkCoeffectContext [] unique) sound)
                  (Inactive Nothing))
                found Refl Refl Refl children supported)

||| The raw-name bijection used only to compare *non-vestigial current endpoint*
||| generations. Historical child births are governed by the generation
||| bijection above. Live roots are fixed because they are external names. A
||| current generation may be omitted from cross-trace coupling only by giving
||| the complete Lemma-57 evidence above, including its discarded birth stamp.
public export
record CurrentEndpointRenaming
  (nameEq : DecEq name) (keyEq : DecEq key)
  (generationRenaming : RegistrationGenerationBijection name)
  {leftFirst, leftFinal, rightFirst, rightFinal :
    SystemState name key value world error}
  (left : Transitions leftFirst leftFinal)
  (right : Transitions rightFirst rightFinal)
  (registrations : RegistrationCorrespondenceByGeneration nameEq
    generationRenaming left right) where
  constructor MkCurrentEndpointRenaming
  currentNameBijection : NameBijection name
  0 leftLiveRootFixed : (n : name) ->
    (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} n (registry leftFinal) = Just fiber ->
    fiberParent fiber = Root -> renameForward currentNameBijection n = n
  0 rightLiveRootFixed : (n : name) ->
    (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} n (registry rightFinal) = Just fiber ->
    fiberParent fiber = Root -> renameBackward currentNameBijection n = n
  0 leftCurrentGenerationMapped : (n : name) ->
    (leftGeneration : RegistrationGeneration name) ->
    lookupCurrentGeneration @{nameEq} n
      (leftFinalGenerations registrations) = Just leftGeneration ->
    Either
      (VestigialEndpointGeneration name key world error value nameEq keyEq
        (leftFinalGenerations registrations)
        (leftDeletedGenerations registrations) n leftFinal)
      (rightGeneration : RegistrationGeneration name **
       (generationForward generationRenaming leftGeneration = rightGeneration,
        lookupCurrentGeneration @{nameEq}
          (renameForward currentNameBijection n)
          (rightFinalGenerations registrations) = Just rightGeneration))
  0 rightCurrentGenerationMapped : (n : name) ->
    (rightGeneration : RegistrationGeneration name) ->
    lookupCurrentGeneration @{nameEq} n
      (rightFinalGenerations registrations) = Just rightGeneration ->
    Either
      (VestigialEndpointGeneration name key world error value nameEq keyEq
        (rightFinalGenerations registrations)
        (rightDeletedGenerations registrations) n rightFinal)
      (leftGeneration : RegistrationGeneration name **
       (generationBackward generationRenaming rightGeneration = leftGeneration,
        lookupCurrentGeneration @{nameEq}
          (renameBackward currentNameBijection n)
          (leftFinalGenerations registrations) = Just leftGeneration))

||| The host specialization packages paper Lemma 56 explicitly: external root
||| actions retain their exact raw order and every historical root birth is
||| generation-coupled to that occurrence; generated registration trees use a
||| parent-local generation bijection; and only the current endpoint receives a
||| raw-name bijection. This extra witness is necessary because O-Insert is an
||| explicit rule rather than a value actually returned by `runStepEffect`.
public export
record SameOrchestrationModuloGenerated
  {leftFirst, leftFinal, rightFirst, rightFinal :
    SystemState name key value world error}
  (nameEq : DecEq name) (keyEq : DecEq key)
  (left : Transitions leftFirst leftFinal)
  (right : Transitions rightFirst rightFinal) where
  constructor MkSameOrchestrationModuloGenerated
  generatedGenerationBijection : RegistrationGenerationBijection name
  sameExternalInputs : SameExternalOrchestration nameEq left right
  externalRootGenerationsCoupled : ExternalRootBirthCorrespondence
    generatedGenerationBijection 0 left 0 right
  generatedRegistrationTree : RegistrationCorrespondenceByGeneration nameEq
    generatedGenerationBijection left right
  endpointRenaming : CurrentEndpointRenaming nameEq keyEq
    generatedGenerationBijection left right generatedRegistrationTree

||| Pointwise control correspondence at a final endpoint. Non-vestigial names
||| must correspond exactly through the raw-name bijection. Domain mismatch is
||| admitted only when each present unmatched side carries the complete
||| trace-derived vestigial evidence; the both-present constructor deliberately
||| does not pretend that two unrelated vestigial components are equal.
public export
record EndpointFiberRelatedModuloVestigial
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {leftFirst, leftFinal, rightFirst, rightFinal :
    SystemState name key value world error}
  {left : Transitions leftFirst leftFinal}
  {right : Transitions rightFirst rightFinal}
  {generationRenaming : RegistrationGenerationBijection name}
  (registrations : RegistrationCorrespondenceByGeneration nameEq
    generationRenaming left right)
  (renaming : NameBijection name) (selected : name) where
  constructor MkEndpointFiberRelatedModuloVestigial
  0 endpointFiberDisposition :
    Either
      (MaybeFiberRelatedBy renaming
        (lookupFiber @{nameEq} {key = key} {value = value} {world = world}
          {error = error} selected (registry leftFinal))
        (lookupFiber @{nameEq} {key = key} {value = value} {world = world}
          {error = error} (renameForward renaming selected)
          (registry rightFinal)))
      (Either
        (VestigialEndpointGeneration name key world error value nameEq keyEq
          (leftFinalGenerations registrations)
          (leftDeletedGenerations registrations) selected leftFinal,
         lookupFiber @{nameEq} {key = key} {value = value} {world = world}
           {error = error} (renameForward renaming selected)
           (registry rightFinal) = Nothing)
        (Either
          (lookupFiber @{nameEq} {key = key} {value = value} {world = world}
             {error = error} selected (registry leftFinal) = Nothing,
           VestigialEndpointGeneration name key world error value nameEq keyEq
             (rightFinalGenerations registrations)
             (rightDeletedGenerations registrations)
             (renameForward renaming selected) rightFinal)
          (VestigialEndpointGeneration name key world error value nameEq keyEq
             (leftFinalGenerations registrations)
             (leftDeletedGenerations registrations) selected leftFinal,
           VestigialEndpointGeneration name key world error value nameEq keyEq
             (rightFinalGenerations registrations)
             (rightDeletedGenerations registrations)
             (renameForward renaming selected) rightFinal)))

||| Paper Lemma 72's outside-R endpoint relation transported through Lemma 56.
||| Effects remain exact (ambient state plus every table lookup under the raw
||| renaming). Controls correspond exactly on every non-vestigial domain point;
||| any unmatched present fiber on either side must be an inert discarded birth.
public export
record SystemEquivalentByRenamingModuloVestigial
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {leftFirst, leftFinal, rightFirst, rightFinal :
    SystemState name key value world error}
  {left : Transitions leftFirst leftFinal}
  {right : Transitions rightFirst rightFinal}
  {generationRenaming : RegistrationGenerationBijection name}
  (registrations : RegistrationCorrespondenceByGeneration nameEq
    generationRenaming left right)
  (renaming : NameBijection name) where
  constructor MkSystemEquivalentByRenamingModuloVestigial
  0 exactRenamedAmbient : worldState leftFinal = worldState rightFinal
  0 exactRenamedTables : (n : name) -> (k : key) ->
    lookupBinding {key = key} {value = value} k
      (effectTables (projectEffectState @{nameEq} leftFinal) n) =
    lookupBinding {key = key} {value = value} k
      (effectTables (projectEffectState @{nameEq} rightFinal)
        (renameForward renaming n))
  0 controlsModuloVestigial : (n : name) ->
    EndpointFiberRelatedModuloVestigial name key world error value nameEq keyEq
      registrations renaming n

||| Registration-tree preservation for one canonical reduction. Withdrawal is
||| keyed by `(raw name, birth ordinal)`, never by the raw name alone. Thus a
||| deleted child generation may share its raw name with a later live root
||| generation. Every retained canonical occurrence is also tied back to the
||| exact original generation that it represents.
public export
record CanonicalRegistrationCorrespondence
  {initial, originalFinal, canonicalFinal :
    SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (canonical : Transitions initial canonicalFinal)
  (withdrawn : List (RegistrationGeneration name)) where
  constructor MkCanonicalRegistrationCorrespondence
  canonicalToOriginal :
    {child, parent : name} ->
    {component : Component key value world error} ->
    LocatedGeneratedRegistration child parent component canonical ->
    LocatedGeneratedRegistration child parent component original
  originalRegistrationAccounted :
    {child, parent : name} ->
    {component : Component key value world error} ->
    (occurrence : LocatedGeneratedRegistration child parent component original) ->
    Either (Elem (registrationGeneration occurrence) withdrawn)
      (canonicalOccurrence :
        LocatedGeneratedRegistration child parent component canonical **
       registrationGeneration (canonicalToOriginal canonicalOccurrence) =
         registrationGeneration occurrence)
  0 canonicalOccurrenceInjective :
    {child, parent : name} ->
    {component : Component key value world error} ->
    (leftOccurrence, rightOccurrence :
      LocatedGeneratedRegistration child parent component canonical) ->
    registrationGeneration (canonicalToOriginal leftOccurrence) =
      registrationGeneration (canonicalToOriginal rightOccurrence) ->
    registrationGeneration leftOccurrence = registrationGeneration rightOccurrence
  0 withdrawnRegistrationRemoved :
    (generation : RegistrationGeneration name) -> Elem generation withdrawn ->
    (parent : name **
     component : Component key value world error **
     occurrence : LocatedGeneratedRegistration (generationName generation)
       parent component original **
     (registrationGeneration occurrence = generation,
      (canonicalParent : name) ->
      (canonicalComponent : Component key value world error) ->
      (canonicalOccurrence : LocatedGeneratedRegistration
        (generationName generation) canonicalParent canonicalComponent canonical) ->
      registrationGeneration (canonicalToOriginal canonicalOccurrence) =
        generation -> Void))

||| Paper Theorem 73's placement rule for inputs. All root orchestration steps
||| precede all lifecycle steps, while each explicit child registration precedes
||| the lifecycle block of the child it created.
public export
record CanonicalInputPlacement
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (supportState : SystemState name key value world error)
  (order : List name)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) where
  constructor MkCanonicalInputPlacement
  0 allRootInputsFirst : RootInputsBeforeLifecycle nameEq trace
  ||| Freshness and placement are stated for each located root birth, not for a
  ||| raw name globally. A later root birth may therefore reuse the raw name of
  ||| a withdrawn child generation.
  0 rootGenerationFresh :
    {root : name} -> {component : Component key value world error} ->
    (birth : LocatedActionOccurrence (OInsert root Root component) trace) ->
    lookupFiber @{nameEq} {key = key} {value = value} {world = world}
      {error = error} root (registry (actionBeforeState birth)) = Nothing
  0 rootGenerationBeforeLifecycle :
    {root : name} -> {component : Component key value world error} ->
    (birth : LocatedActionOccurrence (OInsert root Root component) trace) ->
    {action : Action name key value world error} ->
    (lifecycle : LocatedActionOccurrence action trace) ->
    isLifecycleAction action = True ->
    LT (locatedActionOrdinal birth) (locatedActionOrdinal lifecycle)
  ||| The surviving child is linked to one located birth generation. Its
  ||| checked O-Insert is fresh at that birth state and precedes every located
  ||| lifecycle occurrence of that child.
  0 childGenerationBeforeOwnLifecycle :
    (n, parent : name) -> Elem n order ->
    (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} n (registry supportState) = Just fiber ->
    fiberParent fiber = ChildOf parent ->
    (component : Component key value world error **
     birth : LocatedGeneratedRegistration n parent component trace **
     (lookupFiber @{nameEq} {key = key} {value = value} {world = world}
       {error = error} n (registry (registrationBefore birth)) = Nothing,
      (action : Action name key value world error) ->
      (lifecycle : LocatedActionOccurrence action trace) ->
      isLifecycleAction action = True -> actionOwner action = n ->
      LT (registrationOrdinal birth) (locatedActionOrdinal lifecycle)))

||| Endpoint relation used by canonical deletion. Unlike `SystemEquivalent`, it
||| explicitly permits a nonempty set of vestigial original names to be absent
||| from the canonical endpoint while retaining effects and full controls
||| outside that set.
|||
||| API caveat: this trace-free record does not validate the historical
||| `endpointWithdrawnGenerations` list by itself. Historical entries have
||| semantic force only when this value is the `canonicalEndpoint` of a
||| `CanonicalSchedule`, whose `canonicalRegistrationTree` proves that every
||| listed generation is an actual original child birth absent canonically.
public export
record CanonicalEndpointRelation
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (originalFinal, canonicalFinal : SystemState name key value world error) where
  constructor MkCanonicalEndpointRelation
  ||| Raw names actually absent from the canonical endpoint. This list is only
  ||| for comparing the current endpoint registries.
  endpointWithdrawnNames : List name
  ||| Historical child births deleted while canonicalizing. A generation may
  ||| appear here even when the same raw name denotes a later live endpoint
  ||| root and therefore does not appear in `endpointWithdrawnNames`.
  endpointWithdrawnGenerations : List (RegistrationGeneration name)
  0 endpointEffectsEquivalent : EffectStateRelated keyEq
    (projectEffectState @{nameEq} originalFinal)
    (projectEffectState @{nameEq} canonicalFinal)
  0 endpointControlsOutside : ControlEquivalentOutside nameEq
    endpointWithdrawnNames originalFinal canonicalFinal
  0 endpointNamesWithdrawn : RawNamesWithdrawn nameEq
    endpointWithdrawnNames originalFinal canonicalFinal
  ||| Every raw endpoint omission is justified by at least one deleted
  ||| generation of that raw name; the converse deliberately does not hold.
  0 endpointNameHasWithdrawnGeneration : (child : name) ->
    Elem child endpointWithdrawnNames ->
    (birth : Nat ** Elem (MkRegistrationGeneration child birth)
      endpointWithdrawnGenerations)

||| Finite canonical-form statement package under active repair: it retains the
||| verified Equation-62 order/block fields and exposes all-root input placement
||| plus endpoint withdrawal sets. This coupling is what validates the endpoint
||| relation's otherwise-unchecked historical metadata. Constructive
||| inhabitation remains open.
public export
record CanonicalSchedule
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal) where
  constructor MkCanonicalSchedule
  canonicalFinal : SystemState name key value world error
  canonicalTrace : Transitions initial canonicalFinal
  sameInputs : SameExternalOrchestration nameEq original canonicalTrace
  originalRegistrationDiscipline : RegistrationDiscipline protocol nameEq original
  canonicalRegistrationDiscipline : RegistrationDiscipline protocol nameEq
    canonicalTrace
  supportOrder : List name
  supportLinearization : LinearizesSupport name key world error value nameEq keyEq
    originalFinal supportOrder
  canonicalBlock : (n : name) -> Elem n supportOrder ->
    LocatedOpenEpisodeBlock name key world error value nameEq keyEq n canonicalTrace
  blocksFollowOrder : (earlier, later : name) ->
    (earlierIn : Elem earlier supportOrder) ->
    (laterIn : Elem later supportOrder) ->
    BeforeIn earlier later supportOrder ->
    BlockBefore name key world error value nameEq keyEq canonicalTrace
      earlier later (canonicalBlock earlier earlierIn) (canonicalBlock later laterIn)
  lifecycleCoverage : LifecycleActorsCovered supportOrder canonicalTrace
  inputPlacement : CanonicalInputPlacement name key world error value nameEq keyEq
    originalFinal supportOrder canonicalTrace
  canonicalEndpoint : CanonicalEndpointRelation name key world error value
    nameEq keyEq originalFinal canonicalFinal
  canonicalRegistrationTree : CanonicalRegistrationCorrespondence original
    canonicalTrace (endpointWithdrawnGenerations canonicalEndpoint)

||| Lemma 70, stated as pointwise equality so no finite-set quotient or function
||| extensionality is required.
public export
SupportMatchesActive : {name, key, world, error : Type} ->
  {value : key -> Type} -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  SystemState name key value world error -> Type
SupportMatchesActive {name} nameEq keyEq state = (n : name) ->
  isSupported @{nameEq} @{keyEq} n state = supportedActiveAt @{nameEq} n state

||| Paper Lemma 70 with the missing nested-registration/retirement provenance
||| exposed as `RegistrationDiscipline`; reachability alone is not sufficient.
||| Definition 69 is the component-level semantic property above.
||| Constructively implemented by
||| `DGamma.CP4Lemma70.supportAtQuiescenceTheoremProof`.
public export
supportAtQuiescenceTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
supportAtQuiescenceTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (state : SystemState name key value world error) ->
  (reached : ReachedFromEmpty name key world error value nameEq keyEq state) ->
  RegistrationDiscipline protocol nameEq (reachTrace reached) ->
  PrecedenceAcyclic nameEq state ->
  quiet @{nameEq} @{keyEq} state = True ->
  noFailedFibers state = True ->
  TraceComponentsTotal nameEq keyEq (reachTrace reached) ->
  SupportMatchesActive nameEq keyEq state

||| Lemma 71's effect-level transposition core. Control-field applicability
||| frames are separate debt, but the endpoint effect diamond is exactly the
||| generated-monoid commutation field of Definition 60.
public export
0 activationEffectTransposition :
  (independent : TraceIndependent name key world error value keyEq trace) ->
  (left, right : name) -> Not (left = right) ->
  (leftT : TraceEffectTransformation name key world error value left trace) ->
  (rightT : TraceEffectTransformation name key world error value right trace) ->
  PartialCommute (EffectStateEquivalence keyEq)
    (runTraceEffectTransformation leftT)
    (runTraceEffectTransformation rightT)
activationEffectTransposition
  (MkTraceIndependent commute yieldsStable) left right distinct leftT rightT =
  commute left right distinct leftT rightT

||| Mandatory action-filter witness used by paper Lemma 72. Kept actions are
||| replayed as checked transitions and carry proof that they are not deletable;
||| every deletable action is therefore structurally forced through DeleteAction.
public export
data ActionSubsequence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {originalFirst, originalFinal, survivingFirst, survivingFinal :
    SystemState name key value world error} ->
  (deletable : Action name key value world error -> Type) ->
  Transitions originalFirst originalFinal ->
  Transitions survivingFirst survivingFinal -> Type where
  ActionSubsequenceEnd : ActionSubsequence deletable NoTransitions NoTransitions
  KeepAction :
    (originalTransition : Transition originalFirst originalMiddle) ->
    (originalRest : Transitions originalMiddle originalFinal) ->
    (survivingTransition : Transition survivingFirst survivingMiddle) ->
    (survivingRest : Transitions survivingMiddle survivingFinal) ->
    Not (deletable (transitionAction originalTransition)) ->
    transitionAction originalTransition = transitionAction survivingTransition ->
    ActionSubsequence deletable originalRest survivingRest ->
    ActionSubsequence deletable
      (MoreTransitions originalTransition originalRest)
      (MoreTransitions survivingTransition survivingRest)
  DeleteAction :
    (originalTransition : Transition originalFirst originalMiddle) ->
    (originalRest : Transitions originalMiddle originalFinal) ->
    deletable (transitionAction originalTransition) ->
    ActionSubsequence deletable originalRest surviving ->
    ActionSubsequence deletable
      (MoreTransitions originalTransition originalRest) surviving

public export
RegisteredActor : List name -> Action name key value world error -> Type
RegisteredActor registered action = Elem (actionOwner action) registered

public export
data EpisodeDeletedActor : name -> List name ->
  Action name key value world error -> Type where
  DeleteEpisodeLifecycle :
    actionOwner action = selected ->
    isLifecycleAction action = True ->
    EpisodeDeletedActor selected registered action
  DeleteRegisteredActor : Elem (actionOwner action) registered ->
    EpisodeDeletedActor selected registered action

||| The exact registration generation owning one action occurrence. O-Insert
||| owns the fresh generation it creates; every other action belongs to the
||| generation current immediately before the step.
public export
actionGenerationAt : DecEq name => Nat -> GenerationEnvironment name ->
  Action name key value world error -> Maybe (RegistrationGeneration name)
actionGenerationAt ordinal live (OInsert inserted parent component) =
  Just (MkRegistrationGeneration inserted ordinal)
actionGenerationAt ordinal live action =
  lookupCurrentGeneration (actionOwner action) live

public export
GenerationOwnedActor :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> List (RegistrationGeneration name) -> Nat ->
  GenerationEnvironment name -> Action name key value world error -> Type
GenerationOwnedActor nameEq registered ordinal live action =
  (generation : RegistrationGeneration name **
    (actionGenerationAt @{nameEq} ordinal live action = Just generation,
     Elem generation registered))

||| Generation-indexed action filtering. The scanner state follows the original
||| trace even when a step is deleted, so a later raw-name reissue receives and
||| keeps its distinct birth ordinal.
public export
data GenerationActionSubsequence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {originalFirst, originalFinal, survivingFirst, survivingFinal :
    SystemState name key value world error} ->
  (nameEq : DecEq name) ->
  (deletable : Nat -> GenerationEnvironment name ->
    Action name key value world error -> Type) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  Transitions originalFirst originalFinal ->
  Transitions survivingFirst survivingFinal -> Type where
  GenerationActionSubsequenceEnd :
    GenerationActionSubsequence nameEq deletable ordinal live
      NoTransitions NoTransitions
  KeepGenerationAction :
    (originalTransition : Transition originalFirst originalMiddle) ->
    (originalRest : Transitions originalMiddle originalFinal) ->
    (survivingTransition : Transition survivingFirst survivingMiddle) ->
    (survivingRest : Transitions survivingMiddle survivingFinal) ->
    Not (deletable ordinal live (transitionAction originalTransition)) ->
    transitionAction originalTransition = transitionAction survivingTransition ->
    GenerationActionSubsequence nameEq deletable (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal
        (transitionAction originalTransition) live)
      originalRest survivingRest ->
    GenerationActionSubsequence nameEq deletable ordinal live
      (MoreTransitions originalTransition originalRest)
      (MoreTransitions survivingTransition survivingRest)
  DeleteGenerationAction :
    (originalTransition : Transition originalFirst originalMiddle) ->
    (originalRest : Transitions originalMiddle originalFinal) ->
    deletable ordinal live (transitionAction originalTransition) ->
    GenerationActionSubsequence nameEq deletable (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal
        (transitionAction originalTransition) live)
      originalRest surviving ->
    GenerationActionSubsequence nameEq deletable ordinal live
      (MoreTransitions originalTransition originalRest) surviving

||| Proof-producing scan of exact generation state through a dependent trace.
||| The final ordinal/environment are indices, avoiding any raw-name ambiguity.
public export
data GenerationTraceScan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> Nat -> GenerationEnvironment name ->
  Transitions first finalState -> Nat -> GenerationEnvironment name -> Type where
  GenerationTraceScanEnd :
    GenerationTraceScan nameEq ordinal live NoTransitions ordinal live
  GenerationTraceScanStep :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    GenerationTraceScan nameEq (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal
        (transitionAction transition) live)
      rest finalOrdinal finalLive ->
    GenerationTraceScan nameEq ordinal live
      (MoreTransitions transition rest) finalOrdinal finalLive

public export
data EpisodeGenerationDeletedActor :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> name -> List (RegistrationGeneration name) ->
  Nat -> GenerationEnvironment name -> Action name key value world error ->
  Type where
  DeleteEpisodeGenerationLifecycle :
    actionOwner action = selected ->
    isLifecycleAction action = True ->
    EpisodeGenerationDeletedActor nameEq selected registered ordinal live action
  DeleteRegisteredGeneration :
    GenerationOwnedActor nameEq registered ordinal live action ->
    EpisodeGenerationDeletedActor nameEq selected registered ordinal live action

public export
data IsBeginAction : Action name key value world error -> Type where
  ItIsLBegin : IsBeginAction (LBegin actor)

||| A later reuse of the same raw name is a different generation and is allowed
||| to begin; only the exact generated births in R are episode-free.
public export
data NoRegisteredEpisode :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> List (RegistrationGeneration name) -> Nat ->
  GenerationEnvironment name -> Transitions first finalState -> Type where
  NoRegisteredEpisodeEnd :
    NoRegisteredEpisode nameEq registered ordinal live NoTransitions
  NoRegisteredEpisodeStep :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    (IsBeginAction (transitionAction transition) ->
      GenerationOwnedActor nameEq registered ordinal live
        (transitionAction transition) -> Void) ->
    NoRegisteredEpisode nameEq registered (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal
        (transitionAction transition) live) rest ->
    NoRegisteredEpisode nameEq registered ordinal live
      (MoreTransitions transition rest)

||| One exact generated birth in the selected segment, stamped by the global
||| starting ordinal and paired with a later retirement in that same segment.
public export
record GeneratedDuring
  (name, key, world, error : Type) (value : key -> Type)
  (selected : name) (startOrdinal : Nat)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState)
  (generation : RegistrationGeneration name) where
  constructor MkGeneratedDuring
  generatedChild : name
  generatedComponent : Component key value world error
  generatedBirth : LocatedActionOccurrence
    (OInsert generatedChild (ChildOf selected) generatedComponent) trace
  0 generatedStamp : generation = MkRegistrationGeneration generatedChild
    (startOrdinal + locatedActionOrdinal generatedBirth)
  generatedRetiresLater : ActionOccurs (ORetire generatedChild)
    (afterActionOccurrence generatedBirth)

public export
RegisteredGenerationsDuring :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (selected : name) -> (startOrdinal : Nat) ->
  (registered : List (RegistrationGeneration name)) ->
  (trace : Transitions first finalState) -> Type
RegisteredGenerationsDuring {name} {key} {value} {world} {error}
  selected startOrdinal registered trace =
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    GeneratedDuring name key world error value selected startOrdinal trace
      generation,
   (child : name) -> (component : Component key value world error) ->
    (birth : LocatedActionOccurrence
      (OInsert child (ChildOf selected) component) trace) ->
    Elem (MkRegistrationGeneration child
      (startOrdinal + locatedActionOrdinal birth)) registered)

||| The set R of explicit child insertions during the selected closed episode,
||| together with the visible counterpart of Definition 47: each insertion's
||| O-Retire occurs later in that same episode before the parent's leave.
public export
RawRegisteredNamesDuring :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (selected : name) -> (registered : List name) ->
  Transitions first finalState -> Type
RawRegisteredNamesDuring {name} {key} {value} {world} {error}
  selected registered trace =
  ((child : name) -> Elem child registered ->
    (component : Component key value world error **
      (ActionOccurs (OInsert child (ChildOf selected) component) trace,
       ActionBefore (OInsert child (ChildOf selected) component)
         (ORetire child) trace)),
   (child : name) -> (component : Component key value world error) ->
    ActionOccurs (OInsert child (ChildOf selected) component) trace ->
    Elem child registered)

public export
NoRawRegisteredEpisode :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, finalState : SystemState name key value world error} ->
  (registered : List name) ->
  (global : Transitions initial finalState) -> Type
NoRawRegisteredEpisode {name} registered global =
  (child : name) -> Elem child registered ->
  ActionOccurs (LBegin child) global -> Void

public export
NoDependentClosingEpisode :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, finalState : SystemState name key value world error} ->
  (selected : name) -> (global : Transitions initial finalState) -> Type
NoDependentClosingEpisode {name} {key} {world} {error} {value} {nameEq} {keyEq}
  selected global =
    (consumer : name) ->
    (consumerEpisode : LocatedClosedEpisode name key world error value nameEq
      keyEq consumer global) ->
    PrecedenceEdge nameEq selected consumer
      (closedStartState (locatedEpisode consumerEpisode)) -> Void

public export
CurrentGenerationOutside : {name : Type} -> {nameEq : DecEq name} ->
  List (RegistrationGeneration name) -> GenerationEnvironment name -> name -> Type
CurrentGenerationOutside {name} registered live selected =
  (generation : RegistrationGeneration name) ->
  lookupCurrentGeneration selected live = Just generation ->
  Elem generation registered -> Void

||| Equation-53 control agreement exempts only a targeted generation that is
||| still current. A later generation reusing the same raw name remains exact.
public export
ControlEquivalentOutsideGenerations :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> List (RegistrationGeneration name) ->
  GenerationEnvironment name -> SystemState name key value world error ->
  SystemState name key value world error -> Type
ControlEquivalentOutsideGenerations {name} nameEq registered live originalFinal
  survivingFinal = (selected : name) ->
    CurrentGenerationOutside {nameEq = nameEq} registered live selected ->
    FiberControlMaybeRelated
      (lookupFiber @{nameEq} selected (registry originalFinal))
      (lookupFiber @{nameEq} selected (registry survivingFinal))

||| Endpoint disposition of one deleted generation. If it remains current it is
||| the Lemma-57 vestigial removed from the replay; if O-Remove closed it, any
||| later raw-name generation is governed by outside-generation control equality.
public export
data WithdrawnGenerationResult :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (live : GenerationEnvironment name) ->
  (generation : RegistrationGeneration name) ->
  (originalFinal, survivingFinal : SystemState name key value world error) -> Type
  where
  CurrentGenerationWithdrawn :
    (fiber : Fiber name key value world error) ->
    lookupCurrentGeneration @{nameEq} (generationName generation) live =
      Just generation ->
    lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} (generationName generation)
      (registry originalFinal) = Just fiber ->
    retired fiber = True ->
    installed (fiberLifecycle fiber) = False ->
    bindings (ownedValues (fiberTable fiber)) = [] ->
    lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} (generationName generation)
      (registry survivingFinal) = Nothing ->
    WithdrawnGenerationResult {name = name} {key = key} {value = value}
      {world = world} {error = error} nameEq live generation originalFinal
      survivingFinal
  HistoricalGenerationClosed :
    (lookupCurrentGeneration @{nameEq} (generationName generation) live =
      Just generation -> Void) ->
    WithdrawnGenerationResult {name = name} {key = key} {value = value}
      {world = world} {error = error} nameEq live generation originalFinal
      survivingFinal

||| Generation-aware replacement of the old raw-name withdrawal family.
public export
RegisteredNamesWithdrawn :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  SystemState name key value world error ->
  SystemState name key value world error -> Type
RegisteredNamesWithdrawn {name} {key} {world} {error} {value}
  nameEq registered live originalFinal survivingFinal =
  (generation : RegistrationGeneration name) -> Elem generation registered ->
  WithdrawnGenerationResult {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq live generation originalFinal
    survivingFinal

||| Candidate result shape for paper Lemma 72. Bidirectional filtering deletes
||| selected lifecycle actions and exact generated R generations while retaining
||| later raw-name reissues and selected orchestration such as O-Retire/O-Remove.
public export
record DeletionResult
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (selected : name)
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected original)
  (registered : List (RegistrationGeneration name))
  (episodeStartOrdinal : Nat)
  (episodeStartLive : GenerationEnvironment name) where
  constructor MkDeletionResult
  selectedOutsideRegistered : (generation : RegistrationGeneration name) ->
    Elem generation registered -> Not (generationName generation = selected)
  survivingBeforeEnd : SystemState name key value world error
  survivingEpisodeEnd : SystemState name key value world error
  survivingFinal : SystemState name key value world error
  survivingBefore : Transitions initial survivingBeforeEnd
  survivingEpisode : Transitions survivingBeforeEnd survivingEpisodeEnd
  survivingAfter : Transitions survivingEpisodeEnd survivingFinal
  beforeGenerationScan : GenerationTraceScan nameEq 0 []
    (traceBeforeOpening episode) episodeStartOrdinal episodeStartLive
  episodeEndOrdinal : Nat
  episodeEndLive : GenerationEnvironment name
  episodeGenerationScan : GenerationTraceScan nameEq episodeStartOrdinal
    episodeStartLive
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode)))
    episodeEndOrdinal episodeEndLive
  originalFinalOrdinal : Nat
  originalFinalLive : GenerationEnvironment name
  afterGenerationScan : GenerationTraceScan nameEq episodeEndOrdinal
    episodeEndLive (traceAfterClosing episode) originalFinalOrdinal
    originalFinalLive
  beforeDeletion : GenerationActionSubsequence nameEq
    (GenerationOwnedActor nameEq registered) 0 []
    (traceBeforeOpening episode) survivingBefore
  episodeDeletion : GenerationActionSubsequence nameEq
    (EpisodeGenerationDeletedActor nameEq selected registered)
    episodeStartOrdinal episodeStartLive
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode))) survivingEpisode
  afterDeletion : GenerationActionSubsequence nameEq
    (GenerationOwnedActor nameEq registered) episodeEndOrdinal episodeEndLive
    (traceAfterClosing episode) survivingAfter
  effectsPreserved : EffectStateRelated keyEq
    (projectEffectState @{nameEq} originalFinal)
    (projectEffectState @{nameEq} survivingFinal)
  controlsPreservedOutside : ControlEquivalentOutsideGenerations nameEq registered
    originalFinalLive originalFinal survivingFinal
  registeredWithdrawn : RegisteredNamesWithdrawn nameEq registered
    originalFinalLive originalFinal survivingFinal

public export
survivingTrace :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} -> {selected : name} ->
  {episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected original} -> {registered : List (RegistrationGeneration name)} ->
  {episodeStartOrdinal : Nat} ->
  {episodeStartLive : GenerationEnvironment name} ->
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered episodeStartOrdinal episodeStartLive) ->
  Transitions initial (survivingFinal result)
survivingTrace {initial} result = appendTransitions (survivingBefore result)
  (appendTransitions (survivingEpisode result) (survivingAfter result))

||| Candidate paper-Lemma-72 statement after round-3 review: lifecycle-only
||| selected deletion, all-trace totality, yielded/inverse provenance,
||| open-episode exclusion, relevant-episode dependency edges, effect recovery,
||| and outside-R control agreement are explicit. It remains unproved.
||| TODO(proof): one-episode checked replay using Corollary 62 and Lemma 71.
public export
deletionTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
deletionTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (initial, finalState : SystemState name key value world error) ->
  (global : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  RegistrationDiscipline protocol nameEq global ->
  registryWellFormed @{nameEq} @{keyEq} initial = True ->
  bindings (registry initial) = [] ->
  quiet @{nameEq} @{keyEq} finalState = True ->
  noFailedFibers finalState = True ->
  TraceComponentsTotal nameEq keyEq global ->
  TraceIndependent name key world error value keyEq global ->
  (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  (registered : List (RegistrationGeneration name)) ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (episodeStartOrdinal : Nat) ->
  (episodeStartLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq 0 [] (traceBeforeOpening episode)
    episodeStartOrdinal episodeStartLive ->
  RegisteredGenerationsDuring selected episodeStartOrdinal registered
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode))) ->
  NoDependentClosingEpisode {nameEq = nameEq} {keyEq = keyEq}
    selected global ->
  NoRegisteredEpisode nameEq registered 0 [] global ->
  DeletionResult name key world error value nameEq keyEq global selected episode
    registered episodeStartOrdinal episodeStartLive

||| Theorem-73 result transported through the explicit Lemma-56 generation
||| bijection.  Historical registrations and current endpoint names are kept
||| separate, so one raw name may have different images at different births.
public export
record ConfluenceResult
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, leftFinal, rightFinal : SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal)
  (rightTrace : Transitions initial rightFinal)
  (generationRenaming : RegistrationGenerationBijection name)
  (currentRenaming : NameBijection name) where
  constructor MkConfluenceResult
  leftCanonical : CanonicalSchedule name key world error value protocol nameEq
    keyEq leftTrace
  rightCanonical : CanonicalSchedule name key world error value protocol nameEq
    keyEq rightTrace
  finalRegistrationCorrespondence : RegistrationCorrespondenceByGeneration nameEq
    generationRenaming leftTrace rightTrace
  finalEndpointRenaming : CurrentEndpointRenaming nameEq keyEq generationRenaming
    leftTrace rightTrace finalRegistrationCorrespondence
  finalEndpointsEquivalent : SystemEquivalentByRenamingModuloVestigial
    name key world error value nameEq keyEq finalRegistrationCorrespondence
    currentRenaming

||| Candidate finite explicit-registration statement for paper Theorem 73.
||| Yield tags/catalogs provide Definition-47 provenance, and paper Lemma 56 is
||| represented by `SameOrchestrationModuloGenerated` and `ConfluenceResult`.
||| It remains under adversarial statement review.
||| TODO(proof): Lemma-71 applicability frames, Lemma-72 deletion induction,
||| support well-foundedness, and canonical episode sorting.
public export
confluenceTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
confluenceTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (initial, leftFinal, rightFinal : SystemState name key value world error) ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  AlignedTransitions name key world error value nameEq keyEq leftTrace ->
  AlignedTransitions name key world error value nameEq keyEq rightTrace ->
  RegistrationDiscipline protocol nameEq leftTrace ->
  RegistrationDiscipline protocol nameEq rightTrace ->
  registryWellFormed @{nameEq} @{keyEq} initial = True ->
  bindings (registry initial) = [] ->
  quiet @{nameEq} @{keyEq} leftFinal = True ->
  quiet @{nameEq} @{keyEq} rightFinal = True ->
  noFailedFibers leftFinal = True ->
  noFailedFibers rightFinal = True ->
  TraceComponentsTotal nameEq keyEq leftTrace ->
  TraceComponentsTotal nameEq keyEq rightTrace ->
  TraceIndependent name key world error value keyEq leftTrace ->
  TraceIndependent name key world error value keyEq rightTrace ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace) ->
  ConfluenceResult name key world error value protocol nameEq keyEq leftTrace
    rightTrace (generatedGenerationBijection sameInputs)
    (currentNameBijection (endpointRenaming sameInputs))

||| Reflexivity sanity check for the orchestration projection: arbitrary
||| lifecycle noise is ignored, while each orchestration action matches itself.
public export
0 sameOrchestrationReflexive :
  (trace : Transitions first finalState) -> SameOrchestration trace trace
sameOrchestrationReflexive NoTransitions = SameOrchestrationEnd
sameOrchestrationReflexive
  (MoreTransitions transition@(Fired nameEq keyEq (OInsert n parent component)
    tag equation) rest) =
  MatchOrchestration (OInsert n parent component) transition rest transition rest
    Refl Refl Refl (sameOrchestrationReflexive rest)
sameOrchestrationReflexive
  (MoreTransitions transition@(Fired nameEq keyEq (ORetire n) tag equation) rest) =
  MatchOrchestration (ORetire n) transition rest transition rest
    Refl Refl Refl (sameOrchestrationReflexive rest)
sameOrchestrationReflexive
  (MoreTransitions transition@(Fired nameEq keyEq (ORemove n) tag equation) rest) =
  MatchOrchestration (ORemove n) transition rest transition rest
    Refl Refl Refl (sameOrchestrationReflexive rest)
sameOrchestrationReflexive
  (MoreTransitions transition@(Fired nameEq keyEq (LBegin n) tag equation) rest) =
  SkipLeftLifecycle transition rest Refl
    (SkipRightLifecycle transition rest Refl (sameOrchestrationReflexive rest))
sameOrchestrationReflexive
  (MoreTransitions transition@(Fired nameEq keyEq (LAdvance n) tag equation) rest) =
  SkipLeftLifecycle transition rest Refl
    (SkipRightLifecycle transition rest Refl (sameOrchestrationReflexive rest))
sameOrchestrationReflexive
  (MoreTransitions transition@(Fired nameEq keyEq (LDivert n) tag equation) rest) =
  SkipLeftLifecycle transition rest Refl
    (SkipRightLifecycle transition rest Refl (sameOrchestrationReflexive rest))
sameOrchestrationReflexive
  (MoreTransitions transition@(Fired nameEq keyEq (LLeave n) tag equation) rest) =
  SkipLeftLifecycle transition rest Refl
    (SkipRightLifecycle transition rest Refl (sameOrchestrationReflexive rest))
sameOrchestrationReflexive
  (MoreTransitions transition@(Fired nameEq keyEq (LUnload n) tag equation) rest) =
  SkipLeftLifecycle transition rest Refl
    (SkipRightLifecycle transition rest Refl (sameOrchestrationReflexive rest))

public export
0 systemEquivalentReflexive :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  SystemEquivalent name key world error value nameEq keyEq state state
systemEquivalentReflexive nameEq keyEq state = MkSystemEquivalent
  (MkEffectStateRelated Refl (\selected => Refl))
  (MkControlEquivalent
    (\n => fiberControlMaybeReflexive (lookupFiber @{nameEq} n (registry state))))

||| Four possible installed-bit evolutions for one checked transition. The only
||| changing cases are the two episode boundaries.
public export
data InstallationEvolution :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) -> Type where
  RemainedUninstalled :
    installedAt @{nameEq} selected before = False ->
    installedAt @{nameEq} selected afterState = False ->
    InstallationEvolution name key world error value nameEq keyEq selected
      before afterState action tag
  RemainedInstalled :
    installedAt @{nameEq} selected before = True ->
    installedAt @{nameEq} selected afterState = True ->
    InstallationEvolution name key world error value nameEq keyEq selected
      before afterState action tag
  OpenedInstallation :
    InstallationEvolution name key world error value nameEq keyEq selected
      before afterState (LBegin selected) LBeginTag
  ClosedInstallation :
    InstallationEvolution name key world error value nameEq keyEq selected
      before afterState (LUnload selected) LUnloadTag

installedMaybe : {name, key, world, error : Type} -> {value : key -> Type} ->
  Maybe (Fiber name key value world error) -> Bool
installedMaybe Nothing = False
installedMaybe (Just fiber) = installed (fiberLifecycle fiber)

0 installedAtLookupEquation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  installedAt @{nameEq} selected state =
    installedMaybe {name = name} {key = key} {world = world}
      {error = error} {value = value}
      (lookupFiber @{nameEq} selected (registry state))
installedAtLookupEquation nameEq selected
  state@(MkSystemState ambient fibers)
  with (lookupFiber @{nameEq} selected fibers)
  installedAtLookupEquation nameEq selected
    state@(MkSystemState ambient fibers) | Nothing = Refl
  installedAtLookupEquation nameEq selected
    state@(MkSystemState ambient fibers) | Just fiber = Refl

||| Any successful action on another name preserves the selected installed bit.
public export
0 foreignInstalledStable :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (action : Action name key value world error) ->
  Not (selected = actionOwner action) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  installedAt @{nameEq} selected before =
    installedAt @{nameEq} selected afterState
foreignInstalledStable {name} {key} {world} {error} {value}
  nameEq keyEq selected action distinct before afterState tag equation =
  let update = applyActionLocalUpdate nameEq keyEq action before afterState tag
        equation
      lookupTargetSource = systemLocalUpdateForeign nameEq selected
        (actionOwner action) distinct before afterState update
      maybeTargetSource = cong
        (\found => installedMaybe {name = name} {key = key} {world = world}
          {error = error} {value = value} found)
        lookupTargetSource
      sourceObserved = installedAtLookupEquation nameEq selected before
      targetObserved = installedAtLookupEquation nameEq selected afterState
  in trans sourceObserved (trans (sym maybeTargetSource) (sym targetObserved))

public export
0 foreignInstallationEvolution :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (action : Action name key value world error) ->
  Not (selected = actionOwner action) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  InstallationEvolution name key world error value nameEq keyEq selected
    before afterState action tag
foreignInstallationEvolution nameEq keyEq selected action distinct before
  afterState tag equation =
  let stable = foreignInstalledStable nameEq keyEq selected action distinct
        before afterState tag equation in
  case boolEquality (installedAt @{nameEq} selected before) of
    Left sourceFalse =>
      RemainedUninstalled sourceFalse (trans (sym stable) sourceFalse)
    Right sourceTrue =>
      RemainedInstalled sourceTrue (trans (sym stable) sourceTrue)
  where
  boolEquality : (observed : Bool) ->
    Either (observed = False) (observed = True)
  boolEquality False = Left Refl
  boolEquality True = Right Refl

public export
0 installedAtFound :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry state) = Just fiber ->
  installedAt @{nameEq} selected state = installed (fiberLifecycle fiber)
installedAtFound {name} {key} {world} {error} {value}
  nameEq selected state fiber found =
  trans (installedAtLookupEquation nameEq selected state)
    (cong (installedMaybe {name = name} {key = key} {world = world}
      {error = error} {value = value}) found)

public export
0 installedAtMissing :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  (observed : Maybe (Fiber name key value world error)) ->
  lookupFiber @{nameEq} selected (registry state) = observed ->
  observed = Nothing ->
  installedAt @{nameEq} selected state = False
installedAtMissing {name} {key} {world} {error} {value}
  nameEq selected state observed found missing =
  trans (installedAtLookupEquation nameEq selected state)
    (trans (cong (installedMaybe {name = name} {key = key} {world = world}
      {error = error} {value = value}) found)
      (cong (installedMaybe {name = name} {key = key} {world = world}
        {error = error} {value = value}) missing))

0 activeImpliesInstalled :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  activeAt @{nameEq} selected state = True ->
  installedAt @{nameEq} selected state = True
activeImpliesInstalled nameEq selected state evidence
  with (lookupFiber @{nameEq} selected (registry state)) proof found
  activeImpliesInstalled nameEq selected state evidence | Nothing = absurd evidence
  activeImpliesInstalled nameEq selected state evidence | Just fiber
    with (fiberLifecycle fiber) proof life
    activeImpliesInstalled nameEq selected state evidence | Just fiber |
      Inactive outcome = absurd evidence
    activeImpliesInstalled nameEq selected state evidence | Just fiber |
      Reloading remaining accumulator view = absurd evidence
    activeImpliesInstalled nameEq selected state evidence | Just fiber |
      Active accumulator view =
        Refl
    activeImpliesInstalled nameEq selected state evidence | Just fiber |
      Unloading accumulator view outcome = absurd evidence

0 reloadingImpliesInstalled :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  reloadingAt @{nameEq} selected state = True ->
  installedAt @{nameEq} selected state = True
reloadingImpliesInstalled nameEq selected state evidence
  with (lookupFiber @{nameEq} selected (registry state)) proof found
  reloadingImpliesInstalled nameEq selected state evidence | Nothing = absurd evidence
  reloadingImpliesInstalled nameEq selected state evidence | Just fiber
    with (fiberLifecycle fiber) proof life
    reloadingImpliesInstalled nameEq selected state evidence | Just fiber |
      Inactive outcome = absurd evidence
    reloadingImpliesInstalled nameEq selected state evidence | Just fiber |
      Reloading remaining accumulator view =
        Refl
    reloadingImpliesInstalled nameEq selected state evidence | Just fiber |
      Active accumulator view = absurd evidence
    reloadingImpliesInstalled nameEq selected state evidence | Just fiber |
      Unloading accumulator view outcome = absurd evidence

0 unloadingImpliesInstalled :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  unloadingAt @{nameEq} selected state = True ->
  installedAt @{nameEq} selected state = True
unloadingImpliesInstalled nameEq selected state evidence
  with (lookupFiber @{nameEq} selected (registry state)) proof found
  unloadingImpliesInstalled nameEq selected state evidence | Nothing = absurd evidence
  unloadingImpliesInstalled nameEq selected state evidence | Just fiber
    with (fiberLifecycle fiber) proof life
    unloadingImpliesInstalled nameEq selected state evidence | Just fiber |
      Inactive outcome = absurd evidence
    unloadingImpliesInstalled nameEq selected state evidence | Just fiber |
      Reloading remaining accumulator view = absurd evidence
    unloadingImpliesInstalled nameEq selected state evidence | Just fiber |
      Active accumulator view = absurd evidence
    unloadingImpliesInstalled nameEq selected state evidence | Just fiber |
      Unloading accumulator view outcome =
        Refl

public export
0 installedAtDecEqCoherent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (leftEq, rightEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  installedAt @{leftEq} selected state = installedAt @{rightEq} selected state
installedAtDecEqCoherent {name} {key} {world} {error} {value}
  leftEq rightEq selected state =
  let lookupCoherent = lookupFiberDecEqCoherent leftEq rightEq selected
        (registry state)
      observedCoherent = cong
        (installedMaybe {name = name} {key = key} {world = world}
          {error = error} {value = value}) lookupCoherent
  in trans (installedAtLookupEquation leftEq selected state)
    (trans observedCoherent
      (sym (installedAtLookupEquation rightEq selected state)))

0 reloadingAnyImpliesInstalled :
  {leftEq : DecEq name} -> (rightEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  reloadingAt @{leftEq} selected state = True ->
  installedAt @{rightEq} selected state = True
reloadingAnyImpliesInstalled {leftEq} rightEq selected state evidence =
  trans (sym (installedAtDecEqCoherent leftEq rightEq selected state))
    (reloadingImpliesInstalled leftEq selected state evidence)

0 activeAnyImpliesInstalled :
  {leftEq : DecEq name} -> (rightEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  activeAt @{leftEq} selected state = True ->
  installedAt @{rightEq} selected state = True
activeAnyImpliesInstalled {leftEq} rightEq selected state evidence =
  trans (sym (installedAtDecEqCoherent leftEq rightEq selected state))
    (activeImpliesInstalled leftEq selected state evidence)

0 unloadingAnyImpliesInstalled :
  {leftEq : DecEq name} -> (rightEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  unloadingAt @{leftEq} selected state = True ->
  installedAt @{rightEq} selected state = True
unloadingAnyImpliesInstalled {leftEq} rightEq selected state evidence =
  trans (sym (installedAtDecEqCoherent leftEq rightEq selected state))
    (unloadingImpliesInstalled leftEq selected state evidence)


0 reloadingEndpointImpliesInstalled :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  reloadingEndpoint @{nameEq} selected state = True ->
  installedAt @{nameEq} selected state = True
reloadingEndpointImpliesInstalled nameEq selected state evidence
  with (lookupFiber @{nameEq} selected (registry state))
  reloadingEndpointImpliesInstalled nameEq selected state evidence | Nothing =
    absurd evidence
  reloadingEndpointImpliesInstalled nameEq selected state evidence | Just fiber
    with (fiberLifecycle fiber)
    reloadingEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Inactive outcome = absurd evidence
    reloadingEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Reloading remaining accumulator view = Refl
    reloadingEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Active accumulator view = absurd evidence
    reloadingEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Unloading accumulator view outcome = absurd evidence

0 activeEndpointImpliesInstalled :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  activeEndpoint @{nameEq} selected state = True ->
  installedAt @{nameEq} selected state = True
activeEndpointImpliesInstalled nameEq selected state evidence
  with (lookupFiber @{nameEq} selected (registry state))
  activeEndpointImpliesInstalled nameEq selected state evidence | Nothing =
    absurd evidence
  activeEndpointImpliesInstalled nameEq selected state evidence | Just fiber
    with (fiberLifecycle fiber)
    activeEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Inactive outcome = absurd evidence
    activeEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Reloading remaining accumulator view = absurd evidence
    activeEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Active accumulator view = Refl
    activeEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Unloading accumulator view outcome = absurd evidence

0 unloadingEndpointImpliesInstalled :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  unloadingEndpoint @{nameEq} selected state = True ->
  installedAt @{nameEq} selected state = True
unloadingEndpointImpliesInstalled nameEq selected state evidence
  with (lookupFiber @{nameEq} selected (registry state))
  unloadingEndpointImpliesInstalled nameEq selected state evidence | Nothing =
    absurd evidence
  unloadingEndpointImpliesInstalled nameEq selected state evidence | Just fiber
    with (fiberLifecycle fiber)
    unloadingEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Inactive outcome = absurd evidence
    unloadingEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Reloading remaining accumulator view = absurd evidence
    unloadingEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Active accumulator view = absurd evidence
    unloadingEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Unloading accumulator view outcome = Refl

public export
0 lAdvanceStartsInstalled :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LAdvance selected) before =
    Just (tag, afterState) ->
  installedAt @{nameEq} selected before = True
lAdvanceStartsInstalled nameEq keyEq selected before afterState tag equation
  with (lookupFiber @{nameEq} selected (registry before))
  lAdvanceStartsInstalled nameEq keyEq selected before afterState tag equation |
    Nothing = void (nothingIsNotJust equation)
  lAdvanceStartsInstalled nameEq keyEq selected before afterState tag equation |
    Just fiber with (fiberLifecycle fiber)
    lAdvanceStartsInstalled nameEq keyEq selected before afterState tag equation |
      Just fiber | Inactive outcome = void (nothingIsNotJust equation)
    lAdvanceStartsInstalled nameEq keyEq selected before afterState tag equation |
      Just fiber | Reloading remaining accumulator view = Refl
    lAdvanceStartsInstalled nameEq keyEq selected before afterState tag equation |
      Just fiber | Active accumulator view = void (nothingIsNotJust equation)
    lAdvanceStartsInstalled nameEq keyEq selected before afterState tag equation |
      Just fiber | Unloading accumulator view outcome =
        void (nothingIsNotJust equation)

0 lAdvanceEndsInstalled :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LAdvance selected) before =
    Just (tag, afterState) ->
  installedAt @{nameEq} selected afterState = True
lAdvanceEndsInstalled {name} {key} {world} {error} {value}
  nameEq keyEq selected before afterState tag equation =
  case advanceStructureTheorem nameEq keyEq selected before afterState tag
    equation of
    IterAdvance fiber found package reloading =>
      reloadingEndpointImpliesInstalled nameEq selected afterState reloading
    FinishAdvance fiber found package active =>
      activeEndpointImpliesInstalled nameEq selected afterState active
    DivertAdvance unloading =>
      unloadingEndpointImpliesInstalled nameEq selected afterState unloading
    RaiseAdvance unloading =>
      unloadingEndpointImpliesInstalled nameEq selected afterState unloading

public export
0 lDivertInstalled :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (LDivert selected) before =
    Just (LDivertTag, afterState) ->
  (installedAt @{nameEq} selected before = True,
   installedAt @{nameEq} selected afterState = True)
lDivertInstalled {name} {key} {world} {error} {value}
  nameEq keyEq selected before afterState equation =
  case abortDivertStructureTheorem nameEq keyEq selected before afterState
    equation of
    MkAbortDivertStructure fiber found remaining accumulator view reloading
      changed unloading =>
        (trans (installedAtFound nameEq selected before fiber found)
          (cong installed reloading),
         unloadingEndpointImpliesInstalled nameEq selected afterState unloading)

0 installedAtAfterReplace :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (sourceFiber, targetFiberValue : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  (ambient : world) ->
  (found : lookupFiber @{nameEq} selected fibers = Just sourceFiber) ->
  installedAt @{nameEq} selected
    (the (SystemState name key value world error)
      (MkSystemState ambient
        (replaceBinding @{nameEq} selected targetFiberValue fibers))) =
    installed (fiberLifecycle targetFiberValue)
installedAtAfterReplace {name} {key} {world} {error} {value}
  nameEq selected sourceFiber targetFiberValue fibers ambient found =
  trans (installedAtLookupEquation nameEq selected
    (MkSystemState ambient
      (replaceBinding @{nameEq} selected targetFiberValue fibers)))
    (cong (installedMaybe {name = name} {key = key} {world = world}
      {error = error} {value = value})
      (lookupReplacedFiber selected sourceFiber targetFiberValue fibers found))

0 installedSetFiberLifecycle :
  (fiber : Fiber name key value world error) ->
  (next : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  installed (fiberLifecycle (setFiberLifecycle fiber next)) = installed next
installedSetFiberLifecycle (MkFiber component parent retired table lifecycle) next =
  Refl

0 installedSetFiberRuntime :
  (fiber : Fiber name key value world error) ->
  (table : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (next : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  installed (fiberLifecycle (setFiberRuntime fiber table next)) = installed next
installedSetFiberRuntime (MkFiber component parent retired oldTable lifecycle)
  table next = Refl

public export
0 lLeaveInstalled :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LLeave selected) before =
    Just (tag, afterState) ->
  (installedAt @{nameEq} selected before = True,
   installedAt @{nameEq} selected afterState = True)
lLeaveInstalled nameEq keyEq selected
  before@(MkSystemState ambient fibers) afterState tag equation
  with (lookupFiber @{nameEq} selected fibers) proof found
  lLeaveInstalled nameEq keyEq selected
    before@(MkSystemState ambient fibers) afterState tag equation | Nothing =
      void (nothingIsNotJust equation)
  lLeaveInstalled nameEq keyEq selected
    before@(MkSystemState ambient fibers) afterState tag equation | Just fiber
    with (fiberLifecycle fiber)
    lLeaveInstalled nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Inactive outcome = void (nothingIsNotJust equation)
    lLeaveInstalled nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Reloading remaining accumulator view = void (nothingIsNotJust equation)
    lLeaveInstalled nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Unloading accumulator view outcome = void (nothingIsNotJust equation)
    lLeaveInstalled nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Active accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} fiber fibers) view)
      lLeaveInstalled nameEq keyEq selected
        before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Active accumulator view | True = void (nothingIsNotJust equation)
      lLeaveInstalled nameEq keyEq selected
        before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Active accumulator view | False =
          case justInjective equation of
            Refl => let targetObserved = installedAtAfterReplace nameEq selected
                          fiber (setFiberLifecycle fiber
                            (Unloading accumulator view Nothing))
                          fibers ambient found
                        targetInstalled = trans targetObserved
                          (trans (installedSetFiberLifecycle fiber
                            (Unloading accumulator view Nothing)) Refl)
                    in (Refl, targetInstalled)

public export
0 lUnloadBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LUnload selected) before =
    Just (tag, afterState) ->
  (tag = LUnloadTag,
   installedAt @{nameEq} selected before = True,
   installedAt @{nameEq} selected afterState = False)
lUnloadBoundary nameEq keyEq selected
  before@(MkSystemState ambient fibers) afterState tag equation
  with (lookupFiber @{nameEq} selected fibers) proof found
  lUnloadBoundary nameEq keyEq selected
    before@(MkSystemState ambient fibers) afterState tag equation | Nothing =
      void (nothingIsNotJust equation)
  lUnloadBoundary nameEq keyEq selected
    before@(MkSystemState ambient fibers) afterState tag equation | Just fiber
    with (fiberLifecycle fiber)
    lUnloadBoundary nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Inactive outcome = void (nothingIsNotJust equation)
    lUnloadBoundary nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Reloading remaining accumulator view = void (nothingIsNotJust equation)
    lUnloadBoundary nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Active accumulator view = void (nothingIsNotJust equation)
    lUnloadBoundary nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Unloading accumulator view outcome
      with (relied @{nameEq} selected fibers)
      lUnloadBoundary nameEq keyEq selected
        before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Unloading accumulator view outcome | True =
          void (nothingIsNotJust equation)
      lUnloadBoundary nameEq keyEq selected
        before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Unloading accumulator view outcome | False =
          case justInjective equation of
            Refl =>
              let restored = accumulator (MkLocalState ambient
                          (restrictOwnedPreservingOrder
                            (componentProvisions (fiberComponent fiber))
                            (ownedValues (fiberTable fiber))))
                  targetObserved = installedAtAfterReplace nameEq selected fiber
                    (setFiberRuntime fiber
                      (localTable (accumulator
                        (MkLocalState ambient
                          (restrictOwnedPreservingOrder
                            (componentProvisions (fiberComponent fiber))
                            (ownedValues (fiberTable fiber))))))
                      (Inactive outcome)) fibers
                    (localWorld (accumulator
                      (MkLocalState ambient
                          (restrictOwnedPreservingOrder
                            (componentProvisions (fiberComponent fiber))
                            (ownedValues (fiberTable fiber)))))) found
                  targetUninstalled = trans targetObserved
                    (trans (installedSetFiberRuntime fiber
                      (localTable (accumulator
                        (MkLocalState ambient
                          (restrictOwnedPreservingOrder
                            (componentProvisions (fiberComponent fiber))
                            (ownedValues (fiberTable fiber))))))
                      (Inactive outcome)) Refl)
              in (Refl, Refl, targetUninstalled)

public export
0 lBeginBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  checkedApplyAction @{nameEq} @{keyEq} (LBegin selected) before =
    Just (tag, afterState) ->
  (tag = LBeginTag,
   installedAt @{nameEq} selected before = False,
   installedAt @{nameEq} selected afterState = True)
lBeginBoundary nameEq keyEq selected before afterState tag checkedEquation =
  let rawEquation = checkedActionProjects nameEq keyEq (LBegin selected)
        before afterState tag checkedEquation in
  lBeginRaw rawEquation
  where
  lBeginRaw : applyAction @{nameEq} @{keyEq} (LBegin selected) before =
      Just (tag, afterState) ->
    (tag = LBeginTag,
     installedAt @{nameEq} selected before = False,
     installedAt @{nameEq} selected afterState = True)
  lBeginRaw rawEquation
    with (lookupFiber @{nameEq} selected (registry before)) proof found
    lBeginRaw rawEquation | Nothing = void (nothingIsNotJust rawEquation)
    lBeginRaw rawEquation | Just fiber with (fiberLifecycle fiber)
      lBeginRaw rawEquation | Just fiber | Inactive Nothing
        with (targetFiber @{nameEq} @{keyEq} fiber (registry before))
        lBeginRaw rawEquation | Just fiber | Inactive Nothing | Nothing =
          void (nothingIsNotJust rawEquation)
        lBeginRaw rawEquation | Just fiber | Inactive Nothing | Just view =
          case justInjective rawEquation of
            Refl =>
              let targetObserved = installedAtAfterReplace nameEq selected fiber
                    (setFiberLifecycle fiber
                      (Reloading (componentProgram (fiberComponent fiber)) id view))
                    (registry before) (worldState before) found
                  targetInstalled = trans targetObserved
                    (trans (installedSetFiberLifecycle fiber
                      (Reloading (componentProgram (fiberComponent fiber)) id view))
                      Refl)
              in (Refl, Refl, targetInstalled)
      lBeginRaw rawEquation | Just fiber | Inactive (Just err) =
        void (nothingIsNotJust rawEquation)
      lBeginRaw rawEquation | Just fiber |
        Reloading remaining accumulator view = void (nothingIsNotJust rawEquation)
      lBeginRaw rawEquation | Just fiber | Active accumulator view =
        void (nothingIsNotJust rawEquation)
      lBeginRaw rawEquation | Just fiber |
        Unloading accumulator view outcome = void (nothingIsNotJust rawEquation)

0 installedRetireFiber : (fiber : Fiber name key value world error) ->
  installed (fiberLifecycle (retireFiber fiber)) = installed (fiberLifecycle fiber)
installedRetireFiber (MkFiber component parent retired table lifecycle) = Refl

0 oRetireStable :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (ORetire selected) before =
    Just (tag, afterState) ->
  installedAt @{nameEq} selected before =
    installedAt @{nameEq} selected afterState
oRetireStable nameEq keyEq selected
  before@(MkSystemState ambient fibers) afterState tag equation
  with (lookupFiber @{nameEq} selected fibers) proof found
  oRetireStable nameEq keyEq selected before@(MkSystemState ambient fibers)
    afterState tag equation | Nothing = void (nothingIsNotJust equation)
  oRetireStable nameEq keyEq selected before@(MkSystemState ambient fibers)
    afterState tag equation | Just fiber =
      case justInjective equation of
        Refl =>
          let sourceObserved = installedAtFound nameEq selected
                (MkSystemState ambient fibers) fiber found
              targetObserved = installedAtAfterReplace nameEq selected fiber
                (retireFiber fiber) fibers ambient found
          in sym (trans targetObserved (installedRetireFiber fiber))

0 lookupNotElemNothing : DecEq key => (wanted : key) ->
  (entries : List (Binding key value)) ->
  Not (Elem wanted (bindingKeys entries)) ->
  lookupEntries wanted entries = Nothing
lookupNotElemNothing wanted [] absent = Refl
lookupNotElemNothing wanted (Bind current observed :: rest) absent
  with (decEq wanted current)
  lookupNotElemNothing current (Bind current observed :: rest) absent |
    Yes Refl = void (absent Here)
  lookupNotElemNothing wanted (Bind current observed :: rest) absent |
    No distinct = lookupNotElemNothing wanted rest (\later => absent (There later))

0 lookupDeleteSelf : DecEq key => (removed : key) ->
  (table : CoeffectContext key value) ->
  lookupBinding removed (deleteBinding removed table) = Nothing
lookupDeleteSelf removed (MkCoeffectContext entries unique) =
  lookupNotElemNothing removed (deleteEntries removed entries)
    (deletedKeyNotElem removed entries unique)

0 installedAtAfterDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (fibers : Registry name key value world error) -> (ambient : world) ->
  installedAt @{nameEq} selected
    (the (SystemState name key value world error)
      (MkSystemState ambient (deleteBinding selected fibers))) = False
installedAtAfterDelete {name} {key} {world} {error} {value}
  nameEq selected fibers ambient =
  trans (installedAtLookupEquation nameEq selected
    (MkSystemState ambient (deleteBinding selected fibers)))
    (cong (installedMaybe {name = name} {key = key} {world = world}
      {error = error} {value = value}) (lookupDeleteSelf selected fibers))

0 oRemoveUninstalled :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (ORemove selected) before =
    Just (tag, afterState) ->
  (installedAt @{nameEq} selected before = False,
   installedAt @{nameEq} selected afterState = False)
oRemoveUninstalled nameEq keyEq selected
  before@(MkSystemState ambient fibers) afterState tag equation
  with (lookupFiber @{nameEq} selected fibers) proof found
  oRemoveUninstalled nameEq keyEq selected before@(MkSystemState ambient fibers)
    afterState tag equation | Nothing = void (nothingIsNotJust equation)
  oRemoveUninstalled nameEq keyEq selected before@(MkSystemState ambient fibers)
    afterState tag equation | Just fiber
    with (retired fiber && isInactive (fiberLifecycle fiber) &&
      not (hasChild @{nameEq} selected fibers)) proof guards
    oRemoveUninstalled nameEq keyEq selected before@(MkSystemState ambient fibers)
      afterState tag equation | Just fiber | False =
        void (nothingIsNotJust equation)
    oRemoveUninstalled nameEq keyEq selected before@(MkSystemState ambient fibers)
      afterState tag equation | Just fiber | True =
        let tailValid = boolAndRight (retired fiber)
              (isInactive (fiberLifecycle fiber) &&
                not (hasChild @{nameEq} selected fibers)) guards
            inactiveValid = boolAndLeft (isInactive (fiberLifecycle fiber))
              (not (hasChild @{nameEq} selected fibers)) tailValid
        in case inactiveLifecycleWitness (fiberLifecycle fiber) inactiveValid of
          (outcome ** lifecycleIsInactive) =>
            case justInjective equation of
              Refl =>
                let sourceUninstalled =
                      trans (cong installed lifecycleIsInactive) Refl
                in (sourceUninstalled,
                  installedAtAfterDelete nameEq selected fibers ambient)

0 lookupInsertedImplicit : DecEq key => (selected : key) ->
  (next : value selected) -> (before : CoeffectContext key value) ->
  {0 absent : lookupBinding selected before = Nothing} ->
  lookupBinding selected (insertBinding selected next before absent) = Just next
lookupInsertedImplicit selected next (MkCoeffectContext entries unique) {absent}
  with (decEq selected selected)
  lookupInsertedImplicit selected next (MkCoeffectContext entries unique)
    {absent} | Yes Refl = Refl
  lookupInsertedImplicit selected next (MkCoeffectContext entries unique)
    {absent} | No contra = void (contra Refl)

0 setFreshSelectedLookup : DecEq key => (selected : key) ->
  (next : value selected) -> (before : CoeffectContext key value) ->
  (applied : CoeffectApplied before) ->
  setFresh selected next before = Just applied ->
  lookupBinding selected (coeffectAfter applied) = Just next
setFreshSelectedLookup selected next before applied success
  with (lookupBinding selected before) proof found
  setFreshSelectedLookup selected next before applied success | Just current =
    void (nothingIsNotJust success)
  setFreshSelectedLookup selected next before applied success | Nothing =
    case justInjective success of
      Refl => lookupInsertedImplicit selected next before

0 oInsertUninstalled :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (OInsert selected parent component) before =
    Just (tag, afterState) ->
  (installedAt @{nameEq} selected before = False,
   installedAt @{nameEq} selected afterState = False)
oInsertUninstalled {name} {key} {world} {error} {value}
  nameEq keyEq selected parent component
  before@(MkSystemState ambient fibers) afterState tag equation
  with (parentPresent @{nameEq} parent fibers &&
    provisionsDisjointFrom @{keyEq} (componentProvisions component)
      (registryFibers fibers))
  oInsertUninstalled {name} {key} {world} {error} {value}
    nameEq keyEq selected parent component before@(MkSystemState ambient fibers)
    afterState tag equation | False = void (nothingIsNotJust equation)
  oInsertUninstalled {name} {key} {world} {error} {value}
    nameEq keyEq selected parent component before@(MkSystemState ambient fibers)
    afterState tag equation | True
    with (setFresh @{nameEq} selected (freshFiber component parent) fibers) proof inserted
    oInsertUninstalled {name} {key} {world} {error} {value}
      nameEq keyEq selected parent component before@(MkSystemState ambient fibers)
      afterState tag equation | True | Nothing = void (nothingIsNotJust equation)
    oInsertUninstalled {name} {key} {world} {error} {value}
      nameEq keyEq selected parent component before@(MkSystemState ambient fibers)
      afterState tag equation | True | Just applied =
        case justInjective equation of
          Refl =>
            let absent = setFreshAbsent nameEq selected
                  (freshFiber component parent) fibers applied inserted
                sourceUninstalled = installedAtMissing nameEq selected
                  (MkSystemState ambient fibers)
                  (lookupFiber @{nameEq} selected fibers) Refl absent
                insertedLookup = setFreshSelectedLookup selected
                  (freshFiber component parent) fibers applied inserted
                targetObserved = installedAtLookupEquation nameEq selected
                  (MkSystemState ambient (coeffectAfter applied))
                targetUninstalled = trans targetObserved
                  (cong (installedMaybe {name = name} {key = key} {world = world}
                    {error = error} {value = value}) insertedLookup)
            in (sourceUninstalled, targetUninstalled)

||| Exact target lookup for a successful raw O-Insert.  This is the control
||| fact needed to classify a following O-Retire/O-Remove as internal to a
||| generated child rather than as external root orchestration.
public export
0 oInsertResultLookup :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (OInsert selected parent component) before =
    Just (tag, afterState) ->
  lookupFiber @{nameEq} selected (registry afterState) =
    Just (freshFiber component parent)
oInsertResultLookup {name} {key} {world} {error} {value}
  nameEq keyEq selected parent component
  before@(MkSystemState ambient fibers) afterState tag equation
  with (parentPresent @{nameEq} parent fibers &&
    provisionsDisjointFrom @{keyEq} (componentProvisions component)
      (registryFibers fibers))
  oInsertResultLookup {name} {key} {world} {error} {value}
    nameEq keyEq selected parent component before@(MkSystemState ambient fibers)
    afterState tag equation | False = void (nothingIsNotJust equation)
  oInsertResultLookup {name} {key} {world} {error} {value}
    nameEq keyEq selected parent component before@(MkSystemState ambient fibers)
    afterState tag equation | True
    with (setFresh @{nameEq} selected (freshFiber component parent) fibers) proof inserted
    oInsertResultLookup {name} {key} {world} {error} {value}
      nameEq keyEq selected parent component before@(MkSystemState ambient fibers)
      afterState tag equation | True | Nothing = void (nothingIsNotJust equation)
    oInsertResultLookup {name} {key} {world} {error} {value}
      nameEq keyEq selected parent component before@(MkSystemState ambient fibers)
      afterState tag equation | True | Just applied =
        case justInjective equation of
          Refl => setFreshSelectedLookup selected (freshFiber component parent)
            fibers applied inserted

0 retiredFiberKeepsParent : (fiber : Fiber name key value world error) ->
  fiberParent (retireFiber fiber) = fiberParent fiber
retiredFiberKeepsParent (MkFiber component parent retired table lifecycle) = Refl

||| Exact target lookup for successful retirement of a known fiber, retaining
||| the parent role needed to classify a following O-Remove.
public export
0 oRetireResultLookup :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (fiber : Fiber name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  lookupFiber @{nameEq} selected (registry before) = Just fiber ->
  applyAction @{nameEq} @{keyEq} (ORetire selected) before =
    Just (tag, afterState) ->
  (afterFiber : Fiber name key value world error **
   (lookupFiber @{nameEq} selected (registry afterState) = Just afterFiber,
    fiberParent afterFiber = fiberParent fiber))
oRetireResultLookup nameEq keyEq selected fiber
  (MkSystemState ambient fibers) afterState tag found equation
  with (lookupFiber @{nameEq} selected fibers) proof current
    oRetireResultLookup nameEq keyEq selected fiber
      (MkSystemState ambient fibers) afterState tag found equation |
        Nothing = void (nothingIsNotJust equation)
    oRetireResultLookup nameEq keyEq selected fiber
      (MkSystemState ambient fibers) afterState tag found equation |
        Just observed =
          let sameFiber : (observed = fiber)
              sameFiber = justInjective found in
            case justInjective equation of
              Refl => (retireFiber observed **
                (lookupReplacedFiber selected observed (retireFiber observed)
                  fibers current,
                 trans (retiredFiberKeepsParent observed) (cong fiberParent sameFiber)))

0 stableInstallationEvolution :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  installedAt @{nameEq} selected before =
    installedAt @{nameEq} selected afterState ->
  InstallationEvolution name key world error value nameEq keyEq selected
    before afterState action tag
stableInstallationEvolution nameEq keyEq selected before afterState action tag stable =
  case boolEquality (installedAt @{nameEq} selected before) of
    Left sourceFalse =>
      RemainedUninstalled sourceFalse (trans (sym stable) sourceFalse)
    Right sourceTrue =>
      RemainedInstalled sourceTrue (trans (sym stable) sourceTrue)
  where
  boolEquality : (observed : Bool) ->
    Either (observed = False) (observed = True)
  boolEquality False = Left Refl
  boolEquality True = Right Refl

0 openedEvolutionFrom :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) -> tag = LBeginTag ->
  (checkedEquation : checkedApplyAction @{nameEq} @{keyEq}
    (LBegin selected) before = Just (tag, afterState)) ->
  installedAt @{nameEq} selected before = False ->
  installedAt @{nameEq} selected afterState = True ->
  InstallationEvolution name key world error value nameEq keyEq selected
    before afterState (LBegin selected) tag
openedEvolutionFrom nameEq keyEq selected before afterState LBeginTag Refl
  checkedEquation sourceFalse targetTrue =
  OpenedInstallation

0 closedEvolutionFrom :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) -> tag = LUnloadTag ->
  (checkedEquation : checkedApplyAction @{nameEq} @{keyEq}
    (LUnload selected) before = Just (tag, afterState)) ->
  installedAt @{nameEq} selected before = True ->
  installedAt @{nameEq} selected afterState = False ->
  InstallationEvolution name key world error value nameEq keyEq selected
    before afterState (LUnload selected) tag
closedEvolutionFrom nameEq keyEq selected before afterState LUnloadTag Refl
  checkedEquation sourceTrue targetFalse =
  ClosedInstallation

0 lDivertInstallationEvolution :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) -> tag = LDivertTag ->
  applyAction @{nameEq} @{keyEq} (LDivert selected) before =
    Just (tag, afterState) ->
  InstallationEvolution name key world error value nameEq keyEq selected
    before afterState (LDivert selected) tag
lDivertInstallationEvolution nameEq keyEq selected before afterState LDivertTag
  Refl equation = case lDivertInstalled nameEq keyEq selected before afterState
    equation of
    (sourceTrue, targetTrue) => RemainedInstalled sourceTrue targetTrue

||| Lemma 54(4), packaged for every checked step: L-Begin and L-Unload are the
||| unique installed-bit boundaries; every other selected or foreign action
||| preserves the bit.
public export
0 installationEvolutionStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checkedEquation : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  InstallationEvolution name key world error value nameEq keyEq selected
    before afterState action tag
installationEvolutionStep nameEq keyEq selected action tag before afterState
  checkedEquation with (decEq @{nameEq} selected (actionOwner action))
  installationEvolutionStep nameEq keyEq selected action tag before afterState
    checkedEquation | No distinct =
      foreignInstallationEvolution nameEq keyEq selected action distinct before
        afterState tag (checkedActionProjects nameEq keyEq action before afterState
          tag checkedEquation)
  installationEvolutionStep nameEq keyEq selected
    (OInsert selected parent component) tag before afterState checkedEquation |
    Yes Refl = case oInsertUninstalled nameEq keyEq selected parent component before
        afterState tag (checkedActionProjects nameEq keyEq
          (OInsert selected parent component) before afterState tag checkedEquation) of
        (sourceFalse, targetFalse) =>
          RemainedUninstalled sourceFalse targetFalse
  installationEvolutionStep nameEq keyEq selected (ORetire selected) tag before
    afterState checkedEquation | Yes Refl = stableInstallationEvolution nameEq keyEq selected before afterState
        (ORetire selected) tag (oRetireStable nameEq keyEq selected before afterState tag
          (checkedActionProjects nameEq keyEq (ORetire selected) before afterState
            tag checkedEquation))
  installationEvolutionStep nameEq keyEq selected (ORemove selected) tag before
    afterState checkedEquation | Yes Refl = case oRemoveUninstalled nameEq keyEq selected before afterState tag
        (checkedActionProjects nameEq keyEq (ORemove selected) before afterState
          tag checkedEquation) of
        (sourceFalse, targetFalse) =>
          RemainedUninstalled sourceFalse targetFalse
  installationEvolutionStep nameEq keyEq selected (LBegin selected) tag before
    afterState checkedEquation | Yes Refl = case lBeginBoundary nameEq keyEq selected before afterState tag
        checkedEquation of
        (tagShape, sourceFalse, targetTrue) =>
          openedEvolutionFrom nameEq keyEq selected before afterState tag
            tagShape checkedEquation sourceFalse targetTrue
  installationEvolutionStep nameEq keyEq selected (LAdvance selected) tag before
    afterState checkedEquation | Yes Refl =
        let rawEquation = checkedActionProjects nameEq keyEq (LAdvance selected)
              before afterState tag checkedEquation
        in RemainedInstalled
          (lAdvanceStartsInstalled nameEq keyEq selected before afterState tag
            rawEquation)
          (lAdvanceEndsInstalled nameEq keyEq selected before afterState tag
            rawEquation)
  installationEvolutionStep nameEq keyEq selected (LDivert selected) tag before
    afterState checkedEquation | Yes Refl =
        let rawEquation = checkedActionProjects nameEq keyEq (LDivert selected)
              before afterState tag checkedEquation
            tagShape = successfulLDivertTag nameEq keyEq selected before afterState
              tag rawEquation
        in lDivertInstallationEvolution nameEq keyEq selected before afterState
          tag tagShape rawEquation
  installationEvolutionStep nameEq keyEq selected (LLeave selected) tag before
    afterState checkedEquation | Yes Refl = case lLeaveInstalled nameEq keyEq selected before afterState tag
        (checkedActionProjects nameEq keyEq (LLeave selected) before afterState
          tag checkedEquation) of
        (sourceTrue, targetTrue) => RemainedInstalled sourceTrue targetTrue
  installationEvolutionStep nameEq keyEq selected (LUnload selected) tag before
    afterState checkedEquation | Yes Refl = case lUnloadBoundary nameEq keyEq selected before afterState tag
        (checkedActionProjects nameEq keyEq (LUnload selected) before afterState
          tag checkedEquation) of
        (tagShape, sourceTrue, targetFalse) =>
          closedEvolutionFrom nameEq keyEq selected before afterState tag
            tagShape checkedEquation sourceTrue targetFalse

public export
0 alignedAppendSplit :
  (left : Transitions first middle) -> (right : Transitions middle finalState) ->
  AlignedTransitions name key world error value nameEq keyEq
    (appendTransitions left right) ->
  (AlignedTransitions name key world error value nameEq keyEq left,
   AlignedTransitions name key world error value nameEq keyEq right)
alignedAppendSplit NoTransitions right aligned = (AlignedEnd, aligned)
alignedAppendSplit (MoreTransitions (Fired nameEq keyEq action tag equation) rest)
  right (AlignedStep action tag equation
    (appendTransitions rest right) alignedTail) =
  case alignedAppendSplit rest right alignedTail of
    (leftAligned, rightAligned) =>
      (AlignedStep action tag equation rest leftAligned, rightAligned)

public export
0 appendInstalledTrace :
  (left : Transitions first middle) -> (right : Transitions middle finalState) ->
  InstalledTrace name key world error value nameEq keyEq selected left ->
  InstalledTrace name key world error value nameEq keyEq selected right ->
  InstalledTrace name key world error value nameEq keyEq selected
    (appendTransitions left right)
appendInstalledTrace NoTransitions right (InstalledEnd installed) rightInstalled =
  rightInstalled
appendInstalledTrace
  (MoreTransitions (Fired nameEq keyEq action tag equation) rest) right
  (InstalledStep action tag equation rest sourceInstalled tailInstalled)
  rightInstalled =
    InstalledStep action tag equation (appendTransitions rest right)
      sourceInstalled
      (appendInstalledTrace rest right tailInstalled rightInstalled)

public export
data InstalledEnding :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  EntireTraceInstalled :
    InstalledTrace name key world error value nameEq keyEq selected trace ->
    InstalledEnding name key world error value nameEq keyEq selected trace
  LastOpening :
    (preStart, opened : SystemState name key value world error) ->
    (beforeOpening : Transitions first preStart) ->
    (opening : BeginStep nameEq keyEq selected preStart opened) ->
    (afterOpening : Transitions opened finalState) ->
    appendTransitions beforeOpening
      (MoreTransitions (beginTransition opening) afterOpening) = trace ->
    InstalledTrace name key world error value nameEq keyEq selected afterOpening ->
    InstalledEnding name key world error value nameEq keyEq selected trace

0 unloadTargetUninstalled :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  UnloadStep nameEq keyEq selected before afterState ->
  installedAt @{nameEq} selected afterState = False
unloadTargetUninstalled nameEq keyEq selected before afterState closing =
  case lUnloadBoundary nameEq keyEq selected before afterState LUnloadTag
    (checkedActionProjects nameEq keyEq (LUnload selected) before afterState
      LUnloadTag (unloadEquation closing)) of
    (tagShape, sourceTrue, targetFalse) => targetFalse

0 installedEnding :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (trace : Transitions first finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  installedAt @{nameEq} selected finalState = True ->
  InstalledEnding name key world error value nameEq keyEq selected trace
installedEnding nameEq keyEq selected NoTransitions AlignedEnd endpointTrue =
  EntireTraceInstalled (InstalledEnd endpointTrue)
installedEnding nameEq keyEq selected
  trace@(MoreTransitions (Fired nameEq keyEq action tag equation) rest)
  (AlignedStep action tag equation rest alignedRest) endpointTrue =
  case installedEnding nameEq keyEq selected rest alignedRest endpointTrue of
    LastOpening preStart opened beforeOpening opening afterOpening split
      installedAfter =>
        LastOpening preStart opened
          (MoreTransitions (Fired nameEq keyEq action tag equation) beforeOpening)
          opening afterOpening
          (cong (MoreTransitions (Fired nameEq keyEq action tag equation)) split)
          installedAfter
    EntireTraceInstalled installedRest =>
      case installationEvolutionStep nameEq keyEq selected action tag _ _ equation of
        RemainedInstalled sourceTrue targetTrue =>
          EntireTraceInstalled
            (InstalledStep action tag equation rest sourceTrue installedRest)
        OpenedInstallation =>
          LastOpening _ _ NoTransitions (MkBeginStep equation) rest Refl installedRest
        RemainedUninstalled sourceFalse targetFalse =>
          let targetTrue = installedTraceStart installedRest
          in void (falseNotTrue (trans (sym targetFalse) targetTrue))
        ClosedInstallation =>
          let targetFalse = case lUnloadBoundary nameEq keyEq selected _ _
                LUnloadTag (checkedActionProjects nameEq keyEq (LUnload selected)
                  _ _ LUnloadTag equation) of
                (tagShape, sourceTrue, targetFalse) => targetFalse
              targetTrue = installedTraceStart installedRest
          in void (falseNotTrue (trans (sym targetFalse) targetTrue))
  where
  falseNotTrue : False = True -> Void
  falseNotTrue Refl impossible

public export
record LastOpeningResult
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState) where
  constructor MkLastOpeningResult
  openingPreStart : SystemState name key value world error
  openingStart : SystemState name key value world error
  traceBeforeLastOpening : Transitions first openingPreStart
  lastOpeningStep : BeginStep nameEq keyEq selected openingPreStart openingStart
  traceAfterLastOpening : Transitions openingStart finalState
  openingSplit : appendTransitions traceBeforeLastOpening
    (MoreTransitions (beginTransition lastOpeningStep) traceAfterLastOpening) = trace
  afterOpeningInstalled : InstalledTrace name key world error value nameEq keyEq
    selected traceAfterLastOpening

public export
0 extractLastOpening :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (trace : Transitions first finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  installedAt @{nameEq} selected first = False ->
  installedAt @{nameEq} selected finalState = True ->
  LastOpeningResult name key world error value nameEq keyEq selected trace
extractLastOpening nameEq keyEq selected trace aligned sourceFalse targetTrue =
  case installedEnding nameEq keyEq selected trace aligned targetTrue of
    LastOpening preStart opened before opening after split installedAfter =>
      MkLastOpeningResult preStart opened before opening after split installedAfter
    EntireTraceInstalled installedTrace =>
      let sourceTrue = installedTraceStart installedTrace in
      void (falseNotTrue (trans (sym sourceFalse) sourceTrue))
  where
  falseNotTrue : False = True -> Void
  falseNotTrue Refl impossible

public export
record FirstClosingResult
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState) where
  constructor MkFirstClosingResult
  closingBefore : SystemState name key value world error
  closingAfter : SystemState name key value world error
  traceBeforeFirstClosing : Transitions first closingBefore
  beforeClosingInstalled : InstalledTrace name key world error value nameEq keyEq
    selected traceBeforeFirstClosing
  firstClosingStep : UnloadStep nameEq keyEq selected closingBefore closingAfter
  traceAfterFirstClosing : Transitions closingAfter finalState
  closingSplit : appendTransitions traceBeforeFirstClosing
    (MoreTransitions (unloadTransition firstClosingStep) traceAfterFirstClosing) = trace

public export
0 extractFirstClosing :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (trace : Transitions first finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  installedAt @{nameEq} selected first = True ->
  installedAt @{nameEq} selected finalState = False ->
  FirstClosingResult name key world error value nameEq keyEq selected trace
extractFirstClosing nameEq keyEq selected NoTransitions AlignedEnd sourceTrue
  targetFalse = void (falseNotTrue (trans (sym targetFalse) sourceTrue))
  where
  falseNotTrue : False = True -> Void
  falseNotTrue Refl impossible
extractFirstClosing nameEq keyEq selected
  trace@(MoreTransitions (Fired nameEq keyEq action tag equation) rest)
  (AlignedStep action tag equation rest alignedRest) sourceTrue targetFalse =
  case installationEvolutionStep nameEq keyEq selected action tag _ _ equation of
    ClosedInstallation =>
      MkFirstClosingResult _ _ NoTransitions (InstalledEnd sourceTrue)
        (MkUnloadStep equation) rest Refl
    RemainedInstalled stepSource stepTarget =>
      case extractFirstClosing nameEq keyEq selected rest alignedRest stepTarget
        targetFalse of
        MkFirstClosingResult closeBefore closeAfter beforeClosing installedBefore
          closing afterClosing split =>
            MkFirstClosingResult closeBefore closeAfter
              (MoreTransitions (Fired nameEq keyEq action tag equation) beforeClosing)
              (InstalledStep action tag equation beforeClosing stepSource installedBefore)
              closing afterClosing
              (cong (MoreTransitions (Fired nameEq keyEq action tag equation)) split)
    RemainedUninstalled stepSource stepTarget =>
      void (falseNotTrue (trans (sym stepSource) sourceTrue))
    OpenedInstallation =>
      case lBeginBoundary nameEq keyEq selected _ _ LBeginTag equation of
        (tagShape, openingSourceFalse, openingTargetTrue) =>
          void (falseNotTrue (trans (sym openingSourceFalse) sourceTrue))
  where
  falseNotTrue : False = True -> Void
  falseNotTrue Refl impossible

public export
0 appendTransitionsAssociative :
  (left : Transitions first middle) ->
  (center : Transitions middle later) ->
  (right : Transitions later finalState) ->
  appendTransitions (appendTransitions left center) right =
    appendTransitions left (appendTransitions center right)
appendTransitionsAssociative NoTransitions center right = Refl
appendTransitionsAssociative (MoreTransitions transition rest) center right =
  cong (MoreTransitions transition)
    (appendTransitionsAssociative rest center right)

0 spanningDecomposition :
  (beforeOpening : Transitions initial preStart) ->
  (opening : BeginStep nameEq keyEq selected preStart opened) ->
  (afterOpening : Transitions opened anchor) ->
  (beforeClosing : Transitions anchor closeBefore) ->
  (closing : UnloadStep nameEq keyEq selected closeBefore closeAfter) ->
  (afterClosing : Transitions closeAfter finalState) ->
  (leftTrace : Transitions initial anchor) ->
  (rightTrace : Transitions anchor finalState) ->
  appendTransitions beforeOpening
    (MoreTransitions (beginTransition opening) afterOpening) = leftTrace ->
  appendTransitions beforeClosing
    (MoreTransitions (unloadTransition closing) afterClosing) = rightTrace ->
  appendTransitions beforeOpening
    (MoreTransitions (beginTransition opening)
      (appendTransitions (appendTransitions afterOpening beforeClosing)
        (MoreTransitions (unloadTransition closing) afterClosing))) =
  appendTransitions leftTrace rightTrace
spanningDecomposition beforeOpening opening afterOpening beforeClosing closing
  afterClosing leftTrace rightTrace openingSplit closingSplit =
  rewrite appendTransitionsAssociative afterOpening beforeClosing
    (MoreTransitions (unloadTransition closing) afterClosing) in
  rewrite closingSplit in
  rewrite sym (appendTransitionsAssociative beforeOpening
    (MoreTransitions (beginTransition opening) afterOpening) rightTrace) in
  rewrite openingSplit in Refl

||| Boundary-selection core of Theorem 63: an installed anchor between an
||| initially uninstalled state and an uninstalled endpoint determines the
||| unique last-open/first-close episode spanning that anchor.
public export
0 extractSpanningClosedEpisode :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (leftTrace : Transitions initial anchor) ->
  (rightTrace : Transitions anchor finalState) ->
  AlignedTransitions name key world error value nameEq keyEq leftTrace ->
  AlignedTransitions name key world error value nameEq keyEq rightTrace ->
  installedAt @{nameEq} selected initial = False ->
  installedAt @{nameEq} selected anchor = True ->
  installedAt @{nameEq} selected finalState = False ->
  LocatedClosedEpisode name key world error value nameEq keyEq selected
    (appendTransitions leftTrace rightTrace)
extractSpanningClosedEpisode nameEq keyEq selected leftTrace rightTrace prefixAligned
  suffixAligned initialFalse anchorTrue finalFalse =
  case extractLastOpening nameEq keyEq selected leftTrace prefixAligned initialFalse
    anchorTrue of
    MkLastOpeningResult preStart opened beforeOpening opening afterOpening
      openingSplit installedAfterOpening =>
      case extractFirstClosing nameEq keyEq selected rightTrace suffixAligned anchorTrue
        finalFalse of
        MkFirstClosingResult closeBefore closeAfter beforeClosing installedBeforeClosing
          closing afterClosing closingSplit =>
            let insideInstalled = appendInstalledTrace afterOpening beforeClosing
                  installedAfterOpening installedBeforeClosing
                decomposition = spanningDecomposition beforeOpening opening afterOpening
                  beforeClosing closing afterClosing leftTrace rightTrace openingSplit closingSplit
                locatedDecomposition :
                  (appendTransitions beforeOpening
                    (MoreTransitions (beginTransition opening)
                      (appendTransitions
                        (appendTransitions (appendTransitions afterOpening beforeClosing)
                          (MoreTransitions (unloadTransition closing) NoTransitions))
                        afterClosing)) =
                  appendTransitions leftTrace rightTrace)
                locatedDecomposition =
                  rewrite appendTransitionsAssociative
                    (appendTransitions afterOpening beforeClosing)
                    (MoreTransitions (unloadTransition closing) NoTransitions)
                    afterClosing in decomposition
            in MkLocatedClosedEpisode preStart closeAfter beforeOpening
              (MkClosedEpisode opened closeBefore opening
                (appendTransitions afterOpening beforeClosing)
                insideInstalled closing)
              afterClosing locatedDecomposition

0 resolvedViewLookup :
  {name, key : Type} -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  (wanted : key) -> (provider : name) ->
  (case viewLookup @{keyEq} wanted deps view of
     Nothing => False
     Just actual => case decEq @{nameEq} actual provider of
       Yes Refl => True
       No _ => False) = True ->
  viewLookup @{keyEq} wanted deps view = Just provider
resolvedViewLookup nameEq keyEq deps view wanted provider valid
  with (viewLookup @{keyEq} wanted deps view) proof found
  resolvedViewLookup nameEq keyEq deps view wanted provider valid | Nothing = absurd valid
  resolvedViewLookup nameEq keyEq deps view wanted provider valid | Just actual
    with (decEq @{nameEq} actual provider)
    resolvedViewLookup nameEq keyEq deps view wanted actual valid | Just actual | Yes Refl =
      rewrite sym found in Refl
    resolvedViewLookup nameEq keyEq deps view wanted provider valid | Just actual | No distinct =
      absurd valid

public export
cp3AndLeftTrue : (left, right : Bool) -> left && right = True -> left = True
cp3AndLeftTrue False right valid = absurd valid
cp3AndLeftTrue True right valid = Refl

public export
cp3AndRightTrue : (left, right : Bool) -> left && right = True -> right = True
cp3AndRightTrue False right valid = absurd valid
cp3AndRightTrue True False valid = absurd valid
cp3AndRightTrue True True valid = Refl

0 viewLookupStableProvider :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  (wanted : key) -> (provider : name) ->
  (fibers : Registry name key value world error) ->
  (resolvedLookup : viewLookup @{keyEq} wanted deps view = Just provider) ->
  (providersValid : viewProvidersInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fibers view = True) ->
  (providerFiber : Fiber name key value world error **
    (lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} provider fibers = Just providerFiber,
     stableProvider (fiberLifecycle providerFiber) = True))
viewLookupStableProvider nameEq keyEq [] EmptyView wanted provider fibers
  lookup valid = case lookup of Refl impossible
viewLookupStableProvider nameEq keyEq (current :: rest)
  (ProviderView currentProvider viewTail) wanted provider fibers lookup valid
  with (decEq @{keyEq} wanted current)
  viewLookupStableProvider nameEq keyEq (current :: rest)
    (ProviderView currentProvider viewTail) current provider fibers lookup valid |
    Yes Refl = case justInjective lookup of
      Refl => stableHead valid
    where
    stableHead :
      viewProvidersInvariant @{nameEq} {key = key} {value = value}
        {world = world} {error = error} fibers
        (ProviderView currentProvider viewTail) = True ->
      (providerFiber : Fiber name key value world error **
        (lookupFiber @{nameEq} {key = key} {value = value}
          {world = world} {error = error} currentProvider fibers = Just providerFiber,
         stableProvider (fiberLifecycle providerFiber) = True))
    stableHead headValid with (lookupFiber @{nameEq} {key = key} {value = value}
        {world = world} {error = error} currentProvider fibers)
      proof providerFound
      stableHead headValid | Nothing = absurd headValid
      stableHead headValid | Just providerFiber =
        let providerStable = cp3AndLeftTrue
              (stableProvider (fiberLifecycle providerFiber))
              (viewProvidersInvariant @{nameEq} {key = key} {value = value}
                {world = world} {error = error} fibers viewTail) headValid
        in (providerFiber ** (Refl, providerStable))
  viewLookupStableProvider nameEq keyEq (current :: rest)
    (ProviderView currentProvider viewTail) wanted provider fibers lookup valid |
    No distinct =
      viewLookupStableProvider nameEq keyEq rest viewTail wanted provider fibers lookup
        (viewProvidersTailValid nameEq currentProvider current viewTail fibers valid)

0 resolvedViewValue :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  (wanted : key) -> (provider : name) ->
  (fibers : Registry name key value world error) ->
  (resolvedLookup : viewLookup @{keyEq} wanted deps view = Just provider) ->
  (valuesValid : isJust
    (resolveCommittedValues @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps view fibers) = True) ->
  (provided : value wanted **
    valueFromProvider @{nameEq} @{keyEq} {value = value} {world = world} {error = error} provider wanted fibers = Just provided)
resolvedViewValue nameEq keyEq [] EmptyView wanted provider fibers lookup valid =
  case lookup of Refl impossible
resolvedViewValue nameEq keyEq (current :: rest)
  (ProviderView currentProvider viewTail) wanted provider fibers lookup valid
  with (decEq @{keyEq} wanted current)
  resolvedViewValue nameEq keyEq (current :: rest)
    (ProviderView currentProvider viewTail) current provider fibers lookup valid |
    Yes Refl = case justInjective lookup of
      Refl => resolvedHead valid
    where
    resolvedHead :
      isJust (resolveCommittedValues @{nameEq} @{keyEq} {value = value}
        {world = world} {error = error}
        (current :: rest) (ProviderView currentProvider viewTail) fibers) = True ->
      (provided : value current **
        valueFromProvider @{nameEq} @{keyEq} {value = value}
          {world = world} {error = error} currentProvider current fibers =
          Just provided)
    resolvedHead headValid
      with (valueFromProvider @{nameEq} @{keyEq} {value = value}
        {world = world} {error = error} currentProvider current fibers)
      proof currentValue
      resolvedHead headValid | Nothing = absurd headValid
      resolvedHead headValid | Just provided = (provided ** Refl)
  resolvedViewValue nameEq keyEq (current :: rest)
    (ProviderView currentProvider viewTail) wanted provider fibers lookup valid |
    No distinct with (valueFromProvider @{nameEq} @{keyEq} {value = value}
        {world = world} {error = error} currentProvider current fibers)
    proof currentValue
    resolvedViewValue nameEq keyEq (current :: rest)
      (ProviderView currentProvider viewTail) wanted provider fibers lookup valid |
      No distinct | Nothing = absurd valid
    resolvedViewValue nameEq keyEq (current :: rest)
      (ProviderView currentProvider viewTail) wanted provider fibers lookup valid |
      No distinct | Just currentProvided
      with (resolveCommittedValues @{nameEq} @{keyEq} rest viewTail fibers)
      proof tailValues
      resolvedViewValue nameEq keyEq (current :: rest)
        (ProviderView currentProvider viewTail) wanted provider fibers lookup valid |
        No distinct | Just currentProvided | Nothing = absurd valid
      resolvedViewValue nameEq keyEq (current :: rest)
        (ProviderView currentProvider viewTail) wanted provider fibers lookup valid |
        No distinct | Just currentProvided | Just values =
          resolvedViewValue nameEq keyEq rest viewTail wanted provider fibers lookup
            (cong isJust tailValues)

0 stableProviderImpliesInstalled :
  (lifecycle : Lifecycle key value world error name deps provision) ->
  stableProvider lifecycle = True -> installed lifecycle = True
stableProviderImpliesInstalled (Inactive outcome) valid = absurd valid
stableProviderImpliesInstalled (Reloading remaining accumulator view) valid =
  absurd valid
stableProviderImpliesInstalled (Active accumulator view) valid = Refl
stableProviderImpliesInstalled (Unloading accumulator view outcome) valid = Refl

public export
record ResolvedProviderData
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (consumer : name) (wanted : key) (provider : name)
  (state : SystemState name key value world error) where
  constructor MkResolvedProviderData
  resolvedProviderFiber : Fiber name key value world error
  resolvedProviderLookup : lookupFiber @{nameEq} provider (registry state) =
    Just resolvedProviderFiber
  resolvedProviderStable : stableProvider
    (fiberLifecycle resolvedProviderFiber) = True
  resolvedValue : value wanted
  resolvedValuePresent : providerValueAt @{nameEq} @{keyEq} provider wanted state =
    Just resolvedValue
  resolvedProviderInstalled : installedAt @{nameEq} provider state = True



0 resolvedProviderFromView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (consumer : name) -> (wanted : key) -> (provider : name) ->
  (state : SystemState name key value world error) ->
  (deps : List key) -> (view : View name deps) ->
  (resolvedLookup : viewLookup @{keyEq} wanted deps view = Just provider) ->
  (viewValid : viewBindingsInvariant @{nameEq} @{keyEq}
    {value = value} {world = world} {error = error} deps view
    (registry state) = True) ->
  ResolvedProviderData name key world error value nameEq keyEq consumer wanted
    provider state
resolvedProviderFromView {name} {key} {world} {error} {value}
  nameEq keyEq consumer wanted provider state deps view
  resolvedLookup viewValid =
  let providersValid = cp3AndLeftTrue
        (viewProvidersInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (registry state) view)
        (isJust (resolveCommittedValues @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps view
          (registry state))) viewValid
      valuesValid = cp3AndRightTrue
        (viewProvidersInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (registry state) view)
        (isJust (resolveCommittedValues @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps view
          (registry state))) viewValid
  in case viewLookupStableProvider nameEq keyEq deps view wanted provider
       (registry state) resolvedLookup providersValid of
    (providerFiber ** (providerFound, providerStable)) =>
      case resolvedViewValue nameEq keyEq deps view wanted provider
        (registry state) resolvedLookup valuesValid of
        (provided ** valuePresent) =>
          let providerInstalled = trans
                (installedAtFound nameEq provider state providerFiber providerFound)
                (stableProviderImpliesInstalled
                  (fiberLifecycle providerFiber) providerStable)
          in MkResolvedProviderData providerFiber providerFound providerStable
            provided valuePresent providerInstalled

public export
0 committedViewBindingsValid :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  (view : View name (dependencies
    (componentDependencies (fiberComponent fiber)))) ->
  (fiberValid : fiberViewInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} fiber fibers = True) ->
  (committedEquation : committed (fiberLifecycle fiber) = Just view) ->
  viewBindingsInvariant @{nameEq} @{keyEq}
    {value = value} {world = world} {error = error}
    (dependencies (componentDependencies (fiberComponent fiber))) view fibers = True
committedViewBindingsValid nameEq keyEq
  (MkFiber component parent retired table (Inactive outcome)) fibers view valid
  committedEquation = case committedEquation of Refl impossible
committedViewBindingsValid nameEq keyEq
  (MkFiber component parent retired table
    (Reloading remaining accumulator actualView)) fibers view valid
  committedEquation = case justInjective committedEquation of Refl => valid
committedViewBindingsValid nameEq keyEq
  (MkFiber component parent retired table (Active accumulator actualView))
  fibers view valid committedEquation =
    case justInjective committedEquation of Refl => valid
committedViewBindingsValid nameEq keyEq
  (MkFiber component parent retired table
    (Unloading accumulator actualView outcome)) fibers view valid
  committedEquation = case justInjective committedEquation of Refl => valid

0 resolvedCommittedFiberData :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (consumer : name) -> (wanted : key) -> (provider : name) ->
  (state : SystemState name key value world error) ->
  (consumerFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} consumer (registry state) = Just consumerFiber ->
  registryWellFormed @{nameEq} @{keyEq} state = True ->
  (view : View name (dependencies
    (componentDependencies (fiberComponent consumerFiber)))) ->
  committed (fiberLifecycle consumerFiber) = Just view ->
  (resolvedLookup : viewLookup @{keyEq} wanted
    (dependencies (componentDependencies (fiberComponent consumerFiber))) view =
    Just provider) ->
  ResolvedProviderData name key world error value nameEq keyEq consumer wanted
    provider state
resolvedCommittedFiberData {name} {key} {world} {error} {value}
  nameEq keyEq consumer wanted provider state@(MkSystemState ambient fibers)
  consumerFiber consumerFound wellFormed view committedEquation resolvedLookup =
  let allViews = sourceViewsFromWellFormed nameEq keyEq ambient fibers wellFormed
      entryPresent = lookupFiberEntries nameEq consumer consumerFiber fibers
        consumerFound
      selectedControl = viewsInvariantLookup nameEq keyEq consumer consumerFiber
        (registryFibers fibers) fibers entryPresent allViews
      selectedValid = committedViewBindingsValid nameEq keyEq consumerFiber fibers
        view selectedControl committedEquation
  in resolvedProviderFromView nameEq keyEq consumer wanted provider state
    (dependencies (componentDependencies (fiberComponent consumerFiber))) view
    resolvedLookup selectedValid

0 trueFalseImpossible :
  {observed : Bool} -> {result : Type} ->
  observed = True -> observed = False -> result
trueFalseImpossible Refl Refl impossible

0 equalTrueEqualFalseImpossible :
  {left, middle : Bool} -> {result : Type} ->
  left = True -> left = middle -> middle = False -> result
equalTrueEqualFalseImpossible Refl Refl Refl impossible

||| A well-formed committed consumer view yields both the installed provider
||| witness needed for boundary extraction and the concrete opening value.
public export
0 resolvedProviderData :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (consumer : name) -> (wanted : key) -> (provider : name) ->
  (state : SystemState name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} state = True ->
  resolvedProviderAt @{nameEq} @{keyEq} consumer wanted provider state = True ->
  ResolvedProviderData name key world error value nameEq keyEq consumer wanted
    provider state
resolvedProviderData nameEq keyEq consumer wanted provider (MkSystemState ambient fibers) wellFormed resolved
  with (lookupFiber @{nameEq} consumer fibers) proof consumerFound
  resolvedProviderData nameEq keyEq consumer wanted provider (MkSystemState ambient fibers) wellFormed resolved |
    Nothing = absurd resolved
  resolvedProviderData nameEq keyEq consumer wanted provider (MkSystemState ambient fibers) wellFormed resolved |
    Just fiber@(MkFiber component parent retired table (Inactive outcome)) =
      absurd resolved
  resolvedProviderData nameEq keyEq consumer wanted provider (MkSystemState ambient fibers) wellFormed resolved |
    Just fiber@(MkFiber component parent retired table
      (Reloading remaining accumulator view))
    with (viewLookup @{keyEq} wanted
      (dependencies (componentDependencies component)) view) proof selectedProvider
    resolvedProviderData nameEq keyEq consumer wanted provider (MkSystemState ambient fibers) wellFormed resolved |
      Just fiber@(MkFiber component parent retired table
        (Reloading remaining accumulator view)) | Nothing = absurd resolved
    resolvedProviderData nameEq keyEq consumer wanted provider (MkSystemState ambient fibers) wellFormed resolved |
      Just fiber@(MkFiber component parent retired table
        (Reloading remaining accumulator view)) | Just actual
      with (decEq @{nameEq} actual provider)
      resolvedProviderData nameEq keyEq consumer wanted provider (MkSystemState ambient fibers) wellFormed resolved |
        Just fiber@(MkFiber component parent retired table
          (Reloading remaining accumulator view)) | Just actual | Yes equal =
          case equal of
            Refl => resolvedCommittedFiberData nameEq keyEq consumer wanted actual (MkSystemState ambient fibers)
              (MkFiber component parent retired table
                (Reloading remaining accumulator view)) consumerFound wellFormed view
              Refl selectedProvider
      resolvedProviderData nameEq keyEq consumer wanted provider (MkSystemState ambient fibers) wellFormed resolved |
        Just fiber@(MkFiber component parent retired table
          (Reloading remaining accumulator view)) | Just actual | No distinct = absurd resolved
  resolvedProviderData nameEq keyEq consumer wanted provider (MkSystemState ambient fibers) wellFormed resolved |
    Just fiber@(MkFiber component parent retired table (Active accumulator view))
    with (viewLookup @{keyEq} wanted
      (dependencies (componentDependencies component)) view) proof selectedProvider
    resolvedProviderData nameEq keyEq consumer wanted provider (MkSystemState ambient fibers) wellFormed resolved |
      Just fiber@(MkFiber component parent retired table (Active accumulator view)) |
      Nothing = absurd resolved
    resolvedProviderData nameEq keyEq consumer wanted provider (MkSystemState ambient fibers) wellFormed resolved |
      Just fiber@(MkFiber component parent retired table (Active accumulator view)) |
      Just actual with (decEq @{nameEq} actual provider)
      resolvedProviderData nameEq keyEq consumer wanted provider (MkSystemState ambient fibers) wellFormed resolved |
        Just fiber@(MkFiber component parent retired table (Active accumulator view)) |
        Just actual | Yes equal = case equal of
          Refl => resolvedCommittedFiberData nameEq keyEq consumer wanted actual (MkSystemState ambient fibers)
            (MkFiber component parent retired table (Active accumulator view))
            consumerFound wellFormed view Refl selectedProvider
      resolvedProviderData nameEq keyEq consumer wanted provider (MkSystemState ambient fibers) wellFormed resolved |
        Just fiber@(MkFiber component parent retired table (Active accumulator view)) |
        Just actual | No distinct = absurd resolved
  resolvedProviderData nameEq keyEq consumer wanted provider (MkSystemState ambient fibers) wellFormed resolved |
    Just fiber@(MkFiber component parent retired table
      (Unloading accumulator view outcome))
    with (viewLookup @{keyEq} wanted
      (dependencies (componentDependencies component)) view) proof selectedProvider
    resolvedProviderData nameEq keyEq consumer wanted provider (MkSystemState ambient fibers) wellFormed resolved |
      Just fiber@(MkFiber component parent retired table
        (Unloading accumulator view outcome)) | Nothing = absurd resolved
    resolvedProviderData nameEq keyEq consumer wanted provider (MkSystemState ambient fibers) wellFormed resolved |
      Just fiber@(MkFiber component parent retired table
        (Unloading accumulator view outcome)) | Just actual
      with (decEq @{nameEq} actual provider)
      resolvedProviderData nameEq keyEq consumer wanted provider (MkSystemState ambient fibers) wellFormed resolved |
        Just fiber@(MkFiber component parent retired table
          (Unloading accumulator view outcome)) | Just actual | Yes equal =
          case equal of
            Refl => resolvedCommittedFiberData nameEq keyEq consumer wanted actual (MkSystemState ambient fibers)
              (MkFiber component parent retired table
                (Unloading accumulator view outcome)) consumerFound wellFormed view
              Refl selectedProvider
      resolvedProviderData nameEq keyEq consumer wanted provider (MkSystemState ambient fibers) wellFormed resolved |
        Just fiber@(MkFiber component parent retired table
          (Unloading accumulator view outcome)) | Just actual | No distinct = absurd resolved
fiberResolvesWith : (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (provider : name) ->
  Fiber name key value world error -> Bool
fiberResolvesWith nameEq keyEq wanted provider
  (MkFiber component parent retired table lifecycle) =
  case committed lifecycle of
    Nothing => False
    Just view => case viewLookup @{keyEq} wanted
      (dependencies (componentDependencies component)) view of
        Nothing => False
        Just actual => case decEq @{nameEq} actual provider of
          Yes Refl => True
          No _ => False

0 fiberResolvesWithMatches :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (provider : name) ->
  (fiber : Fiber name key value world error) ->
  fiberResolvesWith nameEq keyEq wanted provider fiber =
    fiberResolvedProvider @{nameEq} @{keyEq} wanted provider fiber
fiberResolvesWithMatches nameEq keyEq wanted provider
  (MkFiber component parent retired table (Inactive outcome)) = Refl
fiberResolvesWithMatches nameEq keyEq wanted provider
  (MkFiber component parent retired table
    (Reloading remaining accumulator view))
  with (viewLookup @{keyEq} wanted
    (dependencies (componentDependencies component)) view)
  fiberResolvesWithMatches nameEq keyEq wanted provider
    (MkFiber component parent retired table
      (Reloading remaining accumulator view)) | Nothing = Refl
  fiberResolvesWithMatches nameEq keyEq wanted provider
    (MkFiber component parent retired table
      (Reloading remaining accumulator view)) | Just actual
    with (decEq @{nameEq} actual provider)
    fiberResolvesWithMatches nameEq keyEq wanted provider
      (MkFiber component parent retired table
        (Reloading remaining accumulator view)) | Just actual | Yes equal =
        case equal of Refl => Refl
    fiberResolvesWithMatches nameEq keyEq wanted provider
      (MkFiber component parent retired table
        (Reloading remaining accumulator view)) | Just actual | No distinct = Refl
fiberResolvesWithMatches nameEq keyEq wanted provider
  (MkFiber component parent retired table (Active accumulator view))
  with (viewLookup @{keyEq} wanted
    (dependencies (componentDependencies component)) view)
  fiberResolvesWithMatches nameEq keyEq wanted provider
    (MkFiber component parent retired table (Active accumulator view)) |
    Nothing = Refl
  fiberResolvesWithMatches nameEq keyEq wanted provider
    (MkFiber component parent retired table (Active accumulator view)) |
    Just actual with (decEq @{nameEq} actual provider)
    fiberResolvesWithMatches nameEq keyEq wanted provider
      (MkFiber component parent retired table (Active accumulator view)) |
      Just actual | Yes equal = case equal of Refl => Refl
    fiberResolvesWithMatches nameEq keyEq wanted provider
      (MkFiber component parent retired table (Active accumulator view)) |
      Just actual | No distinct = Refl
fiberResolvesWithMatches nameEq keyEq wanted provider
  (MkFiber component parent retired table
    (Unloading accumulator view outcome))
  with (viewLookup @{keyEq} wanted
    (dependencies (componentDependencies component)) view)
  fiberResolvesWithMatches nameEq keyEq wanted provider
    (MkFiber component parent retired table
      (Unloading accumulator view outcome)) | Nothing = Refl
  fiberResolvesWithMatches nameEq keyEq wanted provider
    (MkFiber component parent retired table
      (Unloading accumulator view outcome)) | Just actual
    with (decEq @{nameEq} actual provider)
    fiberResolvesWithMatches nameEq keyEq wanted provider
      (MkFiber component parent retired table
        (Unloading accumulator view outcome)) | Just actual | Yes equal =
        case equal of Refl => Refl
    fiberResolvesWithMatches nameEq keyEq wanted provider
      (MkFiber component parent retired table
        (Unloading accumulator view outcome)) | Just actual | No distinct = Refl

fiberResolves : DecEq name => DecEq key => (wanted : key) -> (provider : name) ->
  Fiber name key value world error -> Bool
fiberResolves @{nameEq} @{keyEq} = fiberResolvesWith nameEq keyEq

resolvedMaybeFiberWith : (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (provider : name) ->
  Maybe (Fiber name key value world error) -> Bool
resolvedMaybeFiberWith nameEq keyEq wanted provider Nothing = False
resolvedMaybeFiberWith nameEq keyEq wanted provider (Just fiber) =
  fiberResolvesWith nameEq keyEq wanted provider fiber


0 resolvedAtLookupEquation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (consumer : name) -> (wanted : key) -> (provider : name) ->
  (state : SystemState name key value world error) ->
  resolvedProviderAt @{nameEq} @{keyEq} consumer wanted provider state =
    resolvedMaybeFiberWith {value = value} {world = world} {error = error}
      nameEq keyEq wanted provider (lookupFiber @{nameEq} consumer (registry state))
resolvedAtLookupEquation nameEq keyEq consumer wanted provider
  state@(MkSystemState ambient fibers)
  with (lookupFiber @{nameEq} consumer fibers)
  resolvedAtLookupEquation nameEq keyEq consumer wanted provider
    state@(MkSystemState ambient fibers) | Nothing = Refl
  resolvedAtLookupEquation nameEq keyEq consumer wanted provider
    state@(MkSystemState ambient fibers) |
    Just (MkFiber component parent retired table (Inactive outcome)) = Refl
  resolvedAtLookupEquation nameEq keyEq consumer wanted provider
    state@(MkSystemState ambient fibers) |
    Just (MkFiber component parent retired table
      (Reloading remaining accumulator view))
    with (viewLookup @{keyEq} wanted
      (dependencies (componentDependencies component)) view)
    resolvedAtLookupEquation nameEq keyEq consumer wanted provider
      state@(MkSystemState ambient fibers) |
      Just (MkFiber component parent retired table
        (Reloading remaining accumulator view)) | Nothing = Refl
    resolvedAtLookupEquation nameEq keyEq consumer wanted provider
      state@(MkSystemState ambient fibers) |
      Just (MkFiber component parent retired table
        (Reloading remaining accumulator view)) | Just actual
      with (decEq @{nameEq} actual provider)
      resolvedAtLookupEquation nameEq keyEq consumer wanted provider
        state@(MkSystemState ambient fibers) |
        Just (MkFiber component parent retired table
          (Reloading remaining accumulator view)) | Just actual | Yes equal =
          case equal of Refl => Refl
      resolvedAtLookupEquation nameEq keyEq consumer wanted provider
        state@(MkSystemState ambient fibers) |
        Just (MkFiber component parent retired table
          (Reloading remaining accumulator view)) | Just actual | No distinct = Refl
  resolvedAtLookupEquation nameEq keyEq consumer wanted provider
    state@(MkSystemState ambient fibers) |
    Just (MkFiber component parent retired table (Active accumulator view))
    with (viewLookup @{keyEq} wanted
      (dependencies (componentDependencies component)) view)
    resolvedAtLookupEquation nameEq keyEq consumer wanted provider
      state@(MkSystemState ambient fibers) |
      Just (MkFiber component parent retired table (Active accumulator view)) |
      Nothing = Refl
    resolvedAtLookupEquation nameEq keyEq consumer wanted provider
      state@(MkSystemState ambient fibers) |
      Just (MkFiber component parent retired table (Active accumulator view)) |
      Just actual with (decEq @{nameEq} actual provider)
      resolvedAtLookupEquation nameEq keyEq consumer wanted provider
        state@(MkSystemState ambient fibers) |
        Just (MkFiber component parent retired table (Active accumulator view)) |
        Just actual | Yes equal = case equal of Refl => Refl
      resolvedAtLookupEquation nameEq keyEq consumer wanted provider
        state@(MkSystemState ambient fibers) |
        Just (MkFiber component parent retired table (Active accumulator view)) |
        Just actual | No distinct = Refl
  resolvedAtLookupEquation nameEq keyEq consumer wanted provider
    state@(MkSystemState ambient fibers) |
    Just (MkFiber component parent retired table
      (Unloading accumulator view outcome))
    with (viewLookup @{keyEq} wanted
      (dependencies (componentDependencies component)) view)
    resolvedAtLookupEquation nameEq keyEq consumer wanted provider
      state@(MkSystemState ambient fibers) |
      Just (MkFiber component parent retired table
        (Unloading accumulator view outcome)) | Nothing = Refl
    resolvedAtLookupEquation nameEq keyEq consumer wanted provider
      state@(MkSystemState ambient fibers) |
      Just (MkFiber component parent retired table
        (Unloading accumulator view outcome)) | Just actual
      with (decEq @{nameEq} actual provider)
      resolvedAtLookupEquation nameEq keyEq consumer wanted provider
        state@(MkSystemState ambient fibers) |
        Just (MkFiber component parent retired table
          (Unloading accumulator view outcome)) | Just actual | Yes equal =
          case equal of Refl => Refl
      resolvedAtLookupEquation nameEq keyEq consumer wanted provider
        state@(MkSystemState ambient fibers) |
        Just (MkFiber component parent retired table
          (Unloading accumulator view outcome)) | Just actual | No distinct = Refl

0 resolvedAtAfterReplace :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (consumer : name) -> (wanted : key) -> (provider : name) ->
  (sourceFiber, targetFiberValue : Fiber name key value world error) ->
  (fibers : Registry name key value world error) -> (ambient : world) ->
  (found : lookupFiber @{nameEq} consumer fibers = Just sourceFiber) ->
  resolvedProviderAt @{nameEq} @{keyEq} consumer wanted provider
    (the (SystemState name key value world error)
      (MkSystemState ambient
        (replaceBinding @{nameEq} consumer targetFiberValue fibers))) =
  fiberResolves @{nameEq} @{keyEq} wanted provider targetFiberValue
resolvedAtAfterReplace {name} {key} {world} {error} {value}
  nameEq keyEq consumer wanted provider sourceFiber targetFiberValue fibers
  ambient found =
  trans (resolvedAtLookupEquation nameEq keyEq consumer wanted provider
    (MkSystemState ambient
      (replaceBinding @{nameEq} consumer targetFiberValue fibers)))
    (cong (resolvedMaybeFiberWith nameEq keyEq wanted provider)
      (lookupReplacedFiber consumer sourceFiber targetFiberValue fibers found))

0 fiberResolvedProviderSetRuntimeSameCommitted :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (provider : name) ->
  (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLife : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  committed (fiberLifecycle fiber) = Just view ->
  committed newLife = Just view ->
  fiberResolves @{nameEq} @{keyEq} wanted provider
    (setFiberRuntime fiber newTable newLife) =
  fiberResolves @{nameEq} @{keyEq} wanted provider fiber
fiberResolvedProviderSetRuntimeSameCommitted nameEq keyEq wanted provider
  fiber newTable newLife view sourceCommitted targetCommitted =
    trans (fiberResolvesWithMatches nameEq keyEq wanted provider
      (setFiberRuntime fiber newTable newLife))
      (trans (fiberResolvedProviderSetRuntimeFrame nameEq keyEq wanted provider
        fiber newTable newLife view sourceCommitted targetCommitted)
        (sym (fiberResolvesWithMatches nameEq keyEq wanted provider fiber)))

0 reloadingToReloadingResolution : DecEq name => DecEq key =>
  (wanted : key) -> (provider : name) ->
  (fiber : Fiber name key value world error) ->
  {remaining : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)))} ->
  {accumulator : LocalState key value world
    (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world (componentProvisions (fiberComponent fiber))} ->
  {view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))} ->
  fiberLifecycle fiber = Reloading remaining accumulator view ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newRemaining : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)))) ->
  (newAccumulator : LocalState key value world
    (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world (componentProvisions (fiberComponent fiber))) ->
  fiberResolves wanted provider
    (setFiberRuntime fiber newTable
      (Reloading newRemaining newAccumulator view)) =
  fiberResolves wanted provider fiber
reloadingToReloadingResolution @{nameEq} @{keyEq} wanted provider
  fiber@(MkFiber component parent retired table
    (Reloading remaining accumulator view)) Refl newTable newRemaining
  newAccumulator =
    fiberResolvedProviderSetRuntimeSameCommitted nameEq keyEq wanted provider
      fiber newTable (Reloading newRemaining newAccumulator view) view Refl Refl

0 reloadingToActiveResolution : DecEq name => DecEq key =>
  (wanted : key) -> (provider : name) ->
  (fiber : Fiber name key value world error) ->
  {remaining : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)))} ->
  {accumulator : LocalState key value world
    (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world (componentProvisions (fiberComponent fiber))} ->
  {view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))} ->
  fiberLifecycle fiber = Reloading remaining accumulator view ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newAccumulator : LocalState key value world
    (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world (componentProvisions (fiberComponent fiber))) ->
  fiberResolves wanted provider
    (setFiberRuntime fiber newTable (Active newAccumulator view)) =
  fiberResolves wanted provider fiber
reloadingToActiveResolution @{nameEq} @{keyEq} wanted provider
  fiber@(MkFiber component parent retired table
    (Reloading remaining accumulator view)) Refl newTable newAccumulator =
    fiberResolvedProviderSetRuntimeSameCommitted nameEq keyEq wanted provider
      fiber newTable (Active newAccumulator view) view Refl Refl

0 reloadingToUnloadingResolution : DecEq name => DecEq key =>
  (wanted : key) -> (provider : name) ->
  (fiber : Fiber name key value world error) ->
  {remaining : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)))} ->
  {accumulator : LocalState key value world
    (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world (componentProvisions (fiberComponent fiber))} ->
  {view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))} ->
  fiberLifecycle fiber = Reloading remaining accumulator view ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newAccumulator : LocalState key value world
    (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world (componentProvisions (fiberComponent fiber))) ->
  (outcome : Maybe error) ->
  fiberResolves wanted provider
    (setFiberRuntime fiber newTable
      (Unloading newAccumulator view outcome)) =
  fiberResolves wanted provider fiber
reloadingToUnloadingResolution @{nameEq} @{keyEq} wanted provider
  fiber@(MkFiber component parent retired table
    (Reloading remaining accumulator view)) Refl newTable newAccumulator outcome =
    fiberResolvedProviderSetRuntimeSameCommitted nameEq keyEq wanted provider
      fiber newTable (Unloading newAccumulator view outcome) view Refl Refl

0 activeToUnloadingResolution : DecEq name => DecEq key =>
  (wanted : key) -> (provider : name) ->
  (fiber : Fiber name key value world error) ->
  {accumulator : LocalState key value world
    (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world (componentProvisions (fiberComponent fiber))} ->
  {view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))} ->
  fiberLifecycle fiber = Active accumulator view ->
  fiberResolves wanted provider
    (setFiberLifecycle fiber (Unloading accumulator view Nothing)) =
  fiberResolves wanted provider fiber
activeToUnloadingResolution @{nameEq} @{keyEq} wanted provider
  fiber@(MkFiber component parent retired table (Active accumulator view)) Refl =
    fiberResolvedProviderSetRuntimeSameCommitted nameEq keyEq wanted provider
      fiber (fiberTable fiber) (Unloading accumulator view Nothing) view Refl Refl

0 retireResolution : DecEq name => DecEq key =>
  (wanted : key) -> (provider : name) ->
  (fiber : Fiber name key value world error) ->
  fiberResolves wanted provider (retireFiber fiber) =
  fiberResolves wanted provider fiber
retireResolution @{nameEq} @{keyEq} wanted provider fiber =
  trans (fiberResolvesWithMatches nameEq keyEq wanted provider (retireFiber fiber))
    (trans (fiberResolvedProviderRetireFrame nameEq keyEq wanted provider fiber)
      (sym (fiberResolvesWithMatches nameEq keyEq wanted provider fiber)))

0 resolvedProviderForeignAction :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (consumer : name) -> (wanted : key) -> (provider : name) ->
  (action : Action name key value world error) ->
  (source, target : SystemState name key value world error) ->
  (tag : RuleTag) -> Not (consumer = actionOwner action) ->
  applyAction @{nameEq} @{keyEq} action source = Just (tag, target) ->
  resolvedProviderAt @{nameEq} @{keyEq} consumer wanted provider target =
  resolvedProviderAt @{nameEq} @{keyEq} consumer wanted provider source
resolvedProviderForeignAction nameEq keyEq consumer wanted provider action source target
  tag distinct raw =
  let local = applyActionLocalUpdate nameEq keyEq action source target tag raw
      lookupFrame = systemLocalUpdateForeign nameEq consumer (actionOwner action)
        distinct source target local
  in trans (resolvedAtLookupEquation nameEq keyEq consumer wanted provider target)
    (trans (cong (resolvedMaybeFiberWith nameEq keyEq wanted provider) lookupFrame)
      (sym (resolvedAtLookupEquation nameEq keyEq consumer wanted provider source)))

0 resolvedAtFoundCore :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (consumer : name) -> (wanted : key) -> (provider : name) ->
  (state : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} consumer (registry state) = Just fiber ->
  resolvedProviderAt @{nameEq} @{keyEq} consumer wanted provider state =
    fiberResolvesWith nameEq keyEq wanted provider fiber
resolvedAtFoundCore nameEq keyEq consumer wanted provider state fiber found =
  trans (resolvedAtLookupEquation nameEq keyEq consumer wanted provider state)
    (cong (resolvedMaybeFiberWith nameEq keyEq wanted provider) found)

0 resolvedAfterReplaceStable :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (consumer : name) -> (wanted : key) -> (provider : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (sourceFiber, targetFiberValue : Fiber name key value world error) ->
  (found : lookupFiber @{nameEq} consumer fibers = Just sourceFiber) ->
  fiberResolvesWith nameEq keyEq wanted provider targetFiberValue =
    fiberResolvesWith nameEq keyEq wanted provider sourceFiber ->
  resolvedProviderAt @{nameEq} @{keyEq} consumer wanted provider
    (the (SystemState name key value world error)
      (MkSystemState ambient
        (replaceBinding @{nameEq} consumer targetFiberValue fibers))) =
  resolvedProviderAt @{nameEq} @{keyEq} consumer wanted provider
    (the (SystemState name key value world error)
      (MkSystemState ambient fibers))
resolvedAfterReplaceStable nameEq keyEq consumer wanted provider ambient fibers
  sourceFiber targetFiberValue found stable =
  trans (resolvedAtAfterReplace nameEq keyEq consumer wanted provider sourceFiber
    targetFiberValue fibers ambient found)
    (trans stable (sym (resolvedAtFoundCore nameEq keyEq consumer wanted provider
      (MkSystemState ambient fibers) sourceFiber found)))

0 falseAndTrueImpossible : observed = False -> observed = True -> result
falseAndTrueImpossible Refl Refl impossible

record StaticSelectedReplacement
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (selected : name)
  (before, afterState : SystemState name key value world error) where
  constructor MkStaticSelectedReplacement
  oldSelectedFiber : Fiber name key value world error
  newSelectedFiber : Fiber name key value world error
  oldSelectedFound : lookupFiber @{nameEq} selected (registry before) =
    Just oldSelectedFiber
  newSelectedFound : lookupFiber @{nameEq} selected (registry afterState) =
    Just newSelectedFiber
  selectedComponentStable : fiberComponent newSelectedFiber =
    fiberComponent oldSelectedFiber

0 installedLocalUpdateStaticReplacement :
  (nameEq : DecEq name) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  SystemLocalUpdate name key world error value nameEq selected before afterState ->
  installedAt @{nameEq} selected before = True ->
  installedAt @{nameEq} selected afterState = True ->
  StaticSelectedReplacement name key world error value nameEq selected before
    afterState
installedLocalUpdateStaticReplacement {name} {key} {world} {error} {value}
  nameEq selected before@(MkSystemState ambient fibers)
  afterState@(MkSystemState afterAmbient afterFibers) update sourceInstalled
  targetInstalled
  with (systemRegistryUpdate update)
  installedLocalUpdateStaticReplacement {name} {key} {world} {error} {value}
    nameEq selected before@(MkSystemState ambient fibers)
    afterState@(MkSystemState afterAmbient
      (insertBinding @{nameEq} selected fiber fibers absent)) update sourceInstalled
    targetInstalled | LocalInsert fiber absent = falseAndTrueImpossible
      (installedAtMissing nameEq selected (MkSystemState ambient fibers)
        (lookupFiber @{nameEq} selected fibers) Refl absent)
      sourceInstalled
  installedLocalUpdateStaticReplacement {name} {key} {world} {error} {value}
    nameEq selected before@(MkSystemState ambient fibers)
    afterState@(MkSystemState afterAmbient
      (replaceBinding @{nameEq} selected targetFiberValue fibers)) update
    sourceInstalled targetInstalled |
    LocalReplace {oldFiber} @{oldFound} @{staticComponent} targetFiberValue =
      MkStaticSelectedReplacement oldFiber targetFiberValue oldFound
        (lookupReplacedFiber selected oldFiber targetFiberValue
          fibers oldFound) staticComponent
  installedLocalUpdateStaticReplacement {name} {key} {world} {error} {value}
    nameEq selected before@(MkSystemState ambient fibers)
    afterState@(MkSystemState afterAmbient
      (deleteBinding @{nameEq} selected fibers)) update sourceInstalled
    targetInstalled | LocalDelete = falseAndTrueImpossible
      (trans (installedAtLookupEquation nameEq selected
        (MkSystemState afterAmbient (deleteBinding @{nameEq} selected fibers)))
        (cong (installedMaybe {name = name} {key = key} {world = world}
          {error = error} {value = value})
          (lookupDeleteSelf selected fibers)))
      targetInstalled

0 installedFiberWitness :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  installedAt @{nameEq} selected state = True ->
  (fiber : Fiber name key value world error **
    lookupFiber @{nameEq} selected (registry state) = Just fiber)
installedFiberWitness nameEq selected state installedTrue
  with (lookupFiber @{nameEq} selected (registry state)) proof found
  installedFiberWitness nameEq selected state installedTrue | Nothing =
    absurd installedTrue
  installedFiberWitness nameEq selected state installedTrue | Just fiber =
    (fiber ** Refl)

0 installedCheckedStepStaticReplacement :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  installedAt @{nameEq} selected before = True ->
  installedAt @{nameEq} selected afterState = True ->
  StaticSelectedReplacement name key world error value nameEq selected before
    afterState
installedCheckedStepStaticReplacement nameEq keyEq selected action tag before
  afterState checkedEquation sourceInstalled targetInstalled
  with (decEq @{nameEq} selected (actionOwner action))
  installedCheckedStepStaticReplacement nameEq keyEq selected action tag before
    afterState checkedEquation sourceInstalled targetInstalled | No distinct =
      case installedFiberWitness nameEq selected before sourceInstalled of
        (fiber ** sourceFound) =>
          let raw = checkedActionProjects nameEq keyEq action before afterState tag
                checkedEquation
              update = applyActionLocalUpdate nameEq keyEq action before afterState
                tag raw
              targetFound = trans
                (systemLocalUpdateForeign nameEq selected (actionOwner action)
                  distinct before afterState update) sourceFound
          in MkStaticSelectedReplacement fiber fiber sourceFound targetFound Refl
  installedCheckedStepStaticReplacement nameEq keyEq selected action tag before
    afterState checkedEquation sourceInstalled targetInstalled | Yes same =
      let raw = checkedActionProjects nameEq keyEq action before afterState tag
            checkedEquation
          update = applyActionLocalUpdate nameEq keyEq action before afterState tag raw
      in case same of
        Refl => installedLocalUpdateStaticReplacement nameEq selected before afterState
          update sourceInstalled targetInstalled

0 cp3JustInjective : Just left = Just right -> left = right
cp3JustInjective Refl = Refl

0 viewProvidersInjective :
  (left, right : View name deps) -> viewProviders left = viewProviders right ->
  left = right
viewProvidersInjective EmptyView EmptyView Refl = Refl
viewProvidersInjective (ProviderView left leftRest)
  (ProviderView right rightRest) equation =
  case consInjective equation of
    (headEqual, tailEqual) => case headEqual of
      Refl => cong (ProviderView right)
        (viewProvidersInjective leftRest rightRest tailEqual)

0 snapshotComponentStable :
  (sourceSnapshot : CommittedSnapshot name key world error value nameEq selected
    providers before) ->
  (targetSnapshot : CommittedSnapshot name key world error value nameEq selected
    providers afterState) ->
  (replacement : StaticSelectedReplacement name key world error value nameEq
    selected before afterState) ->
  fiberComponent (committedFiber targetSnapshot) =
    fiberComponent (committedFiber sourceSnapshot)
snapshotComponentStable sourceSnapshot targetSnapshot replacement =
  let oldEqual = cp3JustInjective (trans (sym (oldSelectedFound replacement))
        (committedLookup sourceSnapshot))
      newEqual = cp3JustInjective (trans (sym (newSelectedFound replacement))
        (committedLookup targetSnapshot))
  in trans (cong fiberComponent (sym newEqual))
    (trans (selectedComponentStable replacement)
      (cong fiberComponent oldEqual))

0 resolvedViewStableAcrossComponents :
  (wanted : key) -> (provider : name) ->
  (targetComponent, sourceComponent : Component key value world error) ->
  (componentStable : targetComponent = sourceComponent) ->
  (targetView : View name
    (dependencies (componentDependencies targetComponent))) ->
  (sourceView : View name
    (dependencies (componentDependencies sourceComponent))) ->
  viewProviders targetView = viewProviders sourceView ->
  viewLookup @{keyEq} wanted
    (dependencies (componentDependencies sourceComponent)) sourceView =
    Just provider ->
  viewLookup @{keyEq} wanted
    (dependencies (componentDependencies targetComponent)) targetView =
    Just provider
resolvedViewStableAcrossComponents wanted provider component component Refl
  targetView sourceView providersEqual sourceResolved =
    rewrite viewProvidersInjective targetView sourceView providersEqual in
      sourceResolved

0 snapshotResolvedLookupStable :
  (wanted : key) -> (provider : name) ->
  (sourceSnapshot : CommittedSnapshot name key world error value nameEq selected
    providers before) ->
  (targetSnapshot : CommittedSnapshot name key world error value nameEq selected
    providers afterState) ->
  fiberComponent (committedFiber targetSnapshot) =
    fiberComponent (committedFiber sourceSnapshot) ->
  viewLookup @{keyEq} wanted
    (dependencies (componentDependencies
      (fiberComponent (committedFiber sourceSnapshot))))
    (committedView sourceSnapshot) = Just provider ->
  viewLookup @{keyEq} wanted
    (dependencies (componentDependencies
      (fiberComponent (committedFiber targetSnapshot))))
    (committedView targetSnapshot) = Just provider
snapshotResolvedLookupStable wanted provider sourceSnapshot targetSnapshot
  componentStable sourceResolved =
  resolvedViewStableAcrossComponents wanted provider
    (fiberComponent (committedFiber targetSnapshot))
    (fiberComponent (committedFiber sourceSnapshot)) componentStable
    (committedView targetSnapshot) (committedView sourceSnapshot)
    (trans (committedProviderNames targetSnapshot)
      (sym (committedProviderNames sourceSnapshot))) sourceResolved

public export
record ResolvedConsumerSnapshotData
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (consumer : name) (wanted : key) (provider : name)
  (state : SystemState name key value world error) where
  constructor MkResolvedConsumerSnapshotData
  resolvedProviders : List name
  resolvedConsumerSnapshot : CommittedSnapshot name key world error value nameEq
    consumer resolvedProviders state
  snapshotKeyResolved : viewLookup @{keyEq} wanted
    (dependencies (componentDependencies
      (fiberComponent (committedFiber resolvedConsumerSnapshot))))
    (committedView resolvedConsumerSnapshot) = Just provider

public export
0 resolvedConsumerSnapshotData :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (consumer : name) -> (wanted : key) -> (provider : name) ->
  (state : SystemState name key value world error) ->
  resolvedProviderAt @{nameEq} @{keyEq} consumer wanted provider state = True ->
  ResolvedConsumerSnapshotData name key world error value nameEq keyEq consumer
    wanted provider state
resolvedConsumerSnapshotData nameEq keyEq consumer wanted provider
  (MkSystemState ambient fibers) resolved
  with (lookupFiber @{nameEq} consumer fibers) proof consumerFound
  resolvedConsumerSnapshotData nameEq keyEq consumer wanted provider
    (MkSystemState ambient fibers) resolved | Nothing = absurd resolved
  resolvedConsumerSnapshotData nameEq keyEq consumer wanted provider
    (MkSystemState ambient fibers) resolved |
    Just (MkFiber component parent retired table (Inactive outcome)) =
      absurd resolved
  resolvedConsumerSnapshotData nameEq keyEq consumer wanted provider
    (MkSystemState ambient fibers) resolved |
    Just fiber@(MkFiber component parent retired table
      (Reloading remaining accumulator view))
    with (viewLookup @{keyEq} wanted
      (dependencies (componentDependencies component)) view) proof selectedProvider
    resolvedConsumerSnapshotData nameEq keyEq consumer wanted provider
      (MkSystemState ambient fibers) resolved |
      Just fiber@(MkFiber component parent retired table
        (Reloading remaining accumulator view)) | Nothing = absurd resolved
    resolvedConsumerSnapshotData nameEq keyEq consumer wanted provider
      (MkSystemState ambient fibers) resolved |
      Just fiber@(MkFiber component parent retired table
        (Reloading remaining accumulator view)) | Just actual
      with (decEq @{nameEq} actual provider)
      resolvedConsumerSnapshotData nameEq keyEq consumer wanted provider
        (MkSystemState ambient fibers) resolved |
        Just fiber@(MkFiber component parent retired table
          (Reloading remaining accumulator view)) | Just actual | Yes equal =
          case equal of
            Refl => MkResolvedConsumerSnapshotData (viewProviders view)
              (MkCommittedSnapshot
                (MkFiber component parent retired table
                  (Reloading remaining accumulator view)) consumerFound view Refl Refl)
              selectedProvider
      resolvedConsumerSnapshotData nameEq keyEq consumer wanted provider
        (MkSystemState ambient fibers) resolved |
        Just fiber@(MkFiber component parent retired table
          (Reloading remaining accumulator view)) | Just actual | No distinct =
            absurd resolved
  resolvedConsumerSnapshotData nameEq keyEq consumer wanted provider
    (MkSystemState ambient fibers) resolved |
    Just fiber@(MkFiber component parent retired table (Active accumulator view))
    with (viewLookup @{keyEq} wanted
      (dependencies (componentDependencies component)) view) proof selectedProvider
    resolvedConsumerSnapshotData nameEq keyEq consumer wanted provider
      (MkSystemState ambient fibers) resolved |
      Just fiber@(MkFiber component parent retired table (Active accumulator view)) |
      Nothing = absurd resolved
    resolvedConsumerSnapshotData nameEq keyEq consumer wanted provider
      (MkSystemState ambient fibers) resolved |
      Just fiber@(MkFiber component parent retired table (Active accumulator view)) |
      Just actual with (decEq @{nameEq} actual provider)
      resolvedConsumerSnapshotData nameEq keyEq consumer wanted provider
        (MkSystemState ambient fibers) resolved |
        Just fiber@(MkFiber component parent retired table (Active accumulator view)) |
        Just actual | Yes equal = case equal of
          Refl => MkResolvedConsumerSnapshotData (viewProviders view)
            (MkCommittedSnapshot
              (MkFiber component parent retired table (Active accumulator view))
              consumerFound view Refl Refl) selectedProvider
      resolvedConsumerSnapshotData nameEq keyEq consumer wanted provider
        (MkSystemState ambient fibers) resolved |
        Just fiber@(MkFiber component parent retired table (Active accumulator view)) |
        Just actual | No distinct = absurd resolved
  resolvedConsumerSnapshotData nameEq keyEq consumer wanted provider
    (MkSystemState ambient fibers) resolved |
    Just fiber@(MkFiber component parent retired table
      (Unloading accumulator view outcome))
    with (viewLookup @{keyEq} wanted
      (dependencies (componentDependencies component)) view) proof selectedProvider
    resolvedConsumerSnapshotData nameEq keyEq consumer wanted provider
      (MkSystemState ambient fibers) resolved |
      Just fiber@(MkFiber component parent retired table
        (Unloading accumulator view outcome)) | Nothing = absurd resolved
    resolvedConsumerSnapshotData nameEq keyEq consumer wanted provider
      (MkSystemState ambient fibers) resolved |
      Just fiber@(MkFiber component parent retired table
        (Unloading accumulator view outcome)) | Just actual
      with (decEq @{nameEq} actual provider)
      resolvedConsumerSnapshotData nameEq keyEq consumer wanted provider
        (MkSystemState ambient fibers) resolved |
        Just fiber@(MkFiber component parent retired table
          (Unloading accumulator view outcome)) | Just actual | Yes equal =
          case equal of
            Refl => MkResolvedConsumerSnapshotData (viewProviders view)
              (MkCommittedSnapshot
                (MkFiber component parent retired table
                  (Unloading accumulator view outcome)) consumerFound view Refl Refl)
              selectedProvider
      resolvedConsumerSnapshotData nameEq keyEq consumer wanted provider
        (MkSystemState ambient fibers) resolved |
        Just fiber@(MkFiber component parent retired table
          (Unloading accumulator view outcome)) | Just actual | No distinct =
            absurd resolved

0 snapshotResolvedProviderAt :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (consumer : name) -> (wanted : key) -> (provider : name) ->
  (snapshot : CommittedSnapshot name key world error value nameEq consumer
    providers state) ->
  viewLookup @{keyEq} wanted
    (dependencies (componentDependencies
      (fiberComponent (committedFiber snapshot))))
    (committedView snapshot) = Just provider ->
  resolvedProviderAt @{nameEq} @{keyEq} consumer wanted provider state = True
snapshotResolvedProviderAt nameEq keyEq consumer wanted provider
  (MkCommittedSnapshot
    (MkFiber component parent retired table lifecycle) found view committedView
      providerNames) resolved =
  rewrite found in
  rewrite committedView in
  rewrite resolved in
    sameName
  where
    sameName : (case decEq @{nameEq} provider provider of
      Yes Refl => True
      No _ => False) = True
    sameName with (decEq @{nameEq} provider provider)
      sameName | Yes Refl = Refl
      sameName | No distinct = absurd (distinct Refl)

public export
0 resolvedConstantInstalledTrace :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (consumer : name) -> (wanted : key) -> (provider : name) ->
  (providers : List name) ->
  (transitions : Transitions start finalState) ->
  (installedTrace : InstalledTrace name key world error value nameEq keyEq
    consumer transitions) ->
  (snapshot : CommittedSnapshot name key world error value nameEq consumer
    providers start) ->
  (resolved : viewLookup @{keyEq} wanted
    (dependencies (componentDependencies
      (fiberComponent (committedFiber snapshot))))
    (committedView snapshot) = Just provider) ->
  ConsumerResolutionConstant name key world error value nameEq keyEq consumer
    wanted provider transitions
resolvedConstantInstalledTrace nameEq keyEq consumer wanted provider providers
  NoTransitions (InstalledEnd installed) snapshot resolved =
    ResolutionConstantEnd
      (snapshotResolvedProviderAt nameEq keyEq consumer wanted provider snapshot
        resolved)
resolvedConstantInstalledTrace nameEq keyEq consumer wanted provider providers
  (MoreTransitions transition@(Fired nameEq keyEq action tag checkedEquation) rest)
  (InstalledStep action tag checkedEquation rest sourceInstalled tail) snapshot
  resolved =
    let raw = checkedActionProjects nameEq keyEq action _ _ tag checkedEquation
        targetInstalled = installedTraceStart tail
        afterCommitted = case decEq @{nameEq} consumer (actionOwner action) of
          No distinct => committedProvidersForeignAction nameEq keyEq consumer
            providers action _ _ tag distinct (committedSnapshotEquation snapshot)
            raw
          Yes same => committedProvidersSelectedAction nameEq keyEq consumer providers
            action _ _ tag (sym same) snapshot targetInstalled raw
        targetSnapshot = committedSnapshotFrom nameEq consumer providers _
          afterCommitted
        replacement = installedCheckedStepStaticReplacement nameEq keyEq consumer
          action tag _ _ checkedEquation sourceInstalled targetInstalled
        componentStable = snapshotComponentStable snapshot targetSnapshot replacement
        targetResolved = snapshotResolvedLookupStable wanted provider snapshot
          targetSnapshot componentStable resolved
        sourceResolved = snapshotResolvedProviderAt nameEq keyEq consumer wanted
          provider snapshot resolved
    in ResolutionConstantStep transition rest sourceResolved
      (resolvedConstantInstalledTrace nameEq keyEq consumer wanted provider providers
        rest tail targetSnapshot targetResolved)

0 viewLookupImpliesContains :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (deps : List key) -> (view : View name deps) ->
  (provider : name) ->
  viewLookup @{keyEq} wanted deps view = Just provider ->
  viewContains @{nameEq} provider view = True
viewLookupImpliesContains nameEq keyEq wanted [] EmptyView provider found =
  case found of Refl impossible
viewLookupImpliesContains nameEq keyEq wanted (current :: rest)
  (ProviderView currentProvider viewTail) provider found
  with (decEq @{keyEq} wanted current)
  viewLookupImpliesContains nameEq keyEq current (current :: rest)
    (ProviderView currentProvider viewTail) provider found | Yes Refl =
      case cp3JustInjective found of
        Refl => sameProvider
    where
      sameProvider : viewContains @{nameEq} currentProvider
        (ProviderView currentProvider viewTail) = True
      sameProvider with (decEq @{nameEq} currentProvider currentProvider)
        sameProvider | Yes Refl = Refl
        sameProvider | No distinct = absurd (distinct Refl)
  viewLookupImpliesContains nameEq keyEq wanted (current :: rest)
    (ProviderView currentProvider viewTail) provider found | No wantedDistinct
    with (decEq @{nameEq} provider currentProvider)
    viewLookupImpliesContains nameEq keyEq wanted (current :: rest)
      (ProviderView provider viewTail) provider found | No wantedDistinct | Yes Refl = Refl
    viewLookupImpliesContains nameEq keyEq wanted (current :: rest)
      (ProviderView currentProvider viewTail) provider found | No wantedDistinct |
      No providerDistinct = viewLookupImpliesContains nameEq keyEq wanted rest viewTail
        provider found

0 reliedHeadFromCommittedView :
  (nameEq : DecEq name) -> (provider, consumer : name) ->
  Not (consumer = provider) ->
  (fiber : Fiber name key value world error) ->
  (view : View name (dependencies
    (componentDependencies (fiberComponent fiber)))) ->
  committed (fiberLifecycle fiber) = Just view ->
  viewContains @{nameEq} provider view = True ->
  reliedHead @{nameEq} provider provider (Bind consumer fiber) = True
reliedHeadFromCommittedView nameEq provider consumer distinct
  (MkFiber component parent retiredFlag table (Inactive outcome)) view committedView
  contains = case committedView of Refl impossible
reliedHeadFromCommittedView nameEq provider consumer distinct
  (MkFiber component parent retiredFlag table
    (Reloading remaining accumulator actualView)) view committedView contains =
  different (trans (cong (viewContains @{nameEq} provider)
    (cp3JustInjective committedView)) contains)
  where
    different : viewContains @{nameEq} provider actualView = True ->
      reliedHead @{nameEq} provider provider
        (Bind consumer (MkFiber component parent retiredFlag table
          (Reloading remaining accumulator actualView))) = True
    different actualContains with (decEq @{nameEq} consumer provider)
      different actualContains | Yes equal = case equal of
        Refl => absurd (distinct Refl)
      different actualContains | No _ = rewrite actualContains in Refl
reliedHeadFromCommittedView nameEq provider consumer distinct
  (MkFiber component parent retiredFlag table (Active accumulator actualView))
  view committedView contains =
  different (trans (cong (viewContains @{nameEq} provider)
    (cp3JustInjective committedView)) contains)
  where
    different : viewContains @{nameEq} provider actualView = True ->
      reliedHead @{nameEq} provider provider
        (Bind consumer (MkFiber component parent retiredFlag table
          (Active accumulator actualView))) = True
    different actualContains with (decEq @{nameEq} consumer provider)
      different actualContains | Yes equal = case equal of
        Refl => absurd (distinct Refl)
      different actualContains | No _ = rewrite actualContains in Refl
reliedHeadFromCommittedView nameEq provider consumer distinct
  (MkFiber component parent retiredFlag table
    (Unloading accumulator actualView outcome)) view committedView contains =
  different (trans (cong (viewContains @{nameEq} provider)
    (cp3JustInjective committedView)) contains)
  where
    different : viewContains @{nameEq} provider actualView = True ->
      reliedHead @{nameEq} provider provider
        (Bind consumer (MkFiber component parent retiredFlag table
          (Unloading accumulator actualView outcome))) = True
    different actualContains with (decEq @{nameEq} consumer provider)
      different actualContains | Yes equal = case equal of
        Refl => absurd (distinct Refl)
      different actualContains | No _ = rewrite actualContains in Refl


0 resolvedConsumerSnapshotRelied :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {providers : List name} ->
  {state : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (consumer, provider : name) -> Not (consumer = provider) -> (wanted : key) ->
  (snapshot : CommittedSnapshot name key world error value nameEq consumer
    providers state) ->
  viewLookup @{keyEq} wanted
    (dependencies (componentDependencies
      (fiberComponent (committedFiber snapshot))))
    (committedView snapshot) = Just provider ->
  relied @{nameEq} {key = key} {value = value} {world = world} {error = error} provider (registry state) = True
resolvedConsumerSnapshotRelied nameEq keyEq consumer provider distinct wanted
  snapshot resolved =
  let contains = viewLookupImpliesContains nameEq keyEq wanted
        (dependencies (componentDependencies
          (fiberComponent (committedFiber snapshot))))
        (committedView snapshot) provider resolved
      headTrue = reliedHeadFromCommittedView nameEq provider consumer distinct
        (committedFiber snapshot) (committedView snapshot)
        (committedLifecycle snapshot) contains
      entriesFound = lookupFiberEntries nameEq consumer (committedFiber snapshot)
        (registry state) (committedLookup snapshot)
  in reliedOnByLookupTrue nameEq provider consumer (committedFiber snapshot)
    (registry state) (committedLookup snapshot) headTrue

public export
record StableProviderValue
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (provider : name) (wanted : key) (provided : value wanted)
  (state : SystemState name key value world error) where
  constructor MkStableProviderValue
  stableValueFiber : Fiber name key value world error
  stableValueFound : lookupFiber @{nameEq} provider (registry state) =
    Just stableValueFiber
  stableValueLifecycle : stableProvider (fiberLifecycle stableValueFiber) = True
  stableValuePresent : providerValueAt @{nameEq} @{keyEq} provider wanted state =
    Just provided

fiberValueMaybeWith : (keyEq : DecEq key) -> (wanted : key) ->
  Maybe (Fiber name key value world error) -> Maybe (value wanted)
fiberValueMaybeWith keyEq wanted Nothing = Nothing
fiberValueMaybeWith keyEq wanted (Just fiber) =
  lookupBinding @{keyEq} wanted (ownedValues (fiberTable fiber))

0 providerValueAtLookupEquation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider : name) -> (wanted : key) ->
  (state : SystemState name key value world error) ->
  providerValueAt @{nameEq} @{keyEq} provider wanted state =
    fiberValueMaybeWith {value = value} {world = world} {error = error}
      keyEq wanted (lookupFiber @{nameEq} provider (registry state))
providerValueAtLookupEquation nameEq keyEq provider wanted
  state@(MkSystemState ambient fibers)
  with (lookupFiber @{nameEq} provider fibers)
  providerValueAtLookupEquation nameEq keyEq provider wanted
    state@(MkSystemState ambient fibers) | Nothing = Refl
  providerValueAtLookupEquation nameEq keyEq provider wanted
    state@(MkSystemState ambient fibers) |
    Just (MkFiber component parent retired table lifecycle)
    with (lookupBinding @{keyEq} wanted (ownedValues table))
    providerValueAtLookupEquation nameEq keyEq provider wanted
      state@(MkSystemState ambient fibers) |
      Just (MkFiber component parent retired table lifecycle) | Nothing = Refl
    providerValueAtLookupEquation nameEq keyEq provider wanted
      state@(MkSystemState ambient fibers) |
      Just (MkFiber component parent retired table lifecycle) | Just found = Refl

0 providerValueAtFoundCore :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider : name) -> (wanted : key) ->
  (state : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} provider (registry state) = Just fiber ->
  providerValueAt @{nameEq} @{keyEq} provider wanted state =
    fiberValueMaybeWith keyEq wanted (Just fiber)
providerValueAtFoundCore nameEq keyEq provider wanted state fiber found =
  trans (providerValueAtLookupEquation nameEq keyEq provider wanted state)
    (cong (fiberValueMaybeWith keyEq wanted) found)

0 providerValueForeignAction :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider : name) -> (wanted : key) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) -> Not (provider = actionOwner action) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  providerValueAt @{nameEq} @{keyEq} provider wanted afterState =
  providerValueAt @{nameEq} @{keyEq} provider wanted before
providerValueForeignAction nameEq keyEq provider wanted action before afterState
  tag distinct raw =
  let update = applyActionLocalUpdate nameEq keyEq action before afterState tag raw
      lookupFrame = systemLocalUpdateForeign nameEq provider (actionOwner action)
        distinct before afterState update
  in trans (providerValueAtLookupEquation nameEq keyEq provider wanted afterState)
    (trans (cong (fiberValueMaybeWith keyEq wanted) lookupFrame)
      (sym (providerValueAtLookupEquation nameEq keyEq provider wanted before)))

0 stableProviderValueForeign :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider : name) -> (wanted : key) -> (provided : value wanted) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) -> Not (provider = actionOwner action) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  StableProviderValue name key world error value nameEq keyEq provider wanted
    provided before ->
  StableProviderValue name key world error value nameEq keyEq provider wanted
    provided afterState
stableProviderValueForeign nameEq keyEq provider wanted provided action before
  afterState tag distinct raw snapshot =
  let update = applyActionLocalUpdate nameEq keyEq action before afterState tag raw
      targetFound = trans (systemLocalUpdateForeign nameEq provider
        (actionOwner action) distinct before afterState update)
        (stableValueFound snapshot)
      targetValue = trans (providerValueForeignAction nameEq keyEq provider wanted
        action before afterState tag distinct raw) (stableValuePresent snapshot)
  in MkStableProviderValue (stableValueFiber snapshot) targetFound
    (stableValueLifecycle snapshot) targetValue

0 retireStableProvider :
  (fiber : Fiber name key value world error) ->
  stableProvider (fiberLifecycle fiber) = True ->
  stableProvider (fiberLifecycle (retireFiber fiber)) = True
retireStableProvider
  fiber@(MkFiber component parent retiredFlag table lifecycle) stable =
  let targetExact = cong (\observed => stableProvider (fiberLifecycle observed))
        (retireFiberExact component parent retiredFlag table lifecycle)
      targetObserved = fiberStableProviderObservation component parent True table
        lifecycle
      sourceObserved = fiberStableProviderObservation component parent retiredFlag
        table lifecycle
      lifecycleStable = trans (sym sourceObserved) stable
  in trans targetExact (trans targetObserved lifecycleStable)

0 successfulORetireTarget :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider : name) -> (fiber : Fiber name key value world error) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  lookupFiber @{nameEq} provider fibers = Just fiber ->
  applyAction @{nameEq} @{keyEq} (ORetire provider)
    (MkSystemState ambient fibers) = Just (tag, afterState) ->
  afterState = MkSystemState ambient
    (replaceBinding @{nameEq} provider (retireFiber fiber) fibers)
successfulORetireTarget nameEq keyEq provider fiber ambient fibers afterState tag
  found raw with (lookupFiber @{nameEq} provider fibers) proof observed
  successfulORetireTarget nameEq keyEq provider fiber ambient fibers afterState tag
    found raw | Nothing = case found of Refl impossible
  successfulORetireTarget nameEq keyEq provider fiber ambient fibers afterState tag
    found raw | Just actual = case cp3JustInjective found of
      Refl => case cp3JustInjective raw of Refl => Refl

0 stableProviderValueRetire :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider : name) -> (wanted : key) -> (provided : value wanted) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (ORetire provider) before =
    Just (tag, afterState) ->
  StableProviderValue name key world error value nameEq keyEq provider wanted
    provided before ->
  StableProviderValue name key world error value nameEq keyEq provider wanted
    provided afterState
stableProviderValueRetire nameEq keyEq provider wanted provided
  before@(MkSystemState ambient fibers) afterState tag raw
  (MkStableProviderValue fiber found stable present) =
  case successfulORetireTarget nameEq keyEq provider fiber ambient fibers
    afterState tag found raw of
      Refl => MkStableProviderValue (retireFiber fiber)
        (lookupReplacedFiber provider fiber (retireFiber fiber) fibers found)
        (retireStableProvider fiber stable)
        (trans (valueFromProviderRetireRegistry nameEq keyEq provider wanted
          provider fiber fibers found) present)


0 lLeaveProviderValueStable :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (provider : name) ->
  (wanted : key) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LLeave provider) before =
    Just (tag, afterState) ->
  providerValueAt @{nameEq} @{keyEq} provider wanted afterState =
  providerValueAt @{nameEq} @{keyEq} provider wanted before
lLeaveProviderValueStable nameEq keyEq provider wanted
  before@(MkSystemState ambient fibers) afterState tag raw
  with (lookupFiber @{nameEq} provider fibers) proof found
  lLeaveProviderValueStable nameEq keyEq provider wanted
    before@(MkSystemState ambient fibers) afterState tag raw | Nothing =
      void (nothingIsNotJust raw)
  lLeaveProviderValueStable nameEq keyEq provider wanted
    before@(MkSystemState ambient fibers) afterState tag raw | Just fiber
    with (fiberLifecycle fiber) proof life
    lLeaveProviderValueStable nameEq keyEq provider wanted
      before@(MkSystemState ambient fibers) afterState tag raw | Just fiber |
      Inactive outcome = void (nothingIsNotJust raw)
    lLeaveProviderValueStable nameEq keyEq provider wanted
      before@(MkSystemState ambient fibers) afterState tag raw | Just fiber |
      Reloading remaining accumulator view = void (nothingIsNotJust raw)
    lLeaveProviderValueStable nameEq keyEq provider wanted
      before@(MkSystemState ambient fibers) afterState tag raw | Just fiber |
      Unloading accumulator view outcome = void (nothingIsNotJust raw)
    lLeaveProviderValueStable nameEq keyEq provider wanted
      before@(MkSystemState ambient fibers) afterState tag raw | Just fiber |
      Active accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} fiber fibers) view)
      lLeaveProviderValueStable nameEq keyEq provider wanted
        before@(MkSystemState ambient fibers) afterState tag raw | Just fiber |
        Active accumulator view | True = void (nothingIsNotJust raw)
      lLeaveProviderValueStable nameEq keyEq provider wanted
        before@(MkSystemState ambient fibers) afterState tag raw | Just
        fiber@(MkFiber component parent retiredFlag table lifecycle) |
        Active accumulator view | False =
          case trans (sym (fiberLifecycleObservation component parent retiredFlag
            table lifecycle)) life of
            Refl => case cp3JustInjective raw of
              Refl => rewrite setFiberLifecycleExact component parent retiredFlag
                table (Active accumulator view)
                (Unloading accumulator view Nothing) in
                trans (valueFromProviderActiveUnload nameEq keyEq provider wanted provider
                  component parent retiredFlag table accumulator view fibers found)
                  (providerValueAtFoundCore nameEq keyEq provider wanted
                    (MkSystemState ambient fibers)
                    (MkFiber component parent retiredFlag table
                      (Active accumulator view)) found)

public export
0 stableValueInstalled :
  (nameEq : DecEq name) ->
  (snapshot : StableProviderValue name key world error value nameEq keyEq
    provider wanted provided state) ->
  installedAt @{nameEq} provider state = True
stableValueInstalled nameEq snapshot =
  trans (installedAtFound nameEq _ _ (stableValueFiber snapshot)
    (stableValueFound snapshot))
    (stableProviderImpliesInstalled (fiberLifecycle (stableValueFiber snapshot))
      (stableValueLifecycle snapshot))

0 lAdvanceSourceReloading :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (provider : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LAdvance provider) before =
    Just (tag, afterState) ->
  reloadingAt @{nameEq} provider before = True
lAdvanceSourceReloading nameEq keyEq provider
  before@(MkSystemState ambient fibers) afterState tag raw
  with (lookupFiber @{nameEq} provider fibers)
  lAdvanceSourceReloading nameEq keyEq provider
    before@(MkSystemState ambient fibers) afterState tag raw | Nothing =
      void (nothingIsNotJust raw)
  lAdvanceSourceReloading nameEq keyEq provider
    before@(MkSystemState ambient fibers) afterState tag raw | Just fiber
    with (fiberLifecycle fiber)
    lAdvanceSourceReloading nameEq keyEq provider
      before@(MkSystemState ambient fibers) afterState tag raw | Just fiber |
      Inactive outcome = void (nothingIsNotJust raw)
    lAdvanceSourceReloading nameEq keyEq provider
      before@(MkSystemState ambient fibers) afterState tag raw | Just fiber |
      Reloading remaining accumulator view = Refl
    lAdvanceSourceReloading nameEq keyEq provider
      before@(MkSystemState ambient fibers) afterState tag raw | Just fiber |
      Active accumulator view = void (nothingIsNotJust raw)
    lAdvanceSourceReloading nameEq keyEq provider
      before@(MkSystemState ambient fibers) afterState tag raw | Just fiber |
      Unloading accumulator view outcome = void (nothingIsNotJust raw)

0 lDivertSourceReloading :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (provider : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LDivert provider) before =
    Just (tag, afterState) ->
  reloadingAt @{nameEq} provider before = True
lDivertSourceReloading nameEq keyEq provider
  before@(MkSystemState ambient fibers) afterState tag raw
  with (lookupFiber @{nameEq} provider fibers)
  lDivertSourceReloading nameEq keyEq provider
    before@(MkSystemState ambient fibers) afterState tag raw | Nothing =
      void (nothingIsNotJust raw)
  lDivertSourceReloading nameEq keyEq provider
    before@(MkSystemState ambient fibers) afterState tag raw | Just fiber
    with (fiberLifecycle fiber)
    lDivertSourceReloading nameEq keyEq provider
      before@(MkSystemState ambient fibers) afterState tag raw | Just fiber |
      Inactive outcome = void (nothingIsNotJust raw)
    lDivertSourceReloading nameEq keyEq provider
      before@(MkSystemState ambient fibers) afterState tag raw | Just fiber |
      Reloading remaining accumulator view = Refl
    lDivertSourceReloading nameEq keyEq provider
      before@(MkSystemState ambient fibers) afterState tag raw | Just fiber |
      Active accumulator view = void (nothingIsNotJust raw)
    lDivertSourceReloading nameEq keyEq provider
      before@(MkSystemState ambient fibers) afterState tag raw | Just fiber |
      Unloading accumulator view outcome = void (nothingIsNotJust raw)

0 stableValueNotReloading :
  (nameEq : DecEq name) -> (provider : name) ->
  (state : SystemState name key value world error) ->
  (snapshot : StableProviderValue name key world error value nameEq keyEq
    provider wanted provided state) ->
  reloadingAt @{nameEq} provider state = True -> Void
stableValueNotReloading nameEq provider state snapshot reloading
  with (lookupFiber @{nameEq} provider (registry state)) proof found
  stableValueNotReloading nameEq provider state snapshot reloading | Nothing =
    absurd reloading
  stableValueNotReloading nameEq provider state snapshot reloading |
    Just (MkFiber component parent retiredFlag table lifecycle)
    with (fiberLifecycle (MkFiber component parent retiredFlag table lifecycle)) proof life
    stableValueNotReloading nameEq provider state snapshot reloading |
      Just (MkFiber component parent retiredFlag table lifecycle) |
      Inactive outcome = absurd reloading
    stableValueNotReloading nameEq provider state snapshot reloading |
      Just (MkFiber component parent retiredFlag table lifecycle) |
      Reloading remaining accumulator view =
        let sameFiber = cp3JustInjective (trans (sym found)
              (stableValueFound snapshot))
            currentStable = trans (cong
              (\fiber => stableProvider (fiberLifecycle fiber)) sameFiber)
              (stableValueLifecycle snapshot)
        in absurd currentStable
    stableValueNotReloading nameEq provider state snapshot reloading |
      Just (MkFiber component parent retiredFlag table lifecycle) |
      Active accumulator view = absurd reloading
    stableValueNotReloading nameEq provider state snapshot reloading |
      Just (MkFiber component parent retiredFlag table lifecycle) |
      Unloading accumulator view outcome = absurd reloading

0 selectedProviderValueStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider : name) -> (wanted : key) -> (provided : value wanted) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) -> actionOwner action = provider ->
  checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  StableProviderValue name key world error value nameEq keyEq provider wanted
    provided before ->
  installedAt @{nameEq} provider afterState = True ->
  providerValueAt @{nameEq} @{keyEq} provider wanted afterState =
    providerValueAt @{nameEq} @{keyEq} provider wanted before
selectedProviderValueStep nameEq keyEq provider wanted provided
  (OInsert provider parent component) before afterState tag Refl checked snapshot
  targetInstalled =
    let raw = checkedActionProjects nameEq keyEq
          (OInsert provider parent component) before afterState tag checked
        (sourceFalse, targetFalse) = oInsertUninstalled nameEq keyEq provider parent
          component before afterState tag raw
    in falseAndTrueImpossible sourceFalse (stableValueInstalled nameEq snapshot)
selectedProviderValueStep nameEq keyEq provider wanted provided
  (ORetire provider) before afterState tag Refl checked snapshot targetInstalled =
    let raw = checkedActionProjects nameEq keyEq (ORetire provider) before
          afterState tag checked
        targetSnapshot = stableProviderValueRetire nameEq keyEq provider wanted
          provided before afterState tag raw snapshot
    in trans (stableValuePresent targetSnapshot)
      (sym (stableValuePresent snapshot))
selectedProviderValueStep nameEq keyEq provider wanted provided
  (ORemove provider) before afterState tag Refl checked snapshot targetInstalled =
    let raw = checkedActionProjects nameEq keyEq (ORemove provider) before
          afterState tag checked
        (sourceFalse, targetFalse) = oRemoveUninstalled nameEq keyEq provider before
          afterState tag raw
    in falseAndTrueImpossible sourceFalse (stableValueInstalled nameEq snapshot)
selectedProviderValueStep nameEq keyEq provider wanted provided
  (LBegin provider) before afterState tag Refl checked snapshot targetInstalled =
    case lBeginBoundary nameEq keyEq provider before afterState tag checked of
      (tagShape, sourceFalse, targetTrue) =>
        falseAndTrueImpossible sourceFalse (stableValueInstalled nameEq snapshot)
selectedProviderValueStep nameEq keyEq provider wanted provided
  (LAdvance provider) before afterState tag Refl checked snapshot targetInstalled =
    let raw = checkedActionProjects nameEq keyEq (LAdvance provider) before
          afterState tag checked
    in void (stableValueNotReloading nameEq provider before snapshot
      (lAdvanceSourceReloading nameEq keyEq provider before afterState tag raw))
selectedProviderValueStep nameEq keyEq provider wanted provided
  (LDivert provider) before afterState tag Refl checked snapshot targetInstalled =
    let raw = checkedActionProjects nameEq keyEq (LDivert provider) before
          afterState tag checked
    in void (stableValueNotReloading nameEq provider before snapshot
      (lDivertSourceReloading nameEq keyEq provider before afterState tag raw))
selectedProviderValueStep nameEq keyEq provider wanted provided
  (LLeave provider) before afterState tag Refl checked snapshot targetInstalled =
    lLeaveProviderValueStable nameEq keyEq provider wanted before afterState tag
      (checkedActionProjects nameEq keyEq (LLeave provider) before afterState tag
        checked)
selectedProviderValueStep nameEq keyEq provider wanted provided
  (LUnload provider) before afterState tag Refl checked snapshot targetInstalled =
    case lUnloadBoundary nameEq keyEq provider before afterState tag
      (checkedActionProjects nameEq keyEq (LUnload provider) before afterState tag
        checked) of
      (tagShape, sourceTrue, targetFalse) =>
        falseAndTrueImpossible targetFalse targetInstalled

0 consumerResolutionStart :
  {start, end : SystemState name key value world error} ->
  {trace : Transitions start end} ->
  ConsumerResolutionConstant name key world error value nameEq keyEq consumer
    wanted provider trace ->
  resolvedProviderAt @{nameEq} @{keyEq} consumer wanted provider start = True
consumerResolutionStart (ResolutionConstantEnd resolved) = resolved
consumerResolutionStart (ResolutionConstantStep transition rest resolved tail) = resolved

public export
record ProviderValueTraceResult
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (provider : name) (wanted : key) (provided : value wanted)
  {start, finalState : SystemState name key value world error}
  (trace : Transitions start finalState) where
  constructor MkProviderValueTraceResult
  finalProviderWellFormed :
    registryWellFormed @{nameEq} @{keyEq} finalState = True
  finalProviderSnapshot : StableProviderValue name key world error value nameEq
    keyEq provider wanted provided finalState
  providerTraceValues : ProviderValueConstant name key world error value nameEq keyEq
    provider wanted provided trace
  providerTraceInstalled : InstalledTrace name key world error value nameEq keyEq
    provider trace

public export
0 providerValueConstantTrace :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (consumer, provider : name) -> (wanted : key) -> (provided : value wanted) ->
  (trace : Transitions start finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  registryWellFormed @{nameEq} @{keyEq} start = True ->
  ConsumerResolutionConstant name key world error value nameEq keyEq consumer
    wanted provider trace ->
  StableProviderValue name key world error value nameEq keyEq provider wanted
    provided start ->
  ProviderValueTraceResult name key world error value nameEq keyEq provider wanted
    provided trace
providerValueConstantTrace nameEq keyEq consumer provider wanted provided
  NoTransitions AlignedEnd wellFormed (ResolutionConstantEnd resolved) snapshot =
    MkProviderValueTraceResult wellFormed snapshot
      (ValueConstantEnd (stableValuePresent snapshot))
      (InstalledEnd (stableValueInstalled nameEq snapshot))
providerValueConstantTrace nameEq keyEq consumer provider wanted provided
  (MoreTransitions transition@(Fired nameEq keyEq action tag checked) rest)
  (AlignedStep action tag checked rest alignedRest) wellFormed
  (ResolutionConstantStep (Fired nameEq keyEq action tag checked) rest
    sourceResolved resolutionRest) snapshot =
    let raw = checkedActionProjects nameEq keyEq action _ _ tag checked
        targetWellFormed = preservationTheoremProof nameEq keyEq action _ _ tag
          wellFormed raw
        targetData = resolvedProviderData nameEq keyEq consumer wanted provider _
          targetWellFormed (consumerResolutionStart resolutionRest)
        targetSnapshot = case decEq @{nameEq} provider (actionOwner action) of
          No distinct => stableProviderValueForeign nameEq keyEq provider wanted
            provided action _ _ tag distinct raw snapshot
          Yes same =>
            let valueStable = selectedProviderValueStep nameEq keyEq provider wanted
                  provided action _ _ tag (sym same) checked snapshot
                  (resolvedProviderInstalled targetData)
                targetPresent = trans valueStable (stableValuePresent snapshot)
            in MkStableProviderValue (resolvedProviderFiber targetData)
              (resolvedProviderLookup targetData)
              (resolvedProviderStable targetData) targetPresent
        tailResult = providerValueConstantTrace nameEq keyEq consumer provider wanted
          provided rest alignedRest targetWellFormed resolutionRest targetSnapshot
    in MkProviderValueTraceResult
      (finalProviderWellFormed tailResult)
      (finalProviderSnapshot tailResult)
      (ValueConstantStep transition rest (stableValuePresent snapshot)
        (providerTraceValues tailResult))
      (InstalledStep action tag checked rest
        (stableValueInstalled nameEq snapshot)
        (providerTraceInstalled tailResult))

public export
0 alignedTraceWellFormedEnd :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trace : Transitions start finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  registryWellFormed @{nameEq} @{keyEq} start = True ->
  registryWellFormed @{nameEq} @{keyEq} finalState = True
alignedTraceWellFormedEnd nameEq keyEq NoTransitions AlignedEnd wellFormed = wellFormed
alignedTraceWellFormedEnd nameEq keyEq
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
  (AlignedStep action tag checked rest alignedRest) wellFormed =
    let raw = checkedActionProjects nameEq keyEq action _ _ tag checked
        nextWellFormed = preservationTheoremProof nameEq keyEq action _ _ tag
          wellFormed raw
    in alignedTraceWellFormedEnd nameEq keyEq rest alignedRest nextWellFormed

public export
0 emptyRegistryUninstalled :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  bindings (registry state) = [] ->
  installedAt @{nameEq} selected state = False
emptyRegistryUninstalled nameEq selected
  (MkSystemState ambient (MkCoeffectContext [] unique)) Refl = Refl
emptyRegistryUninstalled nameEq selected
  (MkSystemState ambient (MkCoeffectContext (binding :: rest) unique)) empty =
    case empty of Refl impossible

0 appendFinalPath :
  (path : Transitions first middle) ->
  (lastStep : Transition middle finalState) ->
  StrictTransitions first finalState
appendFinalPath NoTransitions lastStep = OneOrMore lastStep NoTransitions
appendFinalPath (MoreTransitions firstStep rest) lastStep =
  OneOrMore firstStep (appendTransitions rest
    (MoreTransitions lastStep NoTransitions))

0 appendFinalPathTrace :
  (path : Transitions first middle) ->
  (lastStep : Transition middle finalState) ->
  strictToTransitions (appendFinalPath path lastStep) =
    appendTransitions path (MoreTransitions lastStep NoTransitions)
appendFinalPathTrace NoTransitions lastStep = Refl
appendFinalPathTrace (MoreTransitions firstStep rest) lastStep = Refl

0 nestedOpeningOrder :
  (providerBefore : Transitions initial providerPre) ->
  (providerOpening : Transition providerPre providerStart) ->
  (between : Transitions providerStart consumerPre) ->
  (consumerBefore : Transitions initial consumerPre) ->
  (consumerOpening : Transition consumerPre consumerStart) ->
  appendTransitions providerBefore
    (MoreTransitions providerOpening between) = consumerBefore ->
  appendTransitions consumerBefore
    (MoreTransitions consumerOpening NoTransitions) =
  appendTransitions
    (appendTransitions providerBefore
      (MoreTransitions providerOpening NoTransitions))
    (strictToTransitions (appendFinalPath between consumerOpening))
nestedOpeningOrder providerBefore providerOpening between consumerBefore
  consumerOpening split =
    rewrite appendFinalPathTrace between consumerOpening in
    rewrite appendTransitionsAssociative providerBefore
      (MoreTransitions providerOpening NoTransitions)
      (appendTransitions between
        (MoreTransitions consumerOpening NoTransitions)) in
    rewrite sym (appendTransitionsAssociative providerBefore
      (MoreTransitions providerOpening between)
      (MoreTransitions consumerOpening NoTransitions)) in
    rewrite split in Refl

0 nestedClosingOrder :
  (providerOpeningPrefix : Transitions initial providerStart) ->
  (afterProviderOpening : Transitions providerStart consumerPre) ->
  (consumerOpening : Transition consumerPre consumerStart) ->
  (consumerAfterOpening : Transitions consumerStart consumerAfter) ->
  (beforeProviderClosing : Transitions consumerAfter providerLast) ->
  (providerClosing : Transition providerLast providerAfter) ->
  appendTransitions providerOpeningPrefix
    (appendTransitions
      (appendTransitions afterProviderOpening
        (appendTransitions
          (MoreTransitions consumerOpening consumerAfterOpening)
          beforeProviderClosing))
      (MoreTransitions providerClosing NoTransitions)) =
  appendTransitions
    (appendTransitions
      (appendTransitions providerOpeningPrefix
        (appendTransitions afterProviderOpening
          (MoreTransitions consumerOpening NoTransitions)))
      consumerAfterOpening)
    (appendTransitions beforeProviderClosing
      (MoreTransitions providerClosing NoTransitions))
nestedClosingOrder providerOpeningPrefix afterProviderOpening consumerOpening
  consumerAfterOpening beforeProviderClosing providerClosing =
    rewrite appendTransitionsAssociative afterProviderOpening
      (appendTransitions (MoreTransitions consumerOpening consumerAfterOpening)
        beforeProviderClosing)
      (MoreTransitions providerClosing NoTransitions) in
    rewrite appendTransitionsAssociative
      (MoreTransitions consumerOpening consumerAfterOpening)
      beforeProviderClosing (MoreTransitions providerClosing NoTransitions) in
    rewrite appendTransitionsAssociative
      (appendTransitions providerOpeningPrefix
        (appendTransitions afterProviderOpening
          (MoreTransitions consumerOpening NoTransitions)))
      consumerAfterOpening
      (appendTransitions beforeProviderClosing
        (MoreTransitions providerClosing NoTransitions)) in
    rewrite appendTransitionsAssociative providerOpeningPrefix
      (appendTransitions afterProviderOpening
        (MoreTransitions consumerOpening NoTransitions))
      (appendTransitions consumerAfterOpening
        (appendTransitions beforeProviderClosing
          (MoreTransitions providerClosing NoTransitions))) in
    rewrite appendTransitionsAssociative afterProviderOpening
      (MoreTransitions consumerOpening NoTransitions)
      (appendTransitions consumerAfterOpening
        (appendTransitions beforeProviderClosing
          (MoreTransitions providerClosing NoTransitions))) in Refl

public export
0 extractContainingProviderEpisode :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider, consumer : name) ->
  (global : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  (consumerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    consumer global) ->
  Not (consumer = provider) ->
  installedAt @{nameEq} provider initial = False ->
  installedAt @{nameEq} provider
    (locatedPreStart consumerEpisode) = True ->
  installedAt @{nameEq} provider
    (locatedAfter consumerEpisode) = True ->
  installedAt @{nameEq} provider finalState = False ->
  InstalledTrace name key world error value nameEq keyEq provider
    (MoreTransitions
      (beginTransition (closedOpening (locatedEpisode consumerEpisode)))
      (closedTransitions (locatedEpisode consumerEpisode))) ->
  (providerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
      provider global **
    ProviderContainsConsumer providerEpisode consumerEpisode)
extractContainingProviderEpisode nameEq keyEq provider consumer global aligned
  consumerEpisode distinct initialFalse providerBeforeConsumer providerAfterConsumer
  finalFalse providerCenterInstalled =
  let alignedSplit = alignedAppendSplit (traceBeforeOpening consumerEpisode)
        (appendTransitions (MoreTransitions (beginTransition (closedOpening (locatedEpisode consumerEpisode))) (closedTransitions (locatedEpisode consumerEpisode))) (traceAfterClosing consumerEpisode))
        (rewrite (locatedDecomposition consumerEpisode) in aligned)
      leftAligned = fst alignedSplit
      centerRightAligned = snd alignedSplit
      centerSplit = alignedAppendSplit (MoreTransitions (beginTransition (closedOpening (locatedEpisode consumerEpisode))) (closedTransitions (locatedEpisode consumerEpisode))) (traceAfterClosing consumerEpisode) centerRightAligned
      rightAligned = snd centerSplit
  in case extractLastOpening nameEq keyEq provider (traceBeforeOpening consumerEpisode) leftAligned
       initialFalse providerBeforeConsumer of
    MkLastOpeningResult providerPre providerStart providerPrefix providerOpening
      afterProviderOpening providerOpeningSplit afterProviderInstalled =>
      case extractFirstClosing nameEq keyEq provider (traceAfterClosing consumerEpisode) rightAligned
        providerAfterConsumer finalFalse of
        MkFirstClosingResult providerLast providerAfter beforeProviderClosing
          beforeProviderInstalled providerClosing afterProviderClosing
          providerClosingSplit =>
          let centerBeforeInstalled = appendInstalledTrace (MoreTransitions (beginTransition (closedOpening (locatedEpisode consumerEpisode))) (closedTransitions (locatedEpisode consumerEpisode)))
                beforeProviderClosing providerCenterInstalled beforeProviderInstalled
              insideInstalled = appendInstalledTrace afterProviderOpening
                (appendTransitions (MoreTransitions (beginTransition (closedOpening (locatedEpisode consumerEpisode))) (closedTransitions (locatedEpisode consumerEpisode))) beforeProviderClosing) afterProviderInstalled centerBeforeInstalled
              combinedClosingSplit :
                (appendTransitions (appendTransitions (MoreTransitions (beginTransition (closedOpening (locatedEpisode consumerEpisode))) (closedTransitions (locatedEpisode consumerEpisode))) beforeProviderClosing)
                  (MoreTransitions (unloadTransition providerClosing)
                    afterProviderClosing) =
                appendTransitions (MoreTransitions (beginTransition (closedOpening (locatedEpisode consumerEpisode))) (closedTransitions (locatedEpisode consumerEpisode))) (traceAfterClosing consumerEpisode))
              combinedClosingSplit =
                rewrite appendTransitionsAssociative (MoreTransitions (beginTransition (closedOpening (locatedEpisode consumerEpisode))) (closedTransitions (locatedEpisode consumerEpisode)))
                  beforeProviderClosing
                  (MoreTransitions (unloadTransition providerClosing)
                    afterProviderClosing) in
                rewrite providerClosingSplit in Refl
              0 providerDecomposition :
                (appendTransitions providerPrefix
                  (MoreTransitions (beginTransition providerOpening)
                    (appendTransitions
                      (appendTransitions (appendTransitions afterProviderOpening (appendTransitions (MoreTransitions (beginTransition (closedOpening (locatedEpisode consumerEpisode))) (closedTransitions (locatedEpisode consumerEpisode))) beforeProviderClosing))
                        (MoreTransitions (unloadTransition providerClosing)
                          NoTransitions))
                      afterProviderClosing)) = global)
              providerDecomposition =
                rewrite appendTransitionsAssociative (appendTransitions afterProviderOpening (appendTransitions (MoreTransitions (beginTransition (closedOpening (locatedEpisode consumerEpisode))) (closedTransitions (locatedEpisode consumerEpisode))) beforeProviderClosing))
                  (MoreTransitions (unloadTransition providerClosing) NoTransitions)
                  afterProviderClosing in
                rewrite sym (locatedDecomposition consumerEpisode) in
                spanningDecomposition providerPrefix providerOpening
                afterProviderOpening (appendTransitions (MoreTransitions (beginTransition (closedOpening (locatedEpisode consumerEpisode))) (closedTransitions (locatedEpisode consumerEpisode))) beforeProviderClosing) providerClosing
                afterProviderClosing (traceBeforeOpening consumerEpisode)
                (appendTransitions (MoreTransitions (beginTransition (closedOpening (locatedEpisode consumerEpisode))) (closedTransitions (locatedEpisode consumerEpisode))) (traceAfterClosing consumerEpisode))
                providerOpeningSplit combinedClosingSplit
              0 providerClosed : ClosedEpisode name key world error value
                nameEq keyEq provider providerPre providerAfter
              providerClosed = MkClosedEpisode providerStart providerLast
                providerOpening (appendTransitions afterProviderOpening (appendTransitions (MoreTransitions (beginTransition (closedOpening (locatedEpisode consumerEpisode))) (closedTransitions (locatedEpisode consumerEpisode))) beforeProviderClosing)) insideInstalled providerClosing
              0 providerLocated : LocatedClosedEpisode name key world error value
                nameEq keyEq provider global
              providerLocated = MkLocatedClosedEpisode providerPre providerAfter
                providerPrefix providerClosed afterProviderClosing
                providerDecomposition
              0 providerToConsumerPath : StrictTransitions providerStart
                (closedStartState (locatedEpisode consumerEpisode))
              providerToConsumerPath = appendFinalPath afterProviderOpening
                (beginTransition (closedOpening (locatedEpisode consumerEpisode)))
              0 consumerToProviderPath : StrictTransitions
                (locatedAfter consumerEpisode) providerAfter
              consumerToProviderPath = appendFinalPath beforeProviderClosing
                (unloadTransition providerClosing)
              0 openingOrder : prefixThroughOpening consumerEpisode =
                appendTransitions (prefixThroughOpening providerLocated)
                  (strictToTransitions providerToConsumerPath)
              openingOrder = nestedOpeningOrder providerPrefix
                (beginTransition providerOpening) afterProviderOpening
                (traceBeforeOpening consumerEpisode) (beginTransition (closedOpening (locatedEpisode consumerEpisode)))
                providerOpeningSplit
              0 expandedClosingOrder :
                prefixThroughClose providerLocated =
                appendTransitions
                  (appendTransitions
                    (appendTransitions (prefixThroughOpening providerLocated)
                      (appendTransitions afterProviderOpening
                        (MoreTransitions
                          (beginTransition (closedOpening
                            (locatedEpisode consumerEpisode))) NoTransitions)))
                    (closedTransitions (locatedEpisode consumerEpisode)))
                  (appendTransitions beforeProviderClosing
                    (MoreTransitions (unloadTransition providerClosing)
                      NoTransitions))
              expandedClosingOrder = nestedClosingOrder
                (prefixThroughOpening providerLocated) afterProviderOpening
                (beginTransition (closedOpening (locatedEpisode consumerEpisode)))
                (closedTransitions (locatedEpisode consumerEpisode)) beforeProviderClosing
                (unloadTransition providerClosing)
              0 closingPrefixExpansion :
                appendTransitions (prefixThroughClose consumerEpisode)
                  (appendTransitions beforeProviderClosing
                    (MoreTransitions (unloadTransition providerClosing)
                      NoTransitions)) =
                appendTransitions
                  (appendTransitions
                    (appendTransitions (prefixThroughOpening providerLocated)
                      (appendTransitions afterProviderOpening
                        (MoreTransitions
                          (beginTransition (closedOpening
                            (locatedEpisode consumerEpisode))) NoTransitions)))
                    (closedTransitions (locatedEpisode consumerEpisode)))
                  (appendTransitions beforeProviderClosing
                    (MoreTransitions (unloadTransition providerClosing)
                      NoTransitions))
              closingPrefixExpansion =
                rewrite sym (appendFinalPathTrace afterProviderOpening
                  (beginTransition (closedOpening
                    (locatedEpisode consumerEpisode)))) in
                cong
                (\openingPrefix => appendTransitions
                  (appendTransitions openingPrefix
                    (closedTransitions (locatedEpisode consumerEpisode)))
                  (appendTransitions beforeProviderClosing
                    (MoreTransitions (unloadTransition providerClosing)
                      NoTransitions)))
                openingOrder
              0 closingOrder : prefixThroughClose providerLocated =
                appendTransitions (prefixThroughClose consumerEpisode)
                  (strictToTransitions consumerToProviderPath)
              closingOrder =
                rewrite appendFinalPathTrace beforeProviderClosing
                  (unloadTransition providerClosing) in
                trans expandedClosingOrder (sym closingPrefixExpansion)
          in (providerLocated ** MkProviderContainsConsumer
            providerToConsumerPath consumerToProviderPath openingOrder closingOrder)

public export
0 alignedEpisodeInside :
  (opening : BeginStep nameEq keyEq consumer preStart start) ->
  (inside : Transitions start afterState) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions (beginTransition opening) inside) ->
  AlignedTransitions name key world error value nameEq keyEq inside
alignedEpisodeInside opening inside
  (AlignedStep (LBegin consumer) LBeginTag (beginEquation opening) inside aligned) =
    aligned

public export
0 lookupFiberEmptyRegistry :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  bindings (registry state) = [] ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} selected (registry state) = Nothing
lookupFiberEmptyRegistry nameEq selected
  (MkSystemState ambient (MkCoeffectContext [] unique)) Refl = Refl
lookupFiberEmptyRegistry nameEq selected
  (MkSystemState ambient (MkCoeffectContext (entry :: rest) unique)) empty =
    case empty of Refl impossible

public export
0 supportSetEmptyRegistry :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  bindings (registry state) = [] -> supportSet @{nameEq} @{keyEq} state = []
supportSetEmptyRegistry nameEq keyEq
  (MkSystemState ambient (MkCoeffectContext [] unique)) Refl = Refl
supportSetEmptyRegistry nameEq keyEq
  (MkSystemState ambient (MkCoeffectContext (entry :: rest) unique)) empty =
    case empty of Refl impossible

