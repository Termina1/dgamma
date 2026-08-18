module DGamma.Calculus

import DGamma.Core
import DGamma.Coeffects
import Decidable.Equality
import Data.List
import Data.List.Elem
import Data.Maybe

%default total

||| A fiber-owned dynamic table whose domain is confined to its declaration.
public export
record OwnedTable (key : Type) (value : key -> Type)
                  (provision : CoeffectSpec key) where
  constructor MkOwnedTable
  ownedValues : CoeffectContext key value
  0 ownedSound : (k : key) ->
    Elem k (bindingKeys (bindings ownedValues)) ->
    Elem k (dependencies provision)

public export
emptyOwned : OwnedTable key value provision
emptyOwned = MkOwnedTable emptyContext (\k, present => absurd present)

record OrderRestrictedEntries (key : Type) (value : key -> Type)
  (allowed : List key) (original : List (Binding key value)) where
  constructor MkOrderRestrictedEntries
  orderRestrictedBindings : List (Binding key value)
  0 orderRestrictedUnique : UniqueKeys (bindingKeys orderRestrictedBindings)
  0 orderRestrictedSound : (k : key) ->
    Elem k (bindingKeys orderRestrictedBindings) -> Elem k allowed
  0 orderRestrictedSubset : (k : key) ->
    Elem k (bindingKeys orderRestrictedBindings) -> Elem k (bindingKeys original)

memberKeyList : DecEq key => key -> List key -> Bool
memberKeyList wanted [] = False
memberKeyList wanted (current :: rest) = case decEq wanted current of
  Yes Refl => True
  No distinct => memberKeyList wanted rest

0 memberKeyListTrueElem : DecEq key => (selected : key) -> (values : List key) ->
  memberKeyList selected values = True -> Elem selected values
memberKeyListTrueElem selected [] present = case present of Refl impossible
memberKeyListTrueElem selected (current :: rest) present with
  (decEq selected current)
  memberKeyListTrueElem current (current :: rest) present | Yes Refl = Here
  memberKeyListTrueElem selected (current :: rest) present | No distinct =
    There (memberKeyListTrueElem selected rest present)

orderRestrictEntries : DecEq key => (allowed : List key) ->
  (entries : List (Binding key value)) ->
  (0 unique : UniqueKeys (bindingKeys entries)) ->
  OrderRestrictedEntries key value allowed entries
orderRestrictEntries allowed [] UniqueNil =
  MkOrderRestrictedEntries [] UniqueNil
    (\k, present => absurd present)
    (\k, present => absurd present)
orderRestrictEntries allowed (Bind current observed :: rest)
  (UniqueCons headFresh tailUnique) with
  (memberKeyList current allowed) proof member
  orderRestrictEntries allowed (Bind current observed :: rest)
    (UniqueCons headFresh tailUnique) | False =
      let tail = orderRestrictEntries allowed rest tailUnique in
      MkOrderRestrictedEntries (orderRestrictedBindings tail)
        (orderRestrictedUnique tail) (orderRestrictedSound tail)
        (\k, present => There (orderRestrictedSubset tail k present))
  orderRestrictEntries allowed (Bind current observed :: rest)
    (UniqueCons headFresh tailUnique) | True =
      let tail = orderRestrictEntries allowed rest tailUnique
          0 currentFresh : Not
            (Elem current (bindingKeys (orderRestrictedBindings tail)))
          currentFresh present = headFresh
            (orderRestrictedSubset tail current present)
      in MkOrderRestrictedEntries
        (Bind current observed :: orderRestrictedBindings tail)
        (UniqueCons currentFresh (orderRestrictedUnique tail))
        (\k, present => case present of
          Here => memberKeyListTrueElem current allowed member
          There later => orderRestrictedSound tail k later)
        (\k, present => case present of
          Here => Here
          There later => There (orderRestrictedSubset tail k later))

AllKeysAllowed : {key : Type} -> List key -> List key -> Type
AllKeysAllowed {key} keys allowed =
  (k : key) -> Elem k keys -> Elem k allowed

0 decUniqueKeys : DecEq key => (keys : List key) -> Dec (UniqueKeys keys)
decUniqueKeys [] = Yes UniqueNil
decUniqueKeys (current :: rest) with (isElem current rest)
  decUniqueKeys (current :: rest) | Yes present =
    No (\(UniqueCons fresh tailUnique) => fresh present)
  decUniqueKeys (current :: rest) | No absent with (decUniqueKeys rest)
    decUniqueKeys (current :: rest) | No absent | Yes tailUnique =
      Yes (UniqueCons absent tailUnique)
    decUniqueKeys (current :: rest) | No absent | No notUnique =
      No (\(UniqueCons fresh tailUnique) => notUnique tailUnique)

0 decAllKeysAllowed : DecEq key => (keys, allowed : List key) ->
  Dec (AllKeysAllowed keys allowed)
decAllKeysAllowed [] allowed = Yes (\k, present => case present of _ impossible)
decAllKeysAllowed (current :: rest) allowed with (isElem current allowed)
  decAllKeysAllowed (current :: rest) allowed | No absent =
    No (\sound => absent (sound current Here))
  decAllKeysAllowed (current :: rest) allowed | Yes currentAllowed
    with (decAllKeysAllowed rest allowed)
    decAllKeysAllowed (current :: rest) allowed | Yes currentAllowed |
      No tailRejected =
        No (\sound => tailRejected (\k, later => sound k (There later)))
    decAllKeysAllowed (current :: rest) allowed | Yes currentAllowed |
      Yes tailSound = Yes (\k, present => case present of
        Here => currentAllowed
        There later => tailSound k later)

%inline
0 canonicalUniqueKeys : DecEq key => (keys : List key) ->
  UniqueKeys keys -> UniqueKeys keys
canonicalUniqueKeys keys evidence with (decUniqueKeys keys)
  canonicalUniqueKeys keys evidence | Yes canonical = canonical
  canonicalUniqueKeys keys evidence | No rejected = void (rejected evidence)

%inline
0 canonicalAllowed : DecEq key => (keys, allowed : List key) ->
  AllKeysAllowed keys allowed -> AllKeysAllowed keys allowed
canonicalAllowed keys allowed evidence with (decAllKeysAllowed keys allowed)
  canonicalAllowed keys allowed evidence | Yes canonical = canonical
  canonicalAllowed keys allowed evidence | No rejected = void (rejected evidence)

%inline
canonicalOwnedFromFiltered : DecEq key =>
  (provision : CoeffectSpec key) ->
  (filtered : List (Binding key value)) ->
  (0 unique : UniqueKeys (bindingKeys filtered)) ->
  (0 sound : AllKeysAllowed (bindingKeys filtered) (dependencies provision)) ->
  OwnedTable key value provision
canonicalOwnedFromFiltered provision filtered unique sound =
  MkOwnedTable
    (MkCoeffectContext filtered
      (canonicalUniqueKeys (bindingKeys filtered) unique))
    (canonicalAllowed (bindingKeys filtered) (dependencies provision) sound)

0 canonicalOwnedEvidenceIrrelevant : DecEq key =>
  (provision : CoeffectSpec key) ->
  (filtered : List (Binding key value)) ->
  (leftUnique, rightUnique : UniqueKeys (bindingKeys filtered)) ->
  (leftSound, rightSound :
    AllKeysAllowed (bindingKeys filtered) (dependencies provision)) ->
  canonicalOwnedFromFiltered provision filtered leftUnique leftSound =
  canonicalOwnedFromFiltered provision filtered rightUnique rightSound
canonicalOwnedEvidenceIrrelevant provision filtered leftUnique rightUnique
  leftSound rightSound with (decUniqueKeys (bindingKeys filtered))
  canonicalOwnedEvidenceIrrelevant provision filtered leftUnique rightUnique
    leftSound rightSound | No rejected = void (rejected leftUnique)
  canonicalOwnedEvidenceIrrelevant provision filtered leftUnique rightUnique
    leftSound rightSound | Yes canonicalUnique
    with (decAllKeysAllowed (bindingKeys filtered) (dependencies provision))
    canonicalOwnedEvidenceIrrelevant provision filtered leftUnique rightUnique
      leftSound rightSound | Yes canonicalUnique | No rejected =
        void (rejected leftSound)
    canonicalOwnedEvidenceIrrelevant provision filtered leftUnique rightUnique
      leftSound rightSound | Yes canonicalUnique | Yes canonicalSound = Refl

0 canonicalOwnedFromFilteredCong : DecEq key =>
  (provision : CoeffectSpec key) ->
  (leftFiltered, rightFiltered : List (Binding key value)) ->
  (same : leftFiltered = rightFiltered) ->
  (leftUnique : UniqueKeys (bindingKeys leftFiltered)) ->
  (rightUnique : UniqueKeys (bindingKeys rightFiltered)) ->
  (leftSound : AllKeysAllowed (bindingKeys leftFiltered)
    (dependencies provision)) ->
  (rightSound : AllKeysAllowed (bindingKeys rightFiltered)
    (dependencies provision)) ->
  canonicalOwnedFromFiltered provision leftFiltered leftUnique leftSound =
  canonicalOwnedFromFiltered provision rightFiltered rightUnique rightSound
canonicalOwnedFromFilteredCong provision leftFiltered leftFiltered Refl
  leftUnique rightUnique leftSound rightSound =
    canonicalOwnedEvidenceIrrelevant provision leftFiltered leftUnique
      rightUnique leftSound rightSound

0 orderRestrictedBindingsProofIrrelevant : DecEq key =>
  (allowed : List key) -> (entries : List (Binding key value)) ->
  (leftUnique, rightUnique : UniqueKeys (bindingKeys entries)) ->
  orderRestrictedBindings (orderRestrictEntries allowed entries leftUnique) =
  orderRestrictedBindings (orderRestrictEntries allowed entries rightUnique)
orderRestrictedBindingsProofIrrelevant allowed [] UniqueNil UniqueNil = Refl
orderRestrictedBindingsProofIrrelevant allowed
  (Bind current observed :: rest)
  (UniqueCons leftFresh leftUnique) (UniqueCons rightFresh rightUnique)
  with (memberKeyList current allowed)
  orderRestrictedBindingsProofIrrelevant allowed
    (Bind current observed :: rest)
    (UniqueCons leftFresh leftUnique) (UniqueCons rightFresh rightUnique) |
    False = orderRestrictedBindingsProofIrrelevant allowed rest leftUnique
      rightUnique
  orderRestrictedBindingsProofIrrelevant allowed
    (Bind current observed :: rest)
    (UniqueCons leftFresh leftUnique) (UniqueCons rightFresh rightUnique) |
    True = cong (Bind current observed ::)
      (orderRestrictedBindingsProofIrrelevant allowed rest leftUnique rightUnique)

||| Reconstruct a capability-confined table by filtering the input bindings in
||| their existing order. Finding #10 canonicalizes both erased certificates
||| from the runtime output bindings and provision; source proof identity is
||| used only to rule out impossible decision branches.
public export
restrictOwnedPreservingOrder : DecEq key => (provision : CoeffectSpec key) ->
  CoeffectContext key value -> OwnedTable key value provision
restrictOwnedPreservingOrder provision@(MkCoeffectSpec allowed allowedUnique)
  (MkCoeffectContext entries entriesUnique) =
    let result = orderRestrictEntries allowed entries entriesUnique in
    canonicalOwnedFromFiltered provision (orderRestrictedBindings result)
      (orderRestrictedUnique result) (orderRestrictedSound result)

||| Finding #10 keystone: equal complete ordered runtime bindings normalize to
||| propositionally equal owned tables, regardless of erased source certificates.
public export
0 canonicalNormalizationFromEqualBindings : DecEq key =>
  (provision : CoeffectSpec key) ->
  (left, right : CoeffectContext key value) ->
  bindings left = bindings right ->
  restrictOwnedPreservingOrder provision left =
  restrictOwnedPreservingOrder provision right
canonicalNormalizationFromEqualBindings
  provision@(MkCoeffectSpec allowed allowedUnique)
  (MkCoeffectContext leftEntries leftUnique)
  (MkCoeffectContext rightEntries rightUnique) sameBindings =
    case sameBindings of
      Refl =>
        let 0 filteredSame :
              (orderRestrictedBindings
                 (orderRestrictEntries allowed rightEntries leftUnique) =
               orderRestrictedBindings
                 (orderRestrictEntries allowed rightEntries rightUnique))
            filteredSame = orderRestrictedBindingsProofIrrelevant allowed
              rightEntries leftUnique rightUnique
        in canonicalOwnedFromFilteredCong
          (MkCoeffectSpec allowed allowedUnique)
          (orderRestrictedBindings
            (orderRestrictEntries allowed rightEntries leftUnique))
          (orderRestrictedBindings
            (orderRestrictEntries allowed rightEntries rightUnique)) filteredSame
          (orderRestrictedUnique
            (orderRestrictEntries allowed rightEntries leftUnique))
          (orderRestrictedUnique
            (orderRestrictEntries allowed rightEntries rightUnique))
          (orderRestrictedSound
            (orderRestrictEntries allowed rightEntries leftUnique))
          (orderRestrictedSound
            (orderRestrictEntries allowed rightEntries rightUnique))

0 memberKeyListFromElem : DecEq key => (selected : key) ->
  (allowed : List key) -> Elem selected allowed ->
  memberKeyList selected allowed = True
memberKeyListFromElem selected (selected :: rest) Here
  with (decEq selected selected)
  memberKeyListFromElem selected (selected :: rest) Here | Yes Refl = Refl
  memberKeyListFromElem selected (selected :: rest) Here | No contra =
    void (contra Refl)
memberKeyListFromElem selected (current :: rest) (There later)
  with (decEq selected current)
  memberKeyListFromElem current (current :: rest) (There later) | Yes Refl = Refl
  memberKeyListFromElem selected (current :: rest) (There later) | No _ =
    memberKeyListFromElem selected rest later

0 orderRestrictBindingsIdentity : DecEq key =>
  (allowed : List key) ->
  (entries : List (Binding key value)) ->
  (unique : UniqueKeys (bindingKeys entries)) ->
  ((k : key) -> Elem k (bindingKeys entries) -> Elem k allowed) ->
  orderRestrictedBindings (orderRestrictEntries allowed entries unique) = entries
orderRestrictBindingsIdentity allowed [] UniqueNil sound = Refl
orderRestrictBindingsIdentity allowed (Bind current observed :: rest)
  (UniqueCons headFresh tailUnique) sound
  with (memberKeyList current allowed) proof member
  orderRestrictBindingsIdentity allowed (Bind current observed :: rest)
    (UniqueCons headFresh tailUnique) sound | False =
      let present = memberKeyListFromElem current allowed (sound current Here)
      in case trans (sym member) present of Refl impossible
  orderRestrictBindingsIdentity allowed (Bind current observed :: rest)
    (UniqueCons headFresh tailUnique) sound | True =
      cong (Bind current observed ::)
        (orderRestrictBindingsIdentity allowed rest tailUnique
          (\k, later => sound k (There later)))

||| Normalizing an already confined owned table preserves its runtime binding
||| list exactly, including its existing order.  The two reconstructed erased
||| uniqueness witnesses need not be propositionally equal, so the executable
||| statement intentionally projects `bindings`.
public export
0 restrictOwnedPreservingOrderBindings : DecEq key =>
  (provision : CoeffectSpec key) ->
  (table : OwnedTable key value provision) ->
  bindings (ownedValues
    (restrictOwnedPreservingOrder provision (ownedValues table))) =
  bindings (ownedValues table)
restrictOwnedPreservingOrderBindings
  (MkCoeffectSpec allowed allowedUnique)
  (MkOwnedTable (MkCoeffectContext entries entriesUnique) sound) =
    orderRestrictBindingsIdentity allowed entries entriesUnique sound

0 orderRestrictedBindingsConstructor :
  (allowed : List key) -> (entries : List (Binding key value)) ->
  (filtered : List (Binding key value)) ->
  (unique : UniqueKeys (bindingKeys filtered)) ->
  (sound : AllKeysAllowed (bindingKeys filtered) allowed) ->
  (subset : AllKeysAllowed (bindingKeys filtered) (bindingKeys entries)) ->
  orderRestrictedBindings
    (MkOrderRestrictedEntries {allowed = allowed} {original = entries}
      filtered unique sound subset) = filtered
orderRestrictedBindingsConstructor allowed entries filtered unique sound subset =
  Refl

||| Finding #11's canonical-domain keystone: one order-preserving restriction
||| already is a fixed point of restriction, even when the original context was
||| not provision-confined.  This is stronger than runtime binding preservation:
||| it identifies the canonically rebuilt erased certificates propositionally.
public export
0 restrictOwnedPreservingOrderIdempotent : DecEq key =>
  (provision : CoeffectSpec key) ->
  (context : CoeffectContext key value) ->
  restrictOwnedPreservingOrder provision
    (ownedValues (restrictOwnedPreservingOrder provision context)) =
  restrictOwnedPreservingOrder provision context
restrictOwnedPreservingOrderIdempotent
  provision@(MkCoeffectSpec allowed allowedUnique)
  context@(MkCoeffectContext entries entriesUnique)
  with (orderRestrictEntries allowed entries entriesUnique) proof firstRun
  restrictOwnedPreservingOrderIdempotent
    provision@(MkCoeffectSpec allowed allowedUnique)
    context@(MkCoeffectContext entries entriesUnique) |
      MkOrderRestrictedEntries filtered firstUnique firstSound firstSubset =
        let observed = MkOrderRestrictedEntries {allowed = allowed}
              {original = entries} filtered firstUnique firstSound firstSubset
            observedBindings = orderRestrictedBindingsConstructor allowed
              entries filtered firstUnique firstSound firstSubset
        in rewrite observedBindings in
          let filteredAgain = orderRestrictBindingsIdentity allowed filtered
                (canonicalUniqueKeys (bindingKeys filtered) firstUnique)
                firstSound
          in canonicalOwnedFromFilteredCong
            (MkCoeffectSpec allowed allowedUnique)
            (orderRestrictedBindings (orderRestrictEntries allowed filtered
              (canonicalUniqueKeys (bindingKeys filtered) firstUnique)))
            filtered filteredAgain
            (orderRestrictedUnique (orderRestrictEntries allowed filtered
              (canonicalUniqueKeys (bindingKeys filtered) firstUnique)))
            firstUnique
            (orderRestrictedSound (orderRestrictEntries allowed filtered
              (canonicalUniqueKeys (bindingKeys filtered) firstUnique)))
            firstSound

||| The only state a component step may mutate: ambient state and its own table.
public export
record LocalState (key : Type) (value : key -> Type) (world : Type)
                  (provision : CoeffectSpec key) where
  constructor MkLocalState
  localWorld : world
  localTable : OwnedTable key value provision

||| Proof-transparent normalization of an already provision-confined local
||| state.  At runtime this preserves the ambient value and binding list exactly;
||| it deliberately rebuilds the erased confinement certificates so consecutive
||| yielded inverse maps share Definition 60's normalization rhythm.
public export
normalizeLocal : DecEq key => (provision : CoeffectSpec key) ->
  LocalState key value world provision -> LocalState key value world provision
normalizeLocal provision (MkLocalState ambient table) =
  MkLocalState ambient
    (restrictOwnedPreservingOrder provision (ownedValues table))

public export
0 normalizeLocalWorld : DecEq key => (provision : CoeffectSpec key) ->
  (local : LocalState key value world provision) ->
  localWorld (normalizeLocal provision local) = localWorld local
normalizeLocalWorld provision (MkLocalState ambient table) = Refl

public export
0 normalizeLocalBindings : DecEq key => (provision : CoeffectSpec key) ->
  (local : LocalState key value world provision) ->
  bindings (ownedValues (localTable (normalizeLocal provision local))) =
  bindings (ownedValues (localTable local))
normalizeLocalBindings provision (MkLocalState ambient table) =
  restrictOwnedPreservingOrderBindings provision table

||| Finding #11 companion keystone: normalization is propositionally
||| idempotent because Finding #10 makes its certificates canonical functions of
||| the complete ordered runtime bindings and provision.
public export
0 normalizeLocalIdempotent : DecEq key => (provision : CoeffectSpec key) ->
  (local : LocalState key value world provision) ->
  normalizeLocal provision (normalizeLocal provision local) =
  normalizeLocal provision local
normalizeLocalIdempotent provision (MkLocalState ambient table) =
  cong (MkLocalState ambient)
    (canonicalNormalizationFromEqualBindings provision
      (ownedValues
        (restrictOwnedPreservingOrder provision (ownedValues table)))
      (ownedValues table)
      (restrictOwnedPreservingOrderBindings provision table))

||| Every evaluator and Definition-60 step source is canonical: both construct
||| it by one order-preserving restriction from a complete actor context.
public export
0 restrictedLocalCanonical : DecEq key =>
  (provision : CoeffectSpec key) -> (ambient : world) ->
  (context : CoeffectContext key value) ->
  normalizeLocal provision
    (MkLocalState ambient (restrictOwnedPreservingOrder provision context)) =
  MkLocalState ambient (restrictOwnedPreservingOrder provision context)
restrictedLocalCanonical provision ambient context =
  cong (MkLocalState ambient)
    (restrictOwnedPreservingOrderIdempotent provision context)

||| Compose one newly yielded undo in LIFO order.  The inter-undo normalization
||| is erased-certificate transparent at runtime but makes the evaluator's
||| accumulator construction align definitionally with repeated Definition-60
||| `yieldedInverseEffectMap` applications.
public export
pushLocalUndo : DecEq key => (provision : CoeffectSpec key) ->
  (accumulator : LocalState key value world provision ->
    LocalState key value world provision) ->
  (undo : LocalState key value world provision ->
    LocalState key value world provision) ->
  LocalState key value world provision -> LocalState key value world provision
pushLocalUndo provision accumulator undo =
  accumulator . normalizeLocal provision . undo . normalizeLocal provision

||| A total, ordered capability for exactly the declared dependency keys.
public export
data DepValues : (key : Type) -> (value : key -> Type) -> List key -> Type where
  NoDepValues : DepValues key value []
  OneDepValue : value k -> DepValues key value rest ->
                DepValues key value (k :: rest)

public export
depValueAt : DecEq key => (wanted : key) -> (deps : List key) ->
  DepValues key value deps -> Maybe (value wanted)
depValueAt wanted [] NoDepValues = Nothing
depValueAt wanted (k :: ks) (OneDepValue v rest) with (decEq wanted k)
  depValueAt k (k :: ks) (OneDepValue v rest) | (Yes Refl) = Just v
  depValueAt wanted (k :: ks) (OneDepValue v rest) | (No _) =
    depValueAt wanted ks rest

||| Definitions 48/51: one capability-confined, partial, failing iterator step.
||| Its inverse is witnessed at the exact local application state.
public export
record StepEffect (key : Type) (value : key -> Type) (world, error : Type)
                  (deps : List key) (provision : CoeffectSpec key) where
  constructor MkStepEffect
  ||| Optional finite-host identifier for a component registration yielded by
  ||| this step. The actual fresh name is chosen by O-Insert; CP3 supplies the
  ||| shared catalog and trace-level occurrence correspondence.
  registrationYieldTag : Maybe Nat
  runStepEffect : DepValues key value deps ->
                  LocalState key value world provision ->
                  Either error
                    (LocalState key value world provision,
                     LocalState key value world provision ->
                       LocalState key value world provision)
  0 stepWitness : {auto keyEq : DecEq key} ->
    (capability : DepValues key value deps) ->
    (before, after : LocalState key value world provision) ->
    (undo : LocalState key value world provision ->
            LocalState key value world provision) ->
    runStepEffect capability before = Right (after, undo) ->
    normalizeLocal provision before = before ->
    undo (normalizeLocal provision after) = before

||| Discharge a `StepEffect` author's conditional recovery law at the exact
||| canonical source shape shared by L-Advance and Definition 60.
public export
0 restrictedStepRecovery : DecEq key =>
  {deps : List key} -> {provision : CoeffectSpec key} ->
  (step : StepEffect key value world error deps provision) ->
  (capability : DepValues key value deps) ->
  (ambient : world) -> (context : CoeffectContext key value) ->
  (after : LocalState key value world provision) ->
  (undo : LocalState key value world provision ->
    LocalState key value world provision) ->
  runStepEffect step capability
    (MkLocalState ambient
      (restrictOwnedPreservingOrder provision context)) =
    Right (after, undo) ->
  undo (normalizeLocal provision after) =
    MkLocalState ambient (restrictOwnedPreservingOrder provision context)
restrictedStepRecovery step capability ambient context after undo ran =
  stepWitness step capability
    (MkLocalState ambient (restrictOwnedPreservingOrder provision context))
    after undo ran (restrictedLocalCanonical provision ambient context)

||| L-Advance specializes the shared restricted-source proof to the fiber's
||| already provision-confined runtime table.
public export
0 advanceSourceStepRecovery : DecEq key =>
  {deps : List key} -> {provision : CoeffectSpec key} ->
  (step : StepEffect key value world error deps provision) ->
  (capability : DepValues key value deps) ->
  (ambient : world) -> (table : OwnedTable key value provision) ->
  (after : LocalState key value world provision) ->
  (undo : LocalState key value world provision ->
    LocalState key value world provision) ->
  runStepEffect step capability
    (MkLocalState ambient
      (restrictOwnedPreservingOrder provision (ownedValues table))) =
    Right (after, undo) ->
  undo (normalizeLocal provision after) =
    MkLocalState ambient
      (restrictOwnedPreservingOrder provision (ownedValues table))
advanceSourceStepRecovery step capability ambient table after undo ran =
  restrictedStepRecovery step capability ambient (ownedValues table) after undo
    ran

||| One successful push supplies the older accumulator with the canonical
||| recovered source. Consequently induction over repeated pushes never feeds a
||| later undo a noncanonical local state.
public export
0 pushLocalUndoRecoversStep : DecEq key =>
  {deps : List key} -> {provision : CoeffectSpec key} ->
  (step : StepEffect key value world error deps provision) ->
  (capability : DepValues key value deps) ->
  (ambient : world) -> (context : CoeffectContext key value) ->
  (after : LocalState key value world provision) ->
  (undo : LocalState key value world provision ->
    LocalState key value world provision) ->
  (accumulator : LocalState key value world provision ->
    LocalState key value world provision) ->
  runStepEffect step capability
    (MkLocalState ambient
      (restrictOwnedPreservingOrder provision context)) =
    Right (after, undo) ->
  pushLocalUndo provision accumulator undo (normalizeLocal provision after) =
    accumulator
      (MkLocalState ambient (restrictOwnedPreservingOrder provision context))
pushLocalUndoRecoversStep step capability ambient context after undo accumulator
  ran =
    let 0 afterCanonical = normalizeLocalIdempotent provision after
        0 recovered = restrictedStepRecovery step capability ambient context
          after undo ran
        0 sourceCanonical = restrictedLocalCanonical provision ambient context
    in rewrite afterCanonical in rewrite recovered in
      rewrite sourceCanonical in Refl

||| Definition 43: declarations plus a finite failing effect iterator.
public export
record Component (key : Type) (value : key -> Type)
                 (world, error : Type) where
  constructor MkComponent
  componentDependencies : CoeffectSpec key
  componentProvisions : CoeffectSpec key
  componentProgram : List (StepEffect key value world error
    (dependencies componentDependencies) componentProvisions)

||| A committed view is intrinsically total on exactly the dependency list.
public export
data View : (name : Type) -> List key -> Type where
  EmptyView : View name []
  ProviderView : name -> View name rest -> View name (k :: rest)

public export
viewProviders : View name deps -> List name
viewProviders EmptyView = []
viewProviders (ProviderView provider rest) = provider :: viewProviders rest

public export
viewEq : DecEq name => View name deps -> View name deps -> Bool
viewEq EmptyView EmptyView = True
viewEq (ProviderView left ls) (ProviderView right rs) =
  case decEq left right of
    Yes Refl => viewEq ls rs
    No _ => False

public export
viewContains : DecEq name => name -> View name deps -> Bool
viewContains wanted EmptyView = False
viewContains wanted (ProviderView provider rest) =
  case decEq wanted provider of
    Yes Refl => True
    No _ => viewContains wanted rest

public export
viewLookup : DecEq key => (wanted : key) -> (deps : List key) ->
  View name deps -> Maybe name
viewLookup wanted [] EmptyView = Nothing
viewLookup wanted (k :: ks) (ProviderView provider rest) with (decEq wanted k)
  viewLookup k (k :: ks) (ProviderView provider rest) | (Yes Refl) = Just provider
  viewLookup wanted (k :: ks) (ProviderView provider rest) | (No _) =
    viewLookup wanted ks rest

||| Definition 49. Accumulators restore both ambient state and the acting
||| fiber's dynamic table, while no other registry field is in their capability.
public export
data Lifecycle : (key : Type) -> (value : key -> Type) ->
  (world, error, name : Type) -> (deps : List key) ->
  (provision : CoeffectSpec key) -> Type where
  Inactive : Maybe error ->
    Lifecycle key value world error name deps provision
  Reloading : List (StepEffect key value world error deps provision) ->
              (LocalState key value world provision ->
               LocalState key value world provision) ->
              View name deps ->
              Lifecycle key value world error name deps provision
  Active : (LocalState key value world provision ->
            LocalState key value world provision) ->
           View name deps ->
           Lifecycle key value world error name deps provision
  Unloading : (LocalState key value world provision ->
               LocalState key value world provision) ->
              View name deps -> Maybe error ->
              Lifecycle key value world error name deps provision

public export
installed : Lifecycle key value world error name deps provision -> Bool
installed (Inactive _) = False
installed _ = True

public export
isActive : Lifecycle key value world error name deps provision -> Bool
isActive (Active _ _) = True
isActive _ = False

public export
committed : Lifecycle key value world error name deps provision ->
  Maybe (View name deps)
committed (Inactive _) = Nothing
committed (Reloading _ _ view) = Just view
committed (Active _ view) = Just view
committed (Unloading _ view _) = Just view

public export
data Parent name = Root | ChildOf name

||| Definition 44: a fiber owns its changing table. Lifecycle indices are tied
||| to the declarations of the immutable component.
public export
data Fiber : (name, key : Type) -> (value : key -> Type) ->
             (world, error : Type) -> Type where
  MkFiber : (component : Component key value world error) ->
            (parent : Parent name) -> (isRetired : Bool) ->
            (table : OwnedTable key value (componentProvisions component)) ->
            Lifecycle key value world error name
              (dependencies (componentDependencies component))
              (componentProvisions component) ->
            Fiber name key value world error

public export
fiberComponent : Fiber name key value world error -> Component key value world error
fiberComponent (MkFiber component _ _ _ _) = component

public export
fiberParent : Fiber name key value world error -> Parent name
fiberParent (MkFiber _ parent _ _ _) = parent

public export
retired : Fiber name key value world error -> Bool
retired (MkFiber _ _ flag _ _) = flag

public export
fiberTable : (fiber : Fiber name key value world error) ->
  OwnedTable key value (componentProvisions (fiberComponent fiber))
fiberTable (MkFiber _ _ _ table _) = table

public export
fiberLifecycle : (fiber : Fiber name key value world error) ->
  Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))
fiberLifecycle (MkFiber _ _ _ _ lifecycle) = lifecycle

public export
fiberContinuationLength : Fiber name key value world error -> Maybe Nat
fiberContinuationLength
  (MkFiber component parent retiredFlag table lifecycle) = case lifecycle of
    Reloading remaining accumulator view => Just (length remaining)
    _ => Nothing

public export
0 fiberLifecycleObservation :
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  fiberLifecycle (MkFiber component parent retiredFlag table lifecycle) = lifecycle
fiberLifecycleObservation component parent retiredFlag table lifecycle = Refl


public export
freshFiber : Component key value world error -> Parent name ->
  Fiber name key value world error
freshFiber component parent =
  MkFiber component parent False emptyOwned (Inactive Nothing)

public export
%inline
setFiberRuntime : (fiber : Fiber name key value world error) ->
  (table : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)) ->
  Fiber name key value world error
setFiberRuntime (MkFiber component parent retired oldTable oldLife) table life =
  MkFiber component parent retired table life

public export
%hint
0 fiberComponentSetRuntime :
  (fiber : Fiber name key value world error) ->
  (table : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (life : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  fiberComponent (setFiberRuntime fiber table life) = fiberComponent fiber
fiberComponentSetRuntime (MkFiber component parent retired oldTable oldLife)
  table life = Refl

public export
%inline
setFiberLifecycle : (fiber : Fiber name key value world error) ->
  Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)) ->
  Fiber name key value world error
setFiberLifecycle fiber lifecycle = setFiberRuntime fiber (fiberTable fiber) lifecycle

public export
0 setFiberLifecycleExact :
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (oldLife, newLife : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  setFiberLifecycle (MkFiber component parent retiredFlag table oldLife) newLife =
    MkFiber component parent retiredFlag table newLife
setFiberLifecycleExact component parent retiredFlag table oldLife newLife = Refl

public export
0 fiberComponentSetLifecycle :
  (fiber : Fiber name key value world error) ->
  (life : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  fiberComponent (setFiberLifecycle fiber life) = fiberComponent fiber
fiberComponentSetLifecycle (MkFiber component parent retired table oldLife) life =
  Refl

public export
%inline
retireFiber : Fiber name key value world error -> Fiber name key value world error
retireFiber (MkFiber component parent retired table lifecycle) =
  MkFiber component parent True table lifecycle

public export
%hint
0 fiberComponentRetire :
  (fiber : Fiber name key value world error) ->
  fiberComponent (retireFiber fiber) = fiberComponent fiber
fiberComponentRetire (MkFiber component parent retired table lifecycle) = Refl

public export
FiberAt : (name, key : Type) -> (value : key -> Type) ->
  (world, error : Type) -> name -> Type
FiberAt name key value world error _ = Fiber name key value world error

||| Definition 45: finite name-unique registry.
public export
Registry : (name, key : Type) -> (value : key -> Type) ->
  (world, error : Type) -> Type
Registry name key value world error =
  CoeffectContext name (FiberAt name key value world error)

public export
record SystemState (name, key : Type) (value : key -> Type)
                   (world, error : Type) where
  constructor MkSystemState
  worldState : world
  registry : Registry name key value world error

public export
lookupFiber : DecEq name => name -> Registry name key value world error ->
  Maybe (Fiber name key value world error)
lookupFiber = lookupBinding

public export
registryFibers : Registry name key value world error ->
  List (Binding name (FiberAt name key value world error))
registryFibers = bindings

public export
parentPresent : DecEq name => Parent name -> Registry name key value world error -> Bool
parentPresent Root fibers = True
parentPresent (ChildOf parent) fibers = isJust (lookupFiber parent fibers)

public export
isChildOf : DecEq name => name ->
  Binding name (FiberAt name key value world error) -> Bool
isChildOf parent (Bind _ fiber) = case fiberParent fiber of
  Root => False
  ChildOf candidate => case decEq parent candidate of
    Yes Refl => True
    No _ => False

public export
hasChildIn : DecEq name => name ->
  List (Binding name (FiberAt name key value world error)) -> Bool
hasChildIn parent [] = False
hasChildIn parent (entry :: rest) = isChildOf parent entry || hasChildIn parent rest

public export
hasChild : DecEq name => name -> Registry name key value world error -> Bool
hasChild parent fibers = hasChildIn parent (registryFibers fibers)

0 justFiberInjective : Just left = Just right -> left = right
justFiberInjective Refl = Refl

0 childOfInjective : ChildOf left = ChildOf right -> left = right
childOfInjective Refl = Refl

0 rootNotChild : Root = ChildOf n -> Void
rootNotChild Refl impossible

0 trueNotFalse : True = False -> Void
trueNotFalse Refl impossible

0 childOfSelfTrue : (nameEq : DecEq name) -> (removed, current : name) ->
  (component : Component key value world error) -> (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  isChildOf @{nameEq} removed
    (Bind current (MkFiber component (ChildOf removed) retired table lifecycle)) = True
childOfSelfTrue nameEq removed current component retired table lifecycle
  with (decEq @{nameEq} removed removed)
  childOfSelfTrue nameEq removed current component retired table lifecycle |
    (Yes Refl) = Refl
  childOfSelfTrue nameEq removed current component retired table lifecycle |
    (No contra) = void (contra Refl)

0 boolOrLeftFalse : (left, right : Bool) -> left || right = False -> left = False
boolOrLeftFalse False right valid = Refl
boolOrLeftFalse True right valid = void (trueNotFalse valid)

0 boolOrRightFalse : (left, right : Bool) -> left || right = False -> right = False
boolOrRightFalse False False valid = Refl
boolOrRightFalse False True valid = void (trueNotFalse valid)
boolOrRightFalse True right valid = void (trueNotFalse valid)

0 noChildHeadParentDistinct :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (removed, current : name) ->
  (observed : Fiber name key value world error) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  hasChildIn @{nameEq} {key = key} {value = value} {world = world}
    {error = error} removed (Bind current observed :: rest) = False ->
  Not (fiberParent observed = ChildOf removed)
noChildHeadParentDistinct {key} {world} {error} {value} nameEq removed current
  (MkFiber component parent retired table lifecycle) rest noChild =
  case parent of
    Root => \same => rootNotChild same
    ChildOf candidate => case decEq @{nameEq} removed candidate of
      Yes Refl => \same =>
        let headFalse = boolOrLeftFalse
              (isChildOf @{nameEq} removed
                (Bind current (MkFiber component (ChildOf removed) retired table lifecycle)))
              (hasChildIn @{nameEq} removed rest) noChild
        in trueNotFalse (trans (sym (childOfSelfTrue nameEq removed current component
          retired table lifecycle)) headFalse)
      No distinct => \same => distinct (sym (childOfInjective same))

||| The executable no-child guard excludes the removed name as the parent of
||| every present fiber, including ancestors reached during a chain traversal.
public export
0 noChildLookupParentDistinct :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (removed, current : name) ->
  (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  hasChild @{nameEq} {key = key} {value = value} {world = world} {error = error} removed fibers = False ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} current fibers = Just fiber ->
  Not (fiberParent fiber = ChildOf removed)
0 noChildEntriesLookupParentDistinct :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (removed, current : name) ->
  (fiber : Fiber name key value world error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  hasChildIn @{nameEq} {key = key} {value = value} {world = world} {error = error} removed entries = False ->
  lookupEntries @{nameEq} {value = FiberAt name key value world error} current entries = Just fiber ->
  Not (fiberParent fiber = ChildOf removed)
noChildEntriesLookupParentDistinct {key} {world} {error} {value} nameEq removed current fiber [] noChild present =
  case present of Refl impossible
noChildEntriesLookupParentDistinct {name} {key} {world} {error} {value}
  nameEq removed current fiber (Bind found observed :: rest) noChild present
  with (decEq @{nameEq} current found)
  noChildEntriesLookupParentDistinct {name} {key} {world} {error} {value}
    nameEq removed found fiber (Bind found observed :: rest) noChild present |
    (Yes Refl) =
      replace {p = \candidate => Not (fiberParent candidate = ChildOf removed)}
        (justFiberInjective present)
        (noChildHeadParentDistinct nameEq removed found observed rest noChild)
  noChildEntriesLookupParentDistinct {name} {key} {world} {error} {value}
    nameEq removed current fiber (Bind found observed :: rest) noChild present |
    (No _) = noChildEntriesLookupParentDistinct {name = name} {key = key}
      {world = world} {error = error} {value = value} nameEq removed current fiber
      rest
      (boolOrRightFalse
        (isChildOf @{nameEq} removed (Bind found observed))
        (hasChildIn @{nameEq} {key = key} {value = value} {world = world} {error = error} removed rest) noChild)
      present

noChildLookupParentDistinct {name} {key} {world} {error} {value}
  nameEq removed current fiber (MkCoeffectContext entries unique) noChild present =
  noChildEntriesLookupParentDistinct {name = name} {key = key} {world = world}
    {error = error} {value = value} nameEq removed current fiber entries
    noChild present


public export
providerIn : DecEq name => DecEq key => key ->
  List (Binding name (FiberAt name key value world error)) -> Maybe name
providerIn k [] = Nothing
providerIn k (Bind n fiber :: rest) =
  if isActive (fiberLifecycle fiber) &&
     memberKey k (ownedValues (fiberTable fiber))
    then Just n
    else providerIn k rest

public export
providerOf : DecEq name => DecEq key => key ->
  Registry name key value world error -> Maybe name
providerOf k fibers = providerIn k (registryFibers fibers)

public export
resolveView : DecEq name => DecEq key => (deps : List key) ->
  Registry name key value world error -> Maybe (View name deps)
resolveView [] fibers = Just EmptyView
resolveView @{nameEq} @{keyEq} (k :: ks) fibers =
  case providerOf @{nameEq} @{keyEq} k fibers of
    Nothing => Nothing
    Just provider => map (ProviderView provider)
      (resolveView @{nameEq} @{keyEq} ks fibers)

public export
valueFromProvider : DecEq name => DecEq key => (provider : name) ->
  (k : key) -> Registry name key value world error -> Maybe (value k)
valueFromProvider provider k fibers = case lookupFiber provider fibers of
  Nothing => Nothing
  Just fiber => lookupBinding k (ownedValues (fiberTable fiber))

||| Inserting an empty Inactive fiber preserves every provider-table lookup.
public export
0 valueFromProviderInactiveInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider : name) -> (k : key) -> (n : name) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  valueFromProvider @{nameEq} @{keyEq} {value = value} {world = world} {error = error} provider k
    (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) =
  valueFromProvider @{nameEq} @{keyEq} {value = value} {world = world} {error = error} provider k fibers
valueFromProviderInactiveInsert {key} {world} {error} {value} nameEq keyEq provider k n component parent fibers absent
  with (decEq @{nameEq} provider n)
  valueFromProviderInactiveInsert {key} {world} {error} {value} nameEq keyEq n k n component parent fibers absent |
    (Yes Refl) =
      rewrite lookupInserted n (freshFiber component parent) fibers absent in
        rewrite absent in Refl
  valueFromProviderInactiveInsert {key} {world} {error} {value} nameEq keyEq provider k n component parent fibers absent |
    (No distinct) with (lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} provider fibers) proof present
    valueFromProviderInactiveInsert {key} {world} {error} {value} nameEq keyEq provider k n component parent fibers absent |
      (No distinct) | Nothing =
        rewrite lookupInsertOther provider n distinct (freshFiber component parent)
          fibers absent in rewrite present in Refl
    valueFromProviderInactiveInsert {key} {world} {error} {value} nameEq keyEq provider k n component parent fibers absent |
      (No distinct) | Just providerFiber =
        rewrite lookupInsertOther provider n distinct (freshFiber component parent)
          fibers absent in rewrite present in Refl

||| Resolve a committed capability directly through provider-owned tables.
||| Providers need only remain installed; they intentionally need not be Active
||| during a dependent's withdrawal interval.
public export
resolveCommittedValues : DecEq name => DecEq key =>
  (deps : List key) -> View name deps ->
  Registry name key value world error -> Maybe (DepValues key value deps)
resolveCommittedValues [] EmptyView fibers = Just NoDepValues
resolveCommittedValues @{nameEq} @{keyEq} (k :: ks) (ProviderView provider rest) fibers =
  case valueFromProvider @{nameEq} @{keyEq} provider k fibers of
    Nothing => Nothing
    Just v => map (OneDepValue v)
      (resolveCommittedValues @{nameEq} @{keyEq} ks rest fibers)

||| Inserting an empty Inactive fiber preserves every committed capability.
public export
0 resolveCommittedValuesInactiveInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  resolveCommittedValues @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps view
    (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) =
  resolveCommittedValues @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps view fibers
resolveCommittedValuesInactiveInsert {key} {world} {error} {value} nameEq keyEq [] EmptyView
  n component parent fibers absent = Refl
resolveCommittedValuesInactiveInsert {name} {key} {world} {error} {value}
  nameEq keyEq (k :: ks) (ProviderView provider rest)
  n component parent fibers absent
  with (valueFromProvider @{nameEq} @{keyEq} provider k fibers) proof original
  resolveCommittedValuesInactiveInsert {name} {key} {world} {error} {value}
    nameEq keyEq (k :: ks) (ProviderView provider rest)
    n component parent fibers absent | Nothing =
      let inserted = trans
            (valueFromProviderInactiveInsert {name = name} {key = key}
              {world = world} {error = error} {value = value}
              nameEq keyEq provider k n component parent fibers absent)
            original in rewrite inserted in Refl
  resolveCommittedValuesInactiveInsert {name} {key} {world} {error} {value}
    nameEq keyEq (k :: ks) (ProviderView provider rest)
    n component parent fibers absent | Just v =
      let inserted = trans
            (valueFromProviderInactiveInsert {name = name} {key = key}
              {world = world} {error = error} {value = value}
              nameEq keyEq provider k n component parent fibers absent)
            original in
      rewrite inserted in cong (map (OneDepValue v))
        (resolveCommittedValuesInactiveInsert {name = name} {key = key}
          {world = world} {error = error} {value = value}
          nameEq keyEq ks rest n component parent fibers absent)

||| Inserting a fresh Inactive fiber cannot become a provider or change any
||| existing target resolution.
public export
0 providerOfInactiveInsert : {name, key, world, error : Type} ->
  {value : key -> Type} -> (nameEq : DecEq name) -> (keyEq : DecEq key) -> (k : key) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  providerOf @{nameEq} @{keyEq} {value = value} {world = world} {error = error} k (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) =
    providerOf @{nameEq} @{keyEq} {value = value} {world = world} {error = error} k fibers
providerOfInactiveInsert nameEq keyEq k n component parent (MkCoeffectContext entries unique) absent =
  Refl

public export
0 resolveViewInactiveInsert : {name, key, world, error : Type} ->
  {value : key -> Type} -> (nameEq : DecEq name) -> (keyEq : DecEq key) -> (deps : List key) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  resolveView @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) =
    resolveView @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps fibers
resolveViewInactiveInsert nameEq keyEq [] n component parent fibers absent = Refl
resolveViewInactiveInsert {name} {key} {world} {error} {value} nameEq keyEq (k :: ks)
  n component parent fibers absent
  with (providerOf @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} k fibers) proof originalProvider
  resolveViewInactiveInsert {name} {key} {world} {error} {value}
    nameEq keyEq (k :: ks) n component parent fibers absent | Nothing =
      let insertedNone = trans
            (providerOfInactiveInsert {name = name} {key = key} {world = world}
              {error = error} {value = value} nameEq keyEq k n component parent fibers absent)
            originalProvider in
        rewrite insertedNone in Refl
  resolveViewInactiveInsert {name} {key} {world} {error} {value}
    nameEq keyEq (k :: ks) n component parent fibers absent | Just provider =
      let insertedJust = trans
            (providerOfInactiveInsert {name = name} {key = key} {world = world}
              {error = error} {value = value} nameEq keyEq k n component parent fibers absent)
            originalProvider in
      rewrite insertedJust in cong (map (ProviderView provider))
        (resolveViewInactiveInsert {name = name} {key = key}
          {world = world} {error = error} {value = value}
          nameEq keyEq ks n component parent fibers absent)

public export
activeCoeffectsFrom : DecEq name => DecEq key =>
  List (Binding name (FiberAt name key value world error)) ->
  CoeffectContext key value
activeCoeffectsFrom [] = emptyContext
activeCoeffectsFrom (Bind n fiber :: rest) =
  if isActive (fiberLifecycle fiber)
    then mergeOwned (ownedValues (fiberTable fiber))
                    (activeCoeffectsFrom rest)
    else activeCoeffectsFrom rest
  where
  mergeOwned : CoeffectContext key value -> CoeffectContext key value ->
               CoeffectContext key value
  mergeOwned left right = foldr insertIfFresh right (bindings left)
    where
    insertIfFresh : Binding key value -> CoeffectContext key value ->
                    CoeffectContext key value
    insertIfFresh (Bind k v) table = case setFresh k v table of
      Nothing => table
      Just applied => coeffectAfter applied

public export
activeCoeffects : DecEq name => DecEq key =>
  Registry name key value world error -> CoeffectContext key value
activeCoeffects fibers = activeCoeffectsFrom (registryFibers fibers)

||| Definition 46: target view.
public export
targetFiber : DecEq name => DecEq key =>
  (fiber : Fiber name key value world error) ->
  Registry name key value world error ->
  Maybe (View name (dependencies
    (componentDependencies (fiberComponent fiber))))
targetFiber fiber fibers = if retired fiber
  then Nothing
  else resolveView (dependencies (componentDependencies (fiberComponent fiber))) fibers

public export
0 targetFiberExplicit :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (fibers : Registry name key value world error) ->
  targetFiber @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} (MkFiber component parent retiredFlag table lifecycle) fibers =
  if retiredFlag then Nothing
  else resolveView @{nameEq} @{keyEq}
    (dependencies (componentDependencies component)) fibers
targetFiberExplicit nameEq keyEq component parent False table lifecycle fibers = Refl
targetFiberExplicit nameEq keyEq component parent True table lifecycle fibers = Refl

public export
data SomeView : Type -> Type where
  MkSomeView : View name deps -> SomeView name

public export
targetAt : DecEq name => DecEq key => name ->
  SystemState name key value world error -> Maybe (SomeView name)
targetAt n state = case lookupFiber n (registry state) of
  Nothing => Nothing
  Just fiber => map MkSomeView (targetFiber fiber (registry state))

public export
targetMatches : DecEq name => Maybe (View name deps) -> View name deps -> Bool
targetMatches Nothing view = False
targetMatches (Just target) view = viewEq target view

public export
reliedHead : DecEq name => name -> name ->
  Binding name (FiberAt name key value world error) -> Bool
reliedHead provider self (Bind n fiber) =
  let different = case decEq n self of Yes Refl => False; No _ => True
      sees = case committed (fiberLifecycle fiber) of
        Nothing => False
        Just view => viewContains provider view
  in different && installed (fiberLifecycle fiber) && sees

public export
reliedOnBy : DecEq name => name -> name ->
  List (Binding name (FiberAt name key value world error)) -> Bool
reliedOnBy provider self [] = False
reliedOnBy provider self (entry :: rest) =
  reliedHead provider self entry || reliedOnBy provider self rest

public export
relied : DecEq name => name -> Registry name key value world error -> Bool
relied n fibers = reliedOnBy n n (registryFibers fibers)

public export
quietFiber : DecEq name => DecEq key =>
  (fiber : Fiber name key value world error) ->
  Registry name key value world error -> Bool
quietFiber fiber fibers = case fiberLifecycle fiber of
  Inactive (Just _) => True
  Inactive Nothing => isNothing (targetFiber fiber fibers)
  Active accumulator view => targetMatches (targetFiber fiber fibers) view
  _ => False

public export
allRecursive : (a -> Bool) -> List a -> Bool
allRecursive predicate [] = True
allRecursive predicate (value :: rest) =
  predicate value && allRecursive predicate rest

public export
quietEntryFor : DecEq name => DecEq key =>
  Registry name key value world error ->
  Binding name (FiberAt name key value world error) -> Bool
quietEntryFor fibers (Bind _ fiber) = quietFiber fiber fibers

public export
quiet : DecEq name => DecEq key => SystemState name key value world error -> Bool
quiet state = allRecursive (quietEntryFor (registry state))
  (registryFibers (registry state))

public export
elemDec : DecEq a => a -> List a -> Bool
elemDec wanted [] = False
elemDec wanted (x :: xs) = case decEq wanted x of
  Yes Refl => True
  No _ => elemDec wanted xs

public export
removeName : DecEq a => a -> List a -> List a
removeName wanted [] = []
removeName wanted (x :: xs) with (decEq wanted x)
  removeName x (x :: xs) | (Yes Refl) = xs
  removeName wanted (x :: xs) | (No _) = x :: removeName wanted xs

public export
0 removeNamePresentLength : DecEq a => (wanted : a) -> (xs : List a) ->
  Elem wanted xs -> S (length (removeName wanted xs)) = length xs
removeNamePresentLength wanted [] present impossible
removeNamePresentLength wanted (x :: xs) present with (decEq wanted x)
  removeNamePresentLength x (x :: xs) present | (Yes Refl) = Refl
  removeNamePresentLength x (x :: xs) Here | (No distinct) =
    void (distinct Refl)
  removeNamePresentLength wanted (x :: xs) (There later) | (No _) =
    cong S (removeNamePresentLength wanted xs later)

public export
0 elemRemoveOtherName : DecEq a => (wanted, removed : a) ->
  Not (wanted = removed) -> (xs : List a) ->
  Elem wanted xs -> Elem wanted (removeName removed xs)
elemRemoveOtherName wanted removed distinct [] present impossible
elemRemoveOtherName wanted removed distinct (x :: xs) present
  with (decEq removed x)
  elemRemoveOtherName wanted x distinct (x :: xs) present | (Yes Refl) =
    case present of
      Here => void (distinct Refl)
      There later => later
  elemRemoveOtherName x removed distinct (x :: xs) Here | (No _) = Here
  elemRemoveOtherName wanted removed distinct (x :: xs) (There later) | (No _) =
    There (elemRemoveOtherName wanted removed distinct xs later)

public export
0 elemRemoveWasPresent : DecEq a => (wanted, removed : a) -> (xs : List a) ->
  Elem wanted (removeName removed xs) -> Elem wanted xs
elemRemoveWasPresent wanted removed [] present impossible
elemRemoveWasPresent wanted removed (x :: xs) present with (decEq removed x)
  elemRemoveWasPresent wanted x (x :: xs) present | (Yes Refl) = There present
  elemRemoveWasPresent x removed (x :: xs) Here | (No _) = Here
  elemRemoveWasPresent wanted removed (x :: xs) (There later) | (No _) =
    There (elemRemoveWasPresent wanted removed xs later)

public export
0 elemDecFalseNotElem : DecEq a => (wanted : a) -> (xs : List a) ->
  elemDec wanted xs = False -> Not (Elem wanted xs)
elemDecFalseNotElem wanted [] absent = \present => uninhabited present
elemDecFalseNotElem wanted (x :: xs) absent with (decEq wanted x)
  elemDecFalseNotElem x (x :: xs) absent | (Yes Refl) =
    case absent of Refl impossible
  elemDecFalseNotElem wanted (x :: xs) absent | (No distinct) = \present =>
    case present of
      Here => distinct Refl
      There later => elemDecFalseNotElem wanted xs absent later

0 elemLengthZeroImpossible : (xs : List a) -> length xs = Z -> Elem x xs -> Void
elemLengthZeroImpossible [] Refl present = uninhabited present
elemLengthZeroImpossible (_ :: _) Refl present impossible

public export
AvailableComplete : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) ->
  List name -> List name -> Registry name key value world error -> Type
AvailableComplete name key world error value nameEq seen available fibers =
  (candidate : name) -> Not (Elem candidate seen) ->
  (found : Fiber name key value world error) ->
  lookupFiber @{nameEq} candidate fibers = Just found -> Elem candidate available

public export
record AvailabilityShrink (name, key, world, error : Type)
  (value : key -> Type) (nameEq : DecEq name)
  (remaining : Nat) (available, seen : List name)
  (current, parent, removed : name)
  (target : Registry name key value world error) where
  constructor MkAvailabilityShrink
  0 shrinkLength : length (removeName current available) = remaining
  0 shrinkParent : Elem parent (removeName current available)
  0 shrinkRemovedAbsent : Not (Elem removed (removeName current available))
  0 shrinkComplete : AvailableComplete name key world error value nameEq
    (parent :: seen) (removeName current available) target

public export
0 shrinkAvailability :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (remaining : Nat) ->
  (available, seen : List name) -> (current, parent, removed : name) ->
  (target : Registry name key value world error) ->
  length available = S remaining -> Elem current available ->
  Not (Elem removed available) -> Elem current seen ->
  Not (Elem parent seen) -> Elem parent available ->
  AvailableComplete name key world error value nameEq seen available target ->
  AvailabilityShrink name key world error value nameEq remaining available seen
    current parent removed target
shrinkAvailability nameEq remaining available seen current parent removed target
  lengthOk currentAvailable removedAbsent currentSeen parentNotSeen parentAvailable
  complete =
  let parentCurrentDistinct : Not (parent = current)
      parentCurrentDistinct same = parentNotSeen
        (replace {p = \candidate => Elem candidate seen} (sym same) currentSeen)
      0 parentNext : Elem parent (removeName current available)
      parentNext = elemRemoveOtherName parent current parentCurrentDistinct
        available parentAvailable
      0 nextRemovedAbsent : Not (Elem removed (removeName current available))
      nextRemovedAbsent occurrence = removedAbsent
        (elemRemoveWasPresent removed current available occurrence)
      0 nextComplete : AvailableComplete name key world error value nameEq
        (parent :: seen) (removeName current available) target
      nextComplete candidate notSeen found foundLookup =
        let oldNotSeen : Not (Elem candidate seen)
            oldNotSeen occurrence = notSeen (There occurrence)
            candidateCurrentDistinct : Not (candidate = current)
            candidateCurrentDistinct same = notSeen
              (There (replace {p = \chosen => Elem chosen seen}
                (sym same) currentSeen))
        in elemRemoveOtherName candidate current candidateCurrentDistinct available
          (complete candidate oldNotSeen found foundLookup)
      0 removedLength : S (length (removeName current available)) =
        length available
      removedLength = removeNamePresentLength current available currentAvailable
      0 nextLength : length (removeName current available) = remaining
      nextLength = case trans removedLength lengthOk of Refl => Refl
  in MkAvailabilityShrink nextLength parentNext nextRemovedAbsent nextComplete

||| Appending a distinct fresh name does not change a failed membership test.
public export
0 elemDecAppendFresh : DecEq a => (wanted, fresh : a) -> (seen : List a) ->
  elemDec wanted seen = False -> Not (wanted = fresh) ->
  elemDec wanted (seen ++ [fresh]) = False
elemDecAppendFresh wanted fresh [] absent distinct with (decEq wanted fresh)
  elemDecAppendFresh fresh fresh [] absent distinct | (Yes Refl) = void (distinct Refl)
  elemDecAppendFresh wanted fresh [] absent distinct | (No _) = Refl
elemDecAppendFresh wanted fresh (x :: xs) absent distinct with (decEq wanted x)
  elemDecAppendFresh x fresh (x :: xs) absent distinct | (Yes Refl) =
    case absent of Refl impossible
  elemDecAppendFresh wanted fresh (x :: xs) absent distinct | (No _) =
    elemDecAppendFresh wanted fresh xs absent distinct

public export
provisionOverlap : DecEq key => CoeffectSpec key -> CoeffectSpec key -> Bool
provisionOverlap left right = any (\k => elemDec k (dependencies right))
                                  (dependencies left)

public export
provisionsDisjointFrom : DecEq key => CoeffectSpec key ->
  List (Binding name (FiberAt name key value world error)) -> Bool
provisionsDisjointFrom provision [] = True
provisionsDisjointFrom provision (Bind _ fiber :: rest) =
  not (provisionOverlap provision
    (componentProvisions (fiberComponent fiber))) &&
  provisionsDisjointFrom provision rest

||| The ten Table-1 rule tags.
public export
data RuleTag = OInsertTag | ORetireTag | ORemoveTag |
               LBeginTag | LIterTag | LFinishTag | LDivertTag |
               LRaiseTag | LLeaveTag | LUnloadTag

public export
data Action : (name, key : Type) -> (value : key -> Type) ->
              (world, error : Type) -> Type where
  OInsert : name -> Parent name -> Component key value world error ->
            Action name key value world error
  ORetire : name -> Action name key value world error
  ORemove : name -> Action name key value world error
  LBegin : name -> Action name key value world error
  LAdvance : name -> Action name key value world error
  LDivert : name -> Action name key value world error
  LLeave : name -> Action name key value world error
  LUnload : name -> Action name key value world error

||| Definition 47's host-visible checked forward/inverse pair.
public export
record Registration (name, key : Type) (value : key -> Type)
                    (world, error : Type) where
  constructor MkRegistration
  registrationForward : Action name key value world error
  registrationInverse : Action name key value world error

public export
registration : name -> Parent name -> Component key value world error ->
  Registration name key value world error
registration n parent component =
  MkRegistration (OInsert n parent component) (ORetire n)

public export
isInactive : Lifecycle key value world error name deps provision -> Bool
isInactive (Inactive _) = True
isInactive _ = False

public export
beginFiberAction : DecEq name => DecEq key => name ->
  Fiber name key value world error ->
  SystemState name key value world error ->
  Maybe (RuleTag, SystemState name key value world error)
beginFiberAction n fiber state = case fiberLifecycle fiber of
  Inactive Nothing => case targetFiber fiber (registry state) of
    Nothing => Nothing
    Just view => Just (LBeginTag,
      MkSystemState (worldState state)
        (replaceBinding n
          (setFiberLifecycle fiber
            (Reloading (componentProgram (fiberComponent fiber)) id view))
          (registry state)))
  _ => Nothing

||| Executable semantics for the ten rules. The empty-program terminal marker
||| obeys the same target equality as a non-empty L-Finish; stale targets divert.
public export
applyAction : DecEq name => DecEq key =>
  Action name key value world error ->
  SystemState name key value world error ->
  Maybe (RuleTag, SystemState name key value world error)
applyAction (OInsert n parent component) state =
  if parentPresent parent (registry state) &&
     provisionsDisjointFrom (componentProvisions component)
       (registryFibers (registry state))
    then case setFresh n (freshFiber component parent) (registry state) of
      Nothing => Nothing
      Just applied => Just (OInsertTag,
        MkSystemState (worldState state) (coeffectAfter applied))
    else Nothing
applyAction (ORetire n) state = case lookupFiber n (registry state) of
  Nothing => Nothing
  Just fiber => Just (ORetireTag,
    MkSystemState (worldState state)
      (replaceBinding n (retireFiber fiber) (registry state)))
applyAction (ORemove n) state = case lookupFiber n (registry state) of
  Nothing => Nothing
  Just fiber =>
    if retired fiber && isInactive (fiberLifecycle fiber) &&
       not (hasChild n (registry state))
      then Just (ORemoveTag,
        MkSystemState (worldState state) (deleteBinding n (registry state)))
      else Nothing
applyAction (LBegin n) state = case lookupFiber n (registry state) of
  Nothing => Nothing
  Just fiber => beginFiberAction n fiber state
applyAction (LAdvance n) state = case lookupFiber n (registry state) of
  Nothing => Nothing
  Just fiber => case fiberLifecycle fiber of
    Reloading [] accumulator view =>
      if targetMatches (targetFiber fiber (registry state)) view
        then Just (LFinishTag,
          MkSystemState (worldState state)
            (replaceBinding n
              (setFiberLifecycle fiber (Active accumulator view))
              (registry state)))
        else Just (LDivertTag,
          MkSystemState (worldState state)
            (replaceBinding n
              (setFiberLifecycle fiber (Unloading accumulator view Nothing))
              (registry state)))
    Reloading (step :: rest) accumulator view =>
      case resolveCommittedValues
        (dependencies (componentDependencies (fiberComponent fiber)))
        view (registry state) of
        Nothing => Nothing
        Just capability =>
          let normalizedTable = restrictOwnedPreservingOrder
                (componentProvisions (fiberComponent fiber))
                (ownedValues (fiberTable fiber))
              localBefore = MkLocalState (worldState state) normalizedTable in
          case runStepEffect step capability localBefore of
            Left err => Just (LRaiseTag,
              MkSystemState (worldState state)
                (replaceBinding n
                  (setFiberLifecycle fiber
                    (Unloading accumulator view (Just err)))
                  (registry state)))
            Right (localAfter, undo) =>
              let nextAccumulator = pushLocalUndo
                    (componentProvisions (fiberComponent fiber)) accumulator undo
                  nextWorld = localWorld localAfter
                  nextTable = localTable localAfter in
              if targetMatches (targetFiber fiber (registry state)) view
                then case rest of
                  [] => Just (LFinishTag,
                    MkSystemState nextWorld
                      (replaceBinding n
                        (setFiberRuntime fiber nextTable
                          (Active nextAccumulator view))
                        (registry state)))
                  _ => Just (LIterTag,
                    MkSystemState nextWorld
                      (replaceBinding n
                        (setFiberRuntime fiber nextTable
                          (Reloading rest nextAccumulator view))
                        (registry state)))
                else Just (LDivertTag,
                  MkSystemState nextWorld
                    (replaceBinding n
                      (setFiberRuntime fiber nextTable
                        (Unloading nextAccumulator view Nothing))
                      (registry state)))
    _ => Nothing
applyAction (LDivert n) state = case lookupFiber n (registry state) of
  Nothing => Nothing
  Just fiber => case fiberLifecycle fiber of
    Reloading remaining accumulator view =>
      if targetMatches (targetFiber fiber (registry state)) view
        then Nothing
        else Just (LDivertTag,
          MkSystemState (worldState state)
            (replaceBinding n
              (setFiberLifecycle fiber (Unloading accumulator view Nothing))
              (registry state)))
    _ => Nothing
applyAction (LLeave n) state = case lookupFiber n (registry state) of
  Nothing => Nothing
  Just fiber => case fiberLifecycle fiber of
    Active accumulator view =>
      if targetMatches (targetFiber fiber (registry state)) view
        then Nothing
        else Just (LLeaveTag,
          MkSystemState (worldState state)
            (replaceBinding n
              (setFiberLifecycle fiber (Unloading accumulator view Nothing))
              (registry state)))
    _ => Nothing
applyAction (LUnload n) state = case lookupFiber n (registry state) of
  Nothing => Nothing
  Just fiber => case fiberLifecycle fiber of
    Unloading accumulator view outcome =>
      if relied n (registry state)
        then Nothing
        else let normalizedTable = restrictOwnedPreservingOrder
                   (componentProvisions (fiberComponent fiber))
                   (ownedValues (fiberTable fiber))
                 restored = accumulator
                   (MkLocalState (worldState state) normalizedTable) in
          Just (LUnloadTag,
            MkSystemState (localWorld restored)
              (replaceBinding n
                (setFiberRuntime fiber (localTable restored) (Inactive outcome))
                (registry state)))
    _ => Nothing

public export
parentInvariant : DecEq name => Parent name -> Registry name key value world error -> Bool
parentInvariant Root fibers = True
parentInvariant (ChildOf parent) fibers = isJust (lookupFiber parent fibers)

public export
0 parentPresentIsInvariant : {name, key, world, error : Type} ->
  {value : key -> Type} -> (nameEq : DecEq name) -> (parent : Parent name) ->
  (fibers : Registry name key value world error) ->
  parentPresent @{nameEq} {key = key} {value = value} {world = world} {error = error}
    parent fibers =
  parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error}
    parent fibers
parentPresentIsInvariant {key} {world} {error} {value} nameEq Root fibers = Refl
parentPresentIsInvariant {key} {world} {error} {value}
  nameEq (ChildOf parent) fibers = Refl

public export
parentChainInvariant : DecEq name => Nat -> List name -> name ->
  Registry name key value world error -> Bool
parentChainInvariant Z seen current fibers = False
parentChainInvariant (S fuel) seen current fibers = case lookupFiber current fibers of
  Nothing => False
  Just fiber => case fiberParent fiber of
    Root => True
    ChildOf parent => if elemDec parent seen
      then False
      else parentChainInvariant fuel (parent :: seen) parent fibers

||| A committed provider may be Active or withdrawing, but never Inactive or
||| Reloading. In particular a Reloading fiber may mutate its table without
||| invalidating any already-committed consumer view.
public export
stableProvider : Lifecycle key value world error name deps provision -> Bool
stableProvider (Active _ _) = True
stableProvider (Unloading _ _ _) = True
stableProvider _ = False

public export
0 fiberStableProviderObservation :
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  stableProvider (fiberLifecycle
    (MkFiber component parent retiredFlag table lifecycle)) =
  stableProvider lifecycle
fiberStableProviderObservation component parent retiredFlag table
  (Inactive outcome) = Refl
fiberStableProviderObservation component parent retiredFlag table
  (Reloading remaining accumulator view) = Refl
fiberStableProviderObservation component parent retiredFlag table
  (Active accumulator view) = Refl
fiberStableProviderObservation component parent retiredFlag table
  (Unloading accumulator view outcome) = Refl


0 falseCannotBeTrue : False = True -> Void
falseCannotBeTrue Refl impossible

0 parentChainAbsentImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (fuel : Nat) -> (seen : List name) ->
  (current : name) -> (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} current fibers = Nothing ->
  parentChainInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fuel seen current fibers = True -> Void
parentChainAbsentImpossible {key} {world} {error} {value} nameEq Z seen current fibers absent valid =
  falseCannotBeTrue valid
parentChainAbsentImpossible {key} {world} {error} {value}
  nameEq (S fuel) seen current fibers absent valid
  with (lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} current fibers)
  parentChainAbsentImpossible {key} {world} {error} {value}
    nameEq (S fuel) seen current fibers absent valid | Nothing =
      falseCannotBeTrue valid
  parentChainAbsentImpossible {key} {world} {error} {value}
    nameEq (S fuel) seen current fibers absent valid | Just fiber =
      case absent of Refl impossible

||| Adding a globally absent name to the seen set cannot truncate a valid chain.
public export
0 parentChainAppendFresh :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (fuel : Nat) -> (seen : List name) ->
  (current, fresh : name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} fresh fibers = Nothing) ->
  Not (Elem fresh seen) -> Elem current seen ->
  parentChainInvariant @{nameEq} {key = key} {value = value}
    {world = world} {error = error} fuel seen current fibers = True ->
  parentChainInvariant @{nameEq} {key = key} {value = value}
    {world = world} {error = error} fuel (seen ++ [fresh]) current fibers = True
parentChainAppendFresh nameEq Z seen current fresh fibers absent notSeen currentSeen valid =
  void (falseCannotBeTrue valid)
parentChainAppendFresh {name} {key} {world} {error} {value}
  nameEq (S fuel) seen current fresh fibers absent notSeen currentSeen valid
  with (lookupFiber @{nameEq} current fibers) proof currentLookup
  parentChainAppendFresh {name} {key} {world} {error} {value}
    nameEq (S fuel) seen current fresh fibers absent notSeen currentSeen valid |
    Nothing = void (falseCannotBeTrue valid)
  parentChainAppendFresh {name} {key} {world} {error} {value}
    nameEq (S fuel) seen current fresh fibers absent notSeen currentSeen valid |
    Just currentFiber with (fiberParent currentFiber) proof parentShape
    parentChainAppendFresh {name} {key} {world} {error} {value}
      nameEq (S fuel) seen current fresh fibers absent notSeen currentSeen valid |
      Just currentFiber | Root =
        Refl
    parentChainAppendFresh {name} {key} {world} {error} {value}
      nameEq (S fuel) seen current fresh fibers absent notSeen currentSeen valid |
      Just currentFiber | ChildOf next
      with (elemDec @{nameEq} next seen) proof sourceSeen
      parentChainAppendFresh {name} {key} {world} {error} {value}
        nameEq (S fuel) seen current fresh fibers absent notSeen currentSeen valid |
        Just currentFiber | ChildOf next | True = void (falseCannotBeTrue valid)
      parentChainAppendFresh {name} {key} {world} {error} {value}
        nameEq (S fuel) seen current fresh fibers absent notSeen currentSeen valid |
        Just currentFiber | ChildOf next | False =
          case decEq @{nameEq} next fresh of
            Yes Refl => void (parentChainAbsentImpossible {key = key} {value = value}
              {world = world} {error = error} nameEq fuel (fresh :: seen) fresh
              fibers absent valid)
            No distinct =>
              let targetSeen = elemDecAppendFresh next fresh seen sourceSeen distinct
                  freshNotLater : Not (Elem fresh (next :: seen))
                  freshNotLater occurrence = case occurrence of
                    Here => distinct Refl
                    There later => notSeen later
              in rewrite targetSeen in
                parentChainAppendFresh {name = name} {key = key} {world = world}
                  {error = error} {value = value} nameEq fuel (next :: seen)
                  next fresh fibers absent freshNotLater Here valid

||| A fresh Inactive insertion preserves an existing parent chain. The `seen`
||| premise records that the fresh name cannot be an ancestor already visited.
public export
0 parentChainInactiveInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (fuel : Nat) -> (seen : List name) ->
  (current, n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} n fibers = Nothing) ->
  parentChainInvariant @{nameEq} {key = key} {value = value}
    {world = world} {error = error} fuel seen current fibers = True ->
  parentChainInvariant @{nameEq} {key = key} {value = value}
    {world = world} {error = error} fuel seen current
    (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) = True
parentChainInactiveInsert nameEq Z seen current n component parent fibers
  absent valid = void (falseCannotBeTrue valid)
parentChainInactiveInsert {name} {key} {world} {error} {value}
  nameEq (S fuel) seen current n component parent fibers absent valid
  with (lookupFiber @{nameEq} current fibers) proof currentLookup
  parentChainInactiveInsert {name} {key} {world} {error} {value}
    nameEq (S fuel) seen current n component parent fibers absent valid |
    Nothing = void (falseCannotBeTrue valid)
  parentChainInactiveInsert {name} {key} {world} {error} {value}
    nameEq (S fuel) seen current n component parent fibers absent valid |
    Just currentFiber with (fiberParent currentFiber) proof parentShape
    parentChainInactiveInsert {name} {key} {world} {error} {value}
      nameEq (S fuel) seen current n component parent fibers absent valid |
      Just currentFiber | Root =
        let distinct = presentAbsentDistinct current n fibers currentFiber
              currentLookup absent
            framed = lookupInsertOther current n distinct (freshFiber component parent)
              fibers absent
            inserted = trans framed currentLookup in
          rewrite inserted in rewrite parentShape in Refl
    parentChainInactiveInsert {name} {key} {world} {error} {value}
      nameEq (S fuel) seen current n component parent fibers absent valid |
      Just currentFiber | ChildOf next
      with (elemDec @{nameEq} next seen) proof seenNext
      parentChainInactiveInsert {name} {key} {world} {error} {value}
        nameEq (S fuel) seen current n component parent fibers absent valid |
        Just currentFiber | ChildOf next | True = void (falseCannotBeTrue valid)
      parentChainInactiveInsert {name} {key} {world} {error} {value}
        nameEq (S fuel) seen current n component parent fibers absent valid |
        Just currentFiber | ChildOf next | False =
          let distinct = presentAbsentDistinct current n fibers currentFiber
                currentLookup absent
              currentFramed = lookupInsertOther current n distinct
                (freshFiber component parent) fibers absent
              insertedCurrent = trans currentFramed currentLookup in
          case decEq @{nameEq} next n of
            Yes Refl =>
              rewrite insertedCurrent in rewrite parentShape in rewrite seenNext in
                void (parentChainAbsentImpossible {key = key} {value = value}
                  {world = world} {error = error} nameEq fuel (n :: seen) n
                  fibers absent valid)
            No nextDistinct =>
              rewrite insertedCurrent in rewrite parentShape in rewrite seenNext in
                parentChainInactiveInsert {name = name} {key = key}
                  {world = world} {error = error} {value = value}
                  nameEq fuel (next :: seen) next n component parent fibers absent valid

||| Parent-chain validity is monotone in fuel. Insertion raises the global fuel
||| by one, so existing chains remain certified.
public export
0 parentChainFuelMonotone : {name, key, world, error : Type} ->
  {value : key -> Type} -> (nameEq : DecEq name) -> (fuel : Nat) ->
  (seen : List name) -> (current : name) ->
  (fibers : Registry name key value world error) ->
  parentChainInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error}
    fuel seen current fibers = True ->
  parentChainInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error}
    (S fuel) seen current fibers = True
parentChainFuelMonotone nameEq Z seen current fibers valid =
  void (falseCannotBeTrue valid)
parentChainFuelMonotone nameEq (S fuel) seen current fibers valid
  with (lookupFiber @{nameEq} current fibers)
  parentChainFuelMonotone nameEq (S fuel) seen current fibers valid | Nothing =
    void (falseCannotBeTrue valid)
  parentChainFuelMonotone nameEq (S fuel) seen current fibers valid | Just fiber
    with (fiberParent fiber)
    parentChainFuelMonotone nameEq (S fuel) seen current fibers valid | Just fiber |
      Root = Refl
    parentChainFuelMonotone nameEq (S fuel) seen current fibers valid | Just fiber |
      ChildOf parent with (elemDec @{nameEq} parent seen)
      parentChainFuelMonotone nameEq (S fuel) seen current fibers valid | Just fiber |
        ChildOf parent | True = void (falseCannotBeTrue valid)
      parentChainFuelMonotone nameEq (S fuel) seen current fibers valid | Just fiber |
        ChildOf parent | False =
          parentChainFuelMonotone nameEq fuel (parent :: seen) parent fibers valid

public export
viewProvidersInvariant : DecEq name => Registry name key value world error ->
  View name deps -> Bool
viewProvidersInvariant fibers EmptyView = True
viewProvidersInvariant @{nameEq} fibers (ProviderView provider rest) =
  case lookupFiber @{nameEq} provider fibers of
    Nothing => False
    Just fiber => stableProvider (fiberLifecycle fiber) &&
                  viewProvidersInvariant @{nameEq} fibers rest

public export
0 viewProvidersInactiveInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (deps : List key) -> (view : View name deps) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  viewProvidersInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error}
    (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) view =
  viewProvidersInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fibers view
viewProvidersInactiveInsert {key} {world} {error} {value} nameEq [] EmptyView n component parent fibers absent = Refl
viewProvidersInactiveInsert {name} {key} {world} {error} {value}
  nameEq (k :: ks) (ProviderView provider rest) n component parent fibers absent
  with (decEq @{nameEq} provider n)
  viewProvidersInactiveInsert {name} {key} {world} {error} {value}
    nameEq (k :: ks) (ProviderView n rest) n component parent fibers absent |
    (Yes Refl) =
      rewrite lookupInserted n (freshFiber component parent) fibers absent in
        rewrite absent in Refl
  viewProvidersInactiveInsert {name} {key} {world} {error} {value}
    nameEq (k :: ks) (ProviderView provider rest) n component parent fibers absent |
    (No distinct) with (lookupFiber @{nameEq} {key = key} {value = value}
      {world = world} {error = error} provider fibers) proof original
    viewProvidersInactiveInsert {name} {key} {world} {error} {value}
      nameEq (k :: ks) (ProviderView provider rest) n component parent fibers absent |
      (No distinct) | Nothing =
        let inserted = trans
              (lookupInsertOther provider n distinct (freshFiber component parent)
                fibers absent) original in rewrite inserted in Refl
    viewProvidersInactiveInsert {name} {key} {world} {error} {value}
      nameEq (k :: ks) (ProviderView provider rest) n component parent fibers absent |
      (No distinct) | Just providerFiber =
        let inserted = trans
              (lookupInsertOther provider n distinct (freshFiber component parent)
                fibers absent) original in
        rewrite inserted in cong (stableProvider (fiberLifecycle providerFiber) &&)
          (viewProvidersInactiveInsert {name = name} {key = key}
            {world = world} {error = error} {value = value}
            nameEq ks rest n component parent fibers absent)

public export
viewBindingsInvariant : DecEq name => DecEq key => (deps : List key) ->
  View name deps -> Registry name key value world error -> Bool
viewBindingsInvariant @{nameEq} @{keyEq} deps view fibers =
  viewProvidersInvariant @{nameEq} fibers view &&
  isJust (resolveCommittedValues @{nameEq} @{keyEq} deps view fibers)

public export
0 viewBindingsInactiveInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} n fibers = Nothing) ->
  viewBindingsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps view
    (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) =
  viewBindingsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps view fibers
viewBindingsInactiveInsert {name} {key} {world} {error} {value}
  nameEq keyEq deps view n component parent fibers absent =
  rewrite viewProvidersInactiveInsert {name = name} {key = key}
    {world = world} {error = error} {value = value}
    nameEq deps view n component parent fibers absent in
  rewrite resolveCommittedValuesInactiveInsert {name = name} {key = key}
    {world = world} {error = error} {value = value}
    nameEq keyEq deps view n component parent fibers absent in Refl

public export
fiberViewInvariant : DecEq name => DecEq key =>
  Fiber name key value world error -> Registry name key value world error -> Bool
fiberViewInvariant @{nameEq} @{keyEq}
  (MkFiber component parent retired table lifecycle) fibers =
  case lifecycle of
    Inactive _ => True
    Reloading _ _ view => viewBindingsInvariant @{nameEq} @{keyEq}
      (dependencies (componentDependencies component)) view fibers
    Active _ view => viewBindingsInvariant @{nameEq} @{keyEq}
      (dependencies (componentDependencies component)) view fibers
    Unloading _ view _ => viewBindingsInvariant @{nameEq} @{keyEq}
      (dependencies (componentDependencies component)) view fibers

public export
0 fiberViewInactiveInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (fiber : Fiber name key value world error) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} n fibers = Nothing) ->
  fiberViewInvariant @{nameEq} @{keyEq} fiber
    (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) =
  fiberViewInvariant @{nameEq} @{keyEq} fiber fibers
fiberViewInactiveInsert {name} {key} {world} {error} {value}
  nameEq keyEq (MkFiber ownComponent ownParent retired table lifecycle)
  n component parent fibers absent = case lifecycle of
    Inactive outcome => Refl
    Reloading remaining accumulator view =>
      viewBindingsInactiveInsert {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq keyEq
        (dependencies (componentDependencies ownComponent)) view
        n component parent fibers absent
    Active accumulator view =>
      viewBindingsInactiveInsert {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq keyEq
        (dependencies (componentDependencies ownComponent)) view
        n component parent fibers absent
    Unloading accumulator view outcome =>
      viewBindingsInactiveInsert {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq keyEq
        (dependencies (componentDependencies ownComponent)) view
        n component parent fibers absent

public export
pairwiseProvisionInvariant : DecEq key =>
  List (Binding name (FiberAt name key value world error)) -> Bool
pairwiseProvisionInvariant [] = True
pairwiseProvisionInvariant @{keyEq} {value} {world} {error}
  (Bind _ fiber :: rest) =
  provisionsDisjointFrom @{keyEq} {value = value} {world = world} {error = error}
    (componentProvisions (fiberComponent fiber)) rest &&
  pairwiseProvisionInvariant @{keyEq}
    {value = value} {world = world} {error = error} rest

0 andTrueLeft : (left, right : Bool) -> left && right = True -> left = True
andTrueLeft False right equation = void (falseCannotBeTrue equation)
andTrueLeft True right equation = Refl

0 andTrueRight : (left, right : Bool) -> left && right = True -> right = True
andTrueRight False right equation = void (falseCannotBeTrue equation)
andTrueRight True False equation = void (falseCannotBeTrue equation)
andTrueRight True True equation = Refl

0 andBothTrue : (left, right : Bool) -> left = True -> right = True ->
  left && right = True
andBothTrue True True Refl Refl = Refl

0 andFourFirst : (a, b, c, d : Bool) ->
  a && b && c && d = True -> a = True
andFourFirst a b c d valid = andTrueLeft a (b && c && d) valid

0 andFourSecond : (a, b, c, d : Bool) ->
  a && b && c && d = True -> b = True
andFourSecond a b c d valid =
  andTrueLeft b (c && d) (andTrueRight a (b && c && d) valid)

0 andFourThird : (a, b, c, d : Bool) ->
  a && b && c && d = True -> c = True
andFourThird a b c d valid =
  andTrueLeft c d
    (andTrueRight b (c && d) (andTrueRight a (b && c && d) valid))

public export
0 andFourFourth : (a, b, c, d : Bool) ->
  a && b && c && d = True -> d = True
andFourFourth a b c d valid =
  andTrueRight c d
    (andTrueRight b (c && d) (andTrueRight a (b && c && d) valid))

0 freshFiberProvision : (component : Component key value world error) ->
  (parent : Parent name) ->
  componentProvisions (fiberComponent (freshFiber component parent)) =
    componentProvisions component
freshFiberProvision (MkComponent deps provision program) parent = Refl

0 pairwiseFreshConsEquation : {name, key, world, error : Type} ->
  {value : key -> Type} -> (keyEq : DecEq key) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  pairwiseProvisionInvariant @{keyEq} {value = value} {world = world} {error = error}
    (Bind n (freshFiber component parent) :: entries) =
  (provisionsDisjointFrom @{keyEq} {value = value} {world = world} {error = error} (componentProvisions component) entries &&
   pairwiseProvisionInvariant @{keyEq} {value = value} {world = world} {error = error} entries)
pairwiseFreshConsEquation {value} {world} {error} keyEq n (MkComponent deps provision program)
  parent entries = Refl

||| The O-Insert provision premise is exactly the new head clause.
public export
0 pairwiseProvisionInsert : {name, key, world, error : Type} ->
  {value : key -> Type} -> (keyEq : DecEq key) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  provisionsDisjointFrom @{keyEq} {value = value} {world = world} {error = error} (componentProvisions component) entries = True ->
  pairwiseProvisionInvariant @{keyEq} {value = value} {world = world} {error = error} entries = True ->
  pairwiseProvisionInvariant @{keyEq} {value = value} {world = world} {error = error} (Bind n (freshFiber component parent) :: entries) = True
pairwiseProvisionInsert {value} {world} {error} keyEq n
  component parent entries disjoint oldValid =
  trans
    (pairwiseFreshConsEquation {value = value} {world = world}
      {error = error} keyEq n component parent entries)
    (andBothTrue
      (provisionsDisjointFrom @{keyEq} {value = value} {world = world}
        {error = error} (componentProvisions component) entries)
      (pairwiseProvisionInvariant @{keyEq} {value = value} {world = world}
        {error = error} entries) disjoint oldValid)

public export
parentsInvariant : DecEq name =>
  List (Binding name (FiberAt name key value world error)) ->
  Registry name key value world error -> Bool
parentsInvariant [] fibers = True
parentsInvariant (Bind _ fiber :: rest) fibers =
  parentInvariant (fiberParent fiber) fibers && parentsInvariant rest fibers

||| Inserting an Inactive fresh fiber preserves every existing parent lookup.
public export
0 parentInvariantInactiveInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (parent : Parent name) ->
  (n : name) -> (component : Component key value world error) ->
  (newParent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} parent fibers = True ->
  parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} parent
    (insertBinding @{nameEq} n (freshFiber component newParent) fibers absent) = True
parentInvariantInactiveInsert {key} {world} {error} {value} nameEq Root n component newParent fibers absent valid = Refl
parentInvariantInactiveInsert {key} {world} {error} {value} nameEq (ChildOf parent) n component newParent fibers absent valid
  with (lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} parent fibers) proof present
  parentInvariantInactiveInsert {key} {world} {error} {value} nameEq (ChildOf parent) n component newParent fibers absent valid |
    Nothing = void (falseCannotBeTrue valid)
  parentInvariantInactiveInsert {key} {world} {error} {value} nameEq (ChildOf parent) n component newParent fibers absent valid |
    Just parentFiber =
      let distinct = presentAbsentDistinct parent n fibers parentFiber present absent
          framed = lookupInsertOther parent n distinct (freshFiber component newParent)
            fibers absent in
        rewrite framed in rewrite present in Refl

public export
0 parentsInvariantInactiveInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (component : Component key value world error) ->
  (newParent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} entries fibers = True ->
  parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} entries
    (insertBinding @{nameEq} n (freshFiber component newParent) fibers absent) = True
parentsInvariantInactiveInsert {key} {world} {error} {value} nameEq [] n component newParent fibers absent valid = Refl
parentsInvariantInactiveInsert {key} {world} {error} {value} nameEq (Bind current fiber :: rest)
  n component newParent fibers absent valid =
  andBothTrue
    (parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (fiberParent fiber)
      (insertBinding @{nameEq} n (freshFiber component newParent) fibers absent))
    (parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} rest
      (insertBinding @{nameEq} n (freshFiber component newParent) fibers absent))
    (parentInvariantInactiveInsert nameEq (fiberParent fiber) n component
      newParent fibers absent
      (andTrueLeft (parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (fiberParent fiber) fibers)
        (parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} rest fibers) valid))
    (parentsInvariantInactiveInsert nameEq rest n component newParent fibers absent
      (andTrueRight (parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (fiberParent fiber) fibers)
        (parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} rest fibers) valid))

public export
chainsInvariant : DecEq name => Nat ->
  List (Binding name (FiberAt name key value world error)) ->
  Registry name key value world error -> Bool
chainsInvariant fuel [] fibers = True
chainsInvariant {key} {value} {world} {error} fuel (Bind n _ :: rest) fibers =
  parentChainInvariant {key = key} {value = value} {world = world} {error = error}
    fuel [n] n fibers &&
  chainsInvariant {key = key} {value = value} {world = world} {error = error}
    fuel rest fibers

||| Extract the chain certificate for any name present in the checked entries.
public export
0 chainsInvariantLookup :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (fuel : Nat) -> (wanted : name) ->
  (fiber : Fiber name key value world error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (fibers : Registry name key value world error) ->
  lookupEntries @{nameEq} wanted entries = Just fiber ->
  chainsInvariant @{nameEq} {key = key} {value = value}
    {world = world} {error = error} fuel entries fibers = True ->
  parentChainInvariant @{nameEq} {key = key} {value = value}
    {world = world} {error = error} fuel [wanted] wanted fibers = True
chainsInvariantLookup nameEq fuel wanted fiber [] fibers present valid =
  case present of Refl impossible
chainsInvariantLookup {name} {key} {world} {error} {value}
  nameEq fuel wanted fiber (Bind current currentFiber :: rest) fibers present valid
  with (decEq @{nameEq} wanted current)
  chainsInvariantLookup {name} {key} {world} {error} {value}
    nameEq fuel current fiber (Bind current currentFiber :: rest) fibers present valid |
    (Yes Refl) =
      case present of
        Refl =>
          andTrueLeft
          (parentChainInvariant @{nameEq} {key = key} {value = value}
            {world = world} {error = error} fuel [current] current fibers)
          (chainsInvariant @{nameEq} {key = key} {value = value}
            {world = world} {error = error} fuel rest fibers) valid
  chainsInvariantLookup {name} {key} {world} {error} {value}
    nameEq fuel wanted fiber (Bind current currentFiber :: rest) fibers present valid |
    (No _) = chainsInvariantLookup {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq fuel wanted fiber rest fibers present
      (andTrueRight
        (parentChainInvariant @{nameEq} {key = key} {value = value}
          {world = world} {error = error} fuel [current] current fibers)
        (chainsInvariant @{nameEq} {key = key} {value = value}
          {world = world} {error = error} fuel rest fibers) valid)

0 newChildChainEquation : {name, key, world, error : Type} ->
  {value : key -> Type} -> (nameEq : DecEq name) -> (fuel : Nat) ->
  (n, parent : name) -> Not (parent = n) ->
  (component : Component key value world error) ->
  (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  parentChainInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (S fuel) [n] n
    (insertBinding @{nameEq} n (freshFiber component (ChildOf parent)) fibers absent) =
  parentChainInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fuel [parent, n] parent
    (insertBinding @{nameEq} n (freshFiber component (ChildOf parent)) fibers absent)
newChildChainEquation {key} {world} {error} {value} nameEq fuel n parent distinct component
  (MkCoeffectContext entries unique) absent with (decEq @{nameEq} n n)
  newChildChainEquation {key} {world} {error} {value} nameEq fuel n parent distinct component
    (MkCoeffectContext entries unique) absent | (Yes Refl)
    with (decEq @{nameEq} parent n)
    newChildChainEquation {key} {world} {error} {value} nameEq fuel n parent distinct component
      (MkCoeffectContext entries unique) absent | (Yes Refl) | (Yes same) =
        void (distinct same)
    newChildChainEquation {key} {world} {error} {value} nameEq fuel n parent distinct component
      (MkCoeffectContext entries unique) absent | (Yes Refl) | (No _) = Refl
  newChildChainEquation {key} {world} {error} {value} nameEq fuel n parent distinct component
    (MkCoeffectContext entries unique) absent | (No contra) = void (contra Refl)

public export
0 lookupFiberEntries : (nameEq : DecEq name) -> (wanted : name) ->
  (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} wanted fibers = Just fiber ->
  lookupEntries @{nameEq} wanted (bindings fibers) = Just fiber
lookupFiberEntries nameEq wanted fiber (MkCoeffectContext entries unique) found = found

||| The newly inserted fiber's parent chain is valid one fuel step above the
||| source registry's chain budget.
public export
0 newFiberParentChain :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (fuel : Nat) -> (n : name) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} parent fibers = True ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fuel (bindings fibers) fibers = True ->
  parentChainInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (S fuel) [n] n
    (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) = True
newFiberParentChain {key} {world} {error} {value} nameEq fuel n component Root fibers absent parentValid chainsValid =
  rewrite lookupInserted n (freshFiber component Root) fibers absent in Refl
newFiberParentChain {name} {key} {world} {error} {value}
  nameEq fuel n component (ChildOf parent) fibers absent parentValid chainsValid
  with (lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} parent fibers) proof parentLookup
  newFiberParentChain {name} {key} {world} {error} {value}
    nameEq fuel n component (ChildOf parent) fibers absent parentValid chainsValid |
    Nothing = void (falseCannotBeTrue parentValid)
  newFiberParentChain {name} {key} {world} {error} {value}
    nameEq fuel n component (ChildOf parent) fibers absent parentValid chainsValid |
    Just parentFiber =
      let distinct = presentAbsentDistinct parent n fibers parentFiber parentLookup absent
          sourceParent = chainsInvariantLookup {name = name} {key = key}
            {world = world} {error = error} {value = value} nameEq fuel parent
            parentFiber (bindings fibers) fibers
            (lookupFiberEntries nameEq parent parentFiber fibers parentLookup) chainsValid
          sourceWithFresh = parentChainAppendFresh {name = name} {key = key}
            {world = world} {error = error} {value = value} nameEq fuel [parent]
            parent n fibers absent
            (\occurrence => case occurrence of Here => distinct Refl)
            Here sourceParent
          targetParent = parentChainInactiveInsert {name = name} {key = key}
            {world = world} {error = error} {value = value} nameEq fuel [parent, n]
            parent n component (ChildOf parent) fibers absent sourceWithFresh in
        trans (newChildChainEquation {key = key} {value = value} {world = world} {error = error} nameEq fuel n parent distinct component
          fibers absent) targetParent

||| Lift fuel monotonicity pointwise over every registry entry.
public export
0 chainsFuelMonotone : {name, key, world, error : Type} ->
  {value : key -> Type} -> (nameEq : DecEq name) -> (fuel : Nat) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (fibers : Registry name key value world error) ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error}
    fuel entries fibers = True ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error}
    (S fuel) entries fibers = True
chainsFuelMonotone nameEq fuel [] fibers valid = Refl
chainsFuelMonotone {key} {world} {error} {value} nameEq fuel
  (Bind n fiber :: rest) fibers valid =
  let headValid = andTrueLeft
        (parentChainInvariant @{nameEq} {key = key} {value = value} {world = world}
          {error = error} fuel [n] n fibers)
        (chainsInvariant @{nameEq} {key = key} {value = value} {world = world}
          {error = error} fuel rest fibers) valid
      tailValid = andTrueRight
        (parentChainInvariant @{nameEq} {key = key} {value = value} {world = world}
          {error = error} fuel [n] n fibers)
        (chainsInvariant @{nameEq} {key = key} {value = value} {world = world}
          {error = error} fuel rest fibers) valid in
    andBothTrue
      (parentChainInvariant @{nameEq} {key = key} {value = value} {world = world}
        {error = error} (S fuel) [n] n fibers)
      (chainsInvariant @{nameEq} {key = key} {value = value} {world = world}
        {error = error} (S fuel) rest fibers)
      (parentChainFuelMonotone {key = key} {value = value}
        {world = world} {error = error} nameEq fuel [n] n fibers headValid)
      (chainsFuelMonotone {key = key} {value = value}
        {world = world} {error = error} nameEq fuel rest fibers tailValid)

||| Pointwise lift of the fresh-insertion frame over existing chain checks.
public export
0 chainsInactiveInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (fuel : Nat) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fuel entries fibers = True ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fuel entries
    (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) = True
chainsInactiveInsert {key} {world} {error} {value} nameEq fuel [] n component parent fibers absent valid = Refl
chainsInactiveInsert {name} {key} {world} {error} {value}
  nameEq fuel (Bind current fiber :: rest) n component parent fibers absent valid =
  let sourceHead = andTrueLeft
        (parentChainInvariant @{nameEq} {key = key} {value = value}
          {world = world} {error = error} fuel [current] current fibers)
        (chainsInvariant @{nameEq} {key = key} {value = value}
          {world = world} {error = error} fuel rest fibers) valid
      sourceTail = andTrueRight
        (parentChainInvariant @{nameEq} {key = key} {value = value}
          {world = world} {error = error} fuel [current] current fibers)
        (chainsInvariant @{nameEq} {key = key} {value = value}
          {world = world} {error = error} fuel rest fibers) valid
      targetHead = parentChainInactiveInsert {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq fuel [current]
        current n component parent fibers absent sourceHead
      targetTail = chainsInactiveInsert {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq fuel rest
        n component parent fibers absent sourceTail in
    andBothTrue _ _ targetHead targetTail

public export
viewsInvariant : DecEq name => DecEq key =>
  List (Binding name (FiberAt name key value world error)) ->
  Registry name key value world error -> Bool
viewsInvariant [] fibers = True
viewsInvariant @{nameEq} @{keyEq} (Bind _ fiber :: rest) fibers =
  fiberViewInvariant @{nameEq} @{keyEq} fiber fibers &&
  viewsInvariant @{nameEq} @{keyEq} rest fibers

public export
0 viewsInactiveInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries fibers = True ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries
    (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) = True
viewsInactiveInsert {key} {world} {error} {value} nameEq keyEq [] n component parent fibers absent valid = Refl
viewsInactiveInsert {name} {key} {world} {error} {value}
  nameEq keyEq (Bind current fiber :: rest) n component parent fibers absent valid =
  let oldHead = andTrueLeft
        (fiberViewInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} fiber fibers)
        (viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} rest fibers) valid
      oldTail = andTrueRight
        (fiberViewInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} fiber fibers)
        (viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} rest fibers) valid
      newHead = trans
        (fiberViewInactiveInsert {name = name} {key = key} {world = world}
          {error = error} {value = value} nameEq keyEq fiber n component parent
          fibers absent) oldHead
      newTail = viewsInactiveInsert {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq keyEq rest n component parent
        fibers absent oldTail in
    andBothTrue _ _ newHead newTail

||| Definition 58's executable registry invariant. Explicit recursive folds make
||| preservation frame proofs reusable and transparent.
public export
registryWellFormed : DecEq name => DecEq key =>
  SystemState name key value world error -> Bool
registryWellFormed state =
  let fibers = registry state
      entries = registryFibers fibers
      fuel = S (length entries)
   in parentsInvariant entries fibers &&
      chainsInvariant fuel entries fibers &&
      pairwiseProvisionInvariant entries && viewsInvariant entries fibers

0 registryFibersInserted : {name, key, world, error : Type} ->
  {value : key -> Type} -> (nameEq : DecEq name) -> (n : name) ->
  (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  registryFibers {value = value} {world = world} {error = error} (insertBinding @{nameEq} n fiber fibers absent) =
    Bind n fiber :: registryFibers {value = value} {world = world} {error = error} fibers
registryFibersInserted {key} {world} {error} {value} nameEq n fiber (MkCoeffectContext entries unique) absent = Refl

0 insertedWellFormedEquation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (ambient : world) ->
  (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
    (MkSystemState ambient
      (insertBinding @{nameEq} n (freshFiber component parent) fibers absent)) =
  (parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} parent
      (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) &&
   parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (registryFibers {value = value} {world = world} {error = error} fibers)
      (insertBinding @{nameEq} n (freshFiber component parent) fibers absent)) &&
  ((parentChainInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (S (S (length (registryFibers {value = value} {world = world} {error = error} fibers)))) [n] n
      (insertBinding @{nameEq} n (freshFiber component parent) fibers absent) &&
    chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (S (S (length (registryFibers {value = value} {world = world} {error = error} fibers))))
      (registryFibers {value = value} {world = world} {error = error} fibers)
      (insertBinding @{nameEq} n (freshFiber component parent) fibers absent)) &&
   (pairwiseProvisionInvariant @{keyEq} {value = value} {world = world} {error = error}
      (Bind n (freshFiber component parent) :: registryFibers {value = value} {world = world} {error = error} fibers) &&
    (True && viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (registryFibers {value = value} {world = world} {error = error} fibers)
      (insertBinding @{nameEq} n (freshFiber component parent) fibers absent))))
insertedWellFormedEquation {key} {world} {error} {value} nameEq keyEq n component parent ambient
  (MkCoeffectContext entries unique) absent = Refl

||| O-Insert preserves all four clauses of Definition 58.
public export
0 registryWellFormedInactiveInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (ambient : world) ->
  (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Nothing) ->
  parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} parent fibers = True ->
  provisionsDisjointFrom @{keyEq} {value = value} {world = world} {error = error} (componentProvisions component)
    (registryFibers {value = value} {world = world} {error = error} fibers) = True ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (MkSystemState ambient fibers) = True ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
    (MkSystemState ambient
      (insertBinding @{nameEq} n (freshFiber component parent) fibers absent)) = True
registryWellFormedInactiveInsert {name} {key} {world} {error} {value}
  nameEq keyEq n component parent ambient
  fibers@(MkCoeffectContext entries unique) absent parentValid disjoint valid =
  let sourceParents = andFourFirst
        (parentsInvariant @{nameEq} entries fibers)
        (chainsInvariant @{nameEq} (S (length entries)) entries fibers)
        (pairwiseProvisionInvariant @{keyEq} entries)
        (viewsInvariant @{nameEq} @{keyEq} entries fibers) valid
      sourceChains = andFourSecond
        (parentsInvariant @{nameEq} entries fibers)
        (chainsInvariant @{nameEq} (S (length entries)) entries fibers)
        (pairwiseProvisionInvariant @{keyEq} entries)
        (viewsInvariant @{nameEq} @{keyEq} entries fibers) valid
      sourcePairwise = andFourThird
        (parentsInvariant @{nameEq} entries fibers)
        (chainsInvariant @{nameEq} (S (length entries)) entries fibers)
        (pairwiseProvisionInvariant @{keyEq} entries)
        (viewsInvariant @{nameEq} @{keyEq} entries fibers) valid
      sourceViews = andFourFourth
        (parentsInvariant @{nameEq} entries fibers)
        (chainsInvariant @{nameEq} (S (length entries)) entries fibers)
        (pairwiseProvisionInvariant @{keyEq} entries)
        (viewsInvariant @{nameEq} @{keyEq} entries fibers) valid
      targetNewParent = parentInvariantInactiveInsert {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq parent n component
        parent fibers absent parentValid
      targetOldParents = parentsInvariantInactiveInsert {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq entries n component
        parent fibers absent sourceParents
      targetParents = andBothTrue _ _ targetNewParent targetOldParents
      sourceChainsRaised = chainsFuelMonotone {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq (S (length entries)) entries
        fibers sourceChains
      targetOldChains = chainsInactiveInsert {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq (S (S (length entries))) entries
        n component parent fibers absent sourceChainsRaised
      targetNewChain = newFiberParentChain {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq (S (length entries)) n component
        parent fibers absent parentValid sourceChains
      targetChains = andBothTrue _ _ targetNewChain targetOldChains
      targetPairwise = pairwiseProvisionInsert {name = name} {key = key}
        {world = world} {error = error} {value = value} keyEq n component parent
        entries disjoint sourcePairwise
      targetOldViews = viewsInactiveInsert {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq entries n
        component parent fibers absent sourceViews
      targetViews = andBothTrue _ _ Refl targetOldViews in
    trans (insertedWellFormedEquation {name = name} {key = key}
      {world = world} {error = error} {value = value} nameEq keyEq n component
      parent ambient fibers absent)
      (andBothTrue _ _ targetParents
        (andBothTrue _ _ targetChains
          (andBothTrue _ _ targetPairwise targetViews)))

0 retireFiberComponent : (fiber : Fiber name key value world error) ->
  fiberComponent (retireFiber fiber) = fiberComponent fiber
retireFiberComponent (MkFiber component parent retired table lifecycle) = Refl

0 retireFiberParent : (fiber : Fiber name key value world error) ->
  fiberParent (retireFiber fiber) = fiberParent fiber
retireFiberParent (MkFiber component parent retired table lifecycle) = Refl

||| Retirement changes only a flag not observed by the local clauses of
||| Definition 58. These projection equations seed the ORetire replacement fold.
public export
0 retireParentInvariant : {name, key, world, error : Type} ->
  {value : key -> Type} -> (nameEq : DecEq name) ->
  (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (fiberParent (retireFiber fiber)) fibers =
  parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (fiberParent fiber) fibers
retireParentInvariant {key} {world} {error} {value} nameEq (MkFiber component parent retired table lifecycle)
  fibers = Refl

||| Replacing a present fiber by its retired form preserves every parent lookup.
public export
0 parentInvariantRetireRegistry :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (parent : Parent name) -> (n : name) ->
  (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Just fiber ->
  parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} parent
    (replaceBinding @{nameEq} n (retireFiber fiber) fibers) =
  parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} parent fibers
parentInvariantRetireRegistry {key} {world} {error} {value} nameEq Root n fiber fibers present = Refl
parentInvariantRetireRegistry {name} {key} {world} {error} {value}
  nameEq (ChildOf parent) n fiber fibers@(MkCoeffectContext entries unique) present
  with (decEq @{nameEq} parent n)
  parentInvariantRetireRegistry {name} {key} {world} {error} {value}
    nameEq (ChildOf n) n fiber fibers@(MkCoeffectContext entries unique) present |
    (Yes Refl) =
      rewrite lookupReplaceEntries n fiber (retireFiber fiber) entries present in
      rewrite present in Refl
  parentInvariantRetireRegistry {name} {key} {world} {error} {value}
    nameEq (ChildOf parent) n fiber fibers@(MkCoeffectContext entries unique) present |
    (No distinct) = rewrite lookupReplaceOtherEntries parent n distinct
      (retireFiber fiber) entries in Refl

||| Committed views observe lifecycle stability, not the retirement flag.
public export
0 viewProvidersRetireRegistry :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (deps : List key) -> (view : View name deps) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  (present : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} n fibers = Just fiber) ->
  viewProvidersInvariant @{nameEq} {key = key} {value = value}
    {world = world} {error = error}
    (replaceBinding @{nameEq} n (retireFiber fiber) fibers) view =
  viewProvidersInvariant @{nameEq} {key = key} {value = value}
    {world = world} {error = error} fibers view
viewProvidersRetireRegistry nameEq [] EmptyView n fiber fibers present = Refl
viewProvidersRetireRegistry {name} {key} {world} {error} {value}
  nameEq (dep :: deps) (ProviderView provider rest) n fiber
  fibers@(MkCoeffectContext entries unique) present
  with (decEq @{nameEq} provider n)
  viewProvidersRetireRegistry {name} {key} {world} {error} {value}
    nameEq (dep :: deps) (ProviderView n rest) n
    fiber@(MkFiber ownComponent ownParent retired table lifecycle)
    fibers@(MkCoeffectContext entries unique) present | (Yes Refl) =
      rewrite lookupReplaceEntries n fiber (retireFiber fiber) entries present in
      rewrite present in
      cong (stableProvider lifecycle &&)
        (viewProvidersRetireRegistry {name = name} {key = key} {world = world}
          {error = error} {value = value} nameEq deps rest n
          (MkFiber ownComponent ownParent retired table lifecycle)
          (MkCoeffectContext entries unique) present)
  viewProvidersRetireRegistry {name} {key} {world} {error} {value}
    nameEq (dep :: deps) (ProviderView provider rest) n fiber
    fibers@(MkCoeffectContext entries unique) present | (No distinct)
    with (lookupEntries @{nameEq} provider entries) proof original
    viewProvidersRetireRegistry {name} {key} {world} {error} {value}
      nameEq (dep :: deps) (ProviderView provider rest) n fiber
      fibers@(MkCoeffectContext entries unique) present | (No distinct) | Nothing =
        rewrite lookupReplaceOtherEntries provider n distinct (retireFiber fiber)
          entries in rewrite original in Refl
    viewProvidersRetireRegistry {name} {key} {world} {error} {value}
      nameEq (dep :: deps) (ProviderView provider rest) n fiber
      fibers@(MkCoeffectContext entries unique) present | (No distinct) |
      Just providerFiber =
        rewrite lookupReplaceOtherEntries provider n distinct (retireFiber fiber)
          entries in rewrite original in
        cong (stableProvider (fiberLifecycle providerFiber) &&)
          (viewProvidersRetireRegistry {name = name} {key = key} {world = world}
            {error = error} {value = value} nameEq deps rest n fiber
            (MkCoeffectContext entries unique) present)

||| Retirement leaves every provider-owned value lookup unchanged.
public export
0 valueFromProviderRetireRegistry :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider : name) -> (k : key) -> (n : name) ->
  (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  (present : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} n fibers = Just fiber) ->
  valueFromProvider @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} provider k
    (replaceBinding @{nameEq} n (retireFiber fiber) fibers) =
  valueFromProvider @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} provider k fibers
valueFromProviderRetireRegistry {name} {key} {world} {error} {value}
  nameEq keyEq provider k n fiber fibers@(MkCoeffectContext entries unique) present
  with (decEq @{nameEq} provider n)
  valueFromProviderRetireRegistry {name} {key} {world} {error} {value}
    nameEq keyEq n k n
    fiber@(MkFiber component parent retired table lifecycle)
    fibers@(MkCoeffectContext entries unique) present | (Yes Refl) =
      rewrite lookupReplaceEntries n fiber (retireFiber fiber) entries present in
      rewrite present in Refl
  valueFromProviderRetireRegistry {name} {key} {world} {error} {value}
    nameEq keyEq provider k n fiber fibers@(MkCoeffectContext entries unique)
    present | (No distinct)
    with (lookupEntries @{nameEq} provider entries) proof original
    valueFromProviderRetireRegistry {name} {key} {world} {error} {value}
      nameEq keyEq provider k n fiber fibers@(MkCoeffectContext entries unique)
      present | (No distinct) | Nothing =
        rewrite lookupReplaceOtherEntries provider n distinct (retireFiber fiber)
          entries in rewrite original in Refl
    valueFromProviderRetireRegistry {name} {key} {world} {error} {value}
      nameEq keyEq provider k n fiber fibers@(MkCoeffectContext entries unique)
      present | (No distinct) | Just providerFiber =
        rewrite lookupReplaceOtherEntries provider n distinct (retireFiber fiber)
          entries in rewrite original in Refl

||| Retirement preserves every value in an already committed capability.
public export
0 resolveCommittedValuesRetireRegistry :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  (present : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} n fibers = Just fiber) ->
  resolveCommittedValues @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} deps view
    (replaceBinding @{nameEq} n (retireFiber fiber) fibers) =
  resolveCommittedValues @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} deps view fibers
resolveCommittedValuesRetireRegistry nameEq keyEq [] EmptyView
  n fiber fibers present = Refl
resolveCommittedValuesRetireRegistry {name} {key} {world} {error} {value}
  nameEq keyEq (k :: ks) (ProviderView provider rest) n fiber fibers present
  with (valueFromProvider @{nameEq} @{keyEq} provider k fibers) proof original
  resolveCommittedValuesRetireRegistry {name} {key} {world} {error} {value}
    nameEq keyEq (k :: ks) (ProviderView provider rest) n fiber fibers present |
    Nothing =
      let target = trans (valueFromProviderRetireRegistry {name = name} {key = key}
            {world = world} {error = error} {value = value} nameEq keyEq provider
            k n fiber fibers present) original in
        rewrite target in Refl
  resolveCommittedValuesRetireRegistry {name} {key} {world} {error} {value}
    nameEq keyEq (k :: ks) (ProviderView provider rest) n fiber fibers present |
    Just v =
      let target = trans (valueFromProviderRetireRegistry {name = name} {key = key}
            {world = world} {error = error} {value = value} nameEq keyEq provider
            k n fiber fibers present) original in
        rewrite target in cong (map (OneDepValue v))
          (resolveCommittedValuesRetireRegistry {name = name} {key = key}
            {world = world} {error = error} {value = value} nameEq keyEq ks rest
            n fiber fibers present)

public export
0 viewBindingsRetireRegistry :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  (present : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} n fibers = Just fiber) ->
  viewBindingsInvariant @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} deps view
    (replaceBinding @{nameEq} n (retireFiber fiber) fibers) =
  viewBindingsInvariant @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} deps view fibers
viewBindingsRetireRegistry {name} {key} {world} {error} {value}
  nameEq keyEq deps view n fiber fibers present =
  rewrite viewProvidersRetireRegistry {name = name} {key = key}
    {world = world} {error = error} {value = value} nameEq deps view n fiber
    fibers present in
  rewrite resolveCommittedValuesRetireRegistry {name = name} {key = key}
    {world = world} {error = error} {value = value} nameEq keyEq deps view n
    fiber fibers present in Refl

public export
0 fiberViewRetireRegistry :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (observed : Fiber name key value world error) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  (present : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} n fibers = Just fiber) ->
  fiberViewInvariant @{nameEq} @{keyEq} observed
    (replaceBinding @{nameEq} n (retireFiber fiber) fibers) =
  fiberViewInvariant @{nameEq} @{keyEq} observed fibers
fiberViewRetireRegistry {name} {key} {world} {error} {value}
  nameEq keyEq
  (MkFiber component parent retired table (Inactive outcome))
  n fiber fibers present = Refl
fiberViewRetireRegistry {name} {key} {world} {error} {value}
  nameEq keyEq
  (MkFiber component parent retired table (Reloading rest accumulator view))
  n fiber fibers present =
    viewBindingsRetireRegistry {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq keyEq
      (dependencies (componentDependencies component)) view n fiber fibers present
fiberViewRetireRegistry {name} {key} {world} {error} {value}
  nameEq keyEq
  (MkFiber component parent retired table (Active accumulator view))
  n fiber fibers present =
    viewBindingsRetireRegistry {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq keyEq
      (dependencies (componentDependencies component)) view n fiber fibers present
fiberViewRetireRegistry {name} {key} {world} {error} {value}
  nameEq keyEq
  (MkFiber component parent retired table (Unloading accumulator view outcome))
  n fiber fibers present =
    viewBindingsRetireRegistry {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq keyEq
      (dependencies (componentDependencies component)) view n fiber fibers present

||| Lift the parent lookup frame over a fixed entry list.
public export
0 parentsRegistryRetire :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  (present : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} n fibers = Just fiber) ->
  parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} entries fibers = True ->
  parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} entries
    (replaceBinding @{nameEq} n (retireFiber fiber) fibers) = True
parentsRegistryRetire {key} {world} {error} {value} nameEq [] n fiber fibers present valid = Refl
parentsRegistryRetire {name} {key} {world} {error} {value}
  nameEq (Bind current observed :: rest) n fiber fibers present valid =
    andBothTrue _ _
      (trans (parentInvariantRetireRegistry {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq
        (fiberParent observed) n fiber fibers present)
        (andTrueLeft _ _ valid))
      (parentsRegistryRetire {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq rest n fiber fibers present
        (andTrueRight _ _ valid))

||| Replacing the matching entry by its retired form preserves its parent field.
public export
0 parentsEntriesRetire :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (entries : List (Binding name
    (FiberAt name key value world error))) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (registry : Registry name key value world error) ->
  lookupEntries @{nameEq} {value = FiberAt name key value world error} n entries = Just fiber ->
  parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} entries registry = True ->
  parentsInvariant @{nameEq} {key = key} {value = value} {world = world}
    {error = error} (replaceEntries @{nameEq} n (retireFiber fiber) entries) registry = True
parentsEntriesRetire {key} {world} {error} {value} nameEq [] n fiber registry present valid =
  case present of Refl impossible
parentsEntriesRetire {name} {key} {world} {error} {value}
  nameEq (Bind current observed :: rest) n fiber registry present valid
  with (decEq @{nameEq} n current)
  parentsEntriesRetire {name} {key} {world} {error} {value}
    nameEq (Bind n observed :: rest) n fiber registry present valid | (Yes Refl) =
      case present of
        Refl =>
          andBothTrue _ _
            (trans (retireParentInvariant {name = name} {key = key}
            {world = world} {error = error} {value = value} nameEq observed registry)
              (andTrueLeft _ _ valid))
            (andTrueRight _ _ valid)
  parentsEntriesRetire {name} {key} {world} {error} {value}
    nameEq (Bind current observed :: rest) n fiber registry present valid |
    (No _) = andBothTrue _ _ (andTrueLeft _ _ valid)
      (parentsEntriesRetire {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq rest n fiber registry present
        (andTrueRight _ _ valid))

public export
0 retireProvisionInvariant : (fiber : Fiber name key value world error) ->
  componentProvisions (fiberComponent (retireFiber fiber)) =
  componentProvisions (fiberComponent fiber)
retireProvisionInvariant (MkFiber component parent retired table lifecycle) = Refl

0 justValuesEqual : Just x = Just y -> x = y
justValuesEqual Refl = Refl

0 nothingNotJust : {a : Type} -> {x : a} ->
  the (Maybe a) Nothing = Just x -> Void
nothingNotJust Refl impossible

||| Expose one parent-chain step without relying on reduction at call sites.
public export
0 parentChainStepEquation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (fuel : Nat) -> (seen : List name) ->
  (current : name) -> (fibers : Registry name key value world error) ->
  parentChainInvariant @{nameEq} {key = key} {value = value}
    {world = world} {error = error} (S fuel) seen current fibers =
  case lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} current fibers of
    Nothing => False
    Just fiber => case fiberParent fiber of
      Root => True
      ChildOf parent => if elemDec @{nameEq} parent seen
        then False else parentChainInvariant @{nameEq} {key = key}
          {value = value} {world = world} {error = error} fuel
          (parent :: seen) parent fibers
parentChainStepEquation nameEq fuel seen current
  (MkCoeffectContext entries unique) with (lookupEntries @{nameEq} current entries)
  parentChainStepEquation nameEq fuel seen current
    (MkCoeffectContext entries unique) | Nothing = Refl
  parentChainStepEquation nameEq fuel seen current
    (MkCoeffectContext entries unique) | Just fiber
    with (fiberParent fiber)
    parentChainStepEquation nameEq fuel seen current
      (MkCoeffectContext entries unique) | Just fiber | Root = Refl
    parentChainStepEquation nameEq fuel seen current
      (MkCoeffectContext entries unique) | Just fiber | ChildOf parent
      with (elemDec @{nameEq} parent seen)
      parentChainStepEquation nameEq fuel seen current
        (MkCoeffectContext entries unique) | Just fiber | ChildOf parent | True = Refl
      parentChainStepEquation nameEq fuel seen current
        (MkCoeffectContext entries unique) | Just fiber | ChildOf parent | False = Refl

public export
record RetireLookupFrame (nameEq : DecEq name) (current, n : name)
  (fiber, observed : Fiber name key value world error)
  (fibers : Registry name key value world error) where
  constructor MkRetireLookupFrame
  framedFiber : Fiber name key value world error
  0 framedLookup : lookupFiber @{nameEq} current
    (replaceBinding @{nameEq} n (retireFiber fiber) fibers) = Just framedFiber
  0 framedParent : fiberParent framedFiber = fiberParent observed

0 retireLookupFrame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (current, n : name) ->
  (fiber, observed : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} current fibers = Just observed ->
  lookupFiber @{nameEq} n fibers = Just fiber ->
  RetireLookupFrame nameEq current n fiber observed fibers
retireLookupFrame {name} {key} {world} {error} {value}
  nameEq current n fiber observed fibers@(MkCoeffectContext entries unique)
  currentLookup present with (decEq @{nameEq} current n)
  retireLookupFrame {name} {key} {world} {error} {value}
    nameEq n n fiber observed fibers@(MkCoeffectContext entries unique)
    currentLookup present | (Yes Refl) =
      case justValuesEqual (trans (sym currentLookup) present) of
        Refl => MkRetireLookupFrame (retireFiber fiber)
          (lookupReplaceEntries n fiber (retireFiber fiber) entries present)
          (retireFiberParent fiber)
  retireLookupFrame {name} {key} {world} {error} {value}
    nameEq current n fiber observed fibers@(MkCoeffectContext entries unique)
    currentLookup present | (No distinct) =
      MkRetireLookupFrame observed
        (trans (lookupReplaceOtherEntries current n distinct (retireFiber fiber)
          entries) currentLookup) Refl

||| Retirement preserves every fuel-bounded parent chain.
public export
0 parentChainRetireRegistry :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (fuel : Nat) -> (seen : List name) ->
  (current, n : name) -> (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  (present : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} n fibers = Just fiber) ->
  parentChainInvariant @{nameEq} {key = key} {value = value}
    {world = world} {error = error} fuel seen current fibers = True ->
  parentChainInvariant @{nameEq} {key = key} {value = value}
    {world = world} {error = error} fuel seen current
    (replaceBinding @{nameEq} n (retireFiber fiber) fibers) = True
parentChainRetireRegistry nameEq Z seen current n fiber fibers present valid =
  void (falseCannotBeTrue valid)
parentChainRetireRegistry {name} {key} {world} {error} {value}
  nameEq (S fuel) seen current n fiber fibers present valid
  with (lookupFiber @{nameEq} current fibers) proof currentLookup
  parentChainRetireRegistry {name} {key} {world} {error} {value}
    nameEq (S fuel) seen current n fiber fibers present valid | Nothing =
      void (falseCannotBeTrue valid)
  parentChainRetireRegistry {name} {key} {world} {error} {value}
    nameEq (S fuel) seen current n fiber fibers present valid | Just observed
    with (fiberParent observed) proof parentShape
    parentChainRetireRegistry {name} {key} {world} {error} {value}
      nameEq (S fuel) seen current n fiber fibers present valid | Just observed |
      Root =
        let frame = retireLookupFrame {name = name} {key = key} {world = world}
              {error = error} {value = value} nameEq current n fiber observed
              fibers currentLookup present in
        rewrite framedLookup frame in rewrite framedParent frame in
        rewrite parentShape in Refl
    parentChainRetireRegistry {name} {key} {world} {error} {value}
      nameEq (S fuel) seen current n fiber fibers present valid | Just observed |
      ChildOf parent with (elemDec @{nameEq} parent seen) proof parentSeen
      parentChainRetireRegistry {name} {key} {world} {error} {value}
        nameEq (S fuel) seen current n fiber fibers present valid | Just observed |
        ChildOf parent | True = void (falseCannotBeTrue valid)
      parentChainRetireRegistry {name} {key} {world} {error} {value}
        nameEq (S fuel) seen current n fiber fibers present valid | Just observed |
        ChildOf parent | False =
          let frame = retireLookupFrame {name = name} {key = key} {world = world}
                {error = error} {value = value} nameEq current n fiber observed
                fibers currentLookup present
              recursive = parentChainRetireRegistry {name = name} {key = key}
                {world = world} {error = error} {value = value} nameEq fuel
                (parent :: seen) parent n fiber fibers present valid in
          rewrite framedLookup frame in rewrite framedParent frame in
          rewrite parentShape in rewrite parentSeen in recursive

public export
0 chainsRegistryRetire :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (fuel : Nat) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  (present : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} n fibers = Just fiber) ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fuel entries fibers = True ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fuel entries
    (replaceBinding @{nameEq} n (retireFiber fiber) fibers) = True
chainsRegistryRetire {key} {world} {error} {value} nameEq fuel [] n fiber fibers present valid = Refl
chainsRegistryRetire {name} {key} {world} {error} {value}
  nameEq fuel (Bind current observed :: rest) n fiber fibers present valid =
  andBothTrue _ _
    (parentChainRetireRegistry {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq fuel [current] current n fiber
      fibers present (andTrueLeft _ _ valid))
    (chainsRegistryRetire {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq fuel rest n fiber fibers present
      (andTrueRight _ _ valid))

public export
0 chainsEntriesRetire :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (fuel : Nat) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (registry : Registry name key value world error) ->
  lookupEntries @{nameEq} {value = FiberAt name key value world error}
    n entries = Just fiber ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fuel entries registry = True ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fuel
    (replaceEntries @{nameEq} n (retireFiber fiber) entries) registry = True
chainsEntriesRetire {key} {world} {error} {value} nameEq fuel [] n fiber registry present valid =
  case present of Refl impossible
chainsEntriesRetire {name} {key} {world} {error} {value}
  nameEq fuel (Bind current observed :: rest) n fiber registry present valid
  with (decEq @{nameEq} n current)
  chainsEntriesRetire {name} {key} {world} {error} {value}
    nameEq fuel (Bind n observed :: rest) n fiber registry present valid |
    (Yes Refl) = case present of Refl => valid
  chainsEntriesRetire {name} {key} {world} {error} {value}
    nameEq fuel (Bind current observed :: rest) n fiber registry present valid |
    (No _) = andBothTrue _ _ (andTrueLeft _ _ valid)
      (chainsEntriesRetire {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq fuel rest n fiber registry present
        (andTrueRight _ _ valid))

public export
0 provisionsDisjointRetireEntries :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provision : CoeffectSpec key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  lookupEntries @{nameEq} {value = FiberAt name key value world error}
    n entries = Just fiber ->
  provisionsDisjointFrom @{keyEq} {value = value} {world = world} {error = error} provision
    (replaceEntries @{nameEq} n (retireFiber fiber) entries) =
  provisionsDisjointFrom @{keyEq} {value = value} {world = world} {error = error} provision entries
provisionsDisjointRetireEntries {world} {error} {value} nameEq keyEq provision [] n fiber present =
  case present of Refl impossible
provisionsDisjointRetireEntries {name} {key} {world} {error} {value}
  nameEq keyEq provision (Bind current observed :: rest) n fiber present
  with (decEq @{nameEq} n current)
  provisionsDisjointRetireEntries {name} {key} {world} {error} {value}
    nameEq keyEq provision (Bind n observed :: rest) n fiber present |
    (Yes Refl) = case present of
      Refl => rewrite retireProvisionInvariant observed in Refl
  provisionsDisjointRetireEntries {name} {key} {world} {error} {value}
    nameEq keyEq provision (Bind current observed :: rest) n fiber present |
    (No _) = cong
      (not (provisionOverlap @{keyEq} provision
        (componentProvisions (fiberComponent observed))) &&)
      (provisionsDisjointRetireEntries {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq provision
        rest n fiber present)

public export
0 pairwiseRetireEntries :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  lookupEntries @{nameEq} {value = FiberAt name key value world error}
    n entries = Just fiber ->
  pairwiseProvisionInvariant @{keyEq} {value = value} {world = world}
    {error = error} (replaceEntries @{nameEq} n (retireFiber fiber) entries) =
  pairwiseProvisionInvariant @{keyEq} {value = value} {world = world} {error = error} entries
pairwiseRetireEntries {world} {error} {value} nameEq keyEq [] n fiber present =
  case present of Refl impossible
pairwiseRetireEntries {name} {key} {world} {error} {value}
  nameEq keyEq (Bind current observed :: rest) n fiber present
  with (decEq @{nameEq} n current)
  pairwiseRetireEntries {name} {key} {world} {error} {value}
    nameEq keyEq (Bind n observed :: rest) n fiber present | (Yes Refl) =
      case present of Refl => rewrite retireProvisionInvariant observed in Refl
  pairwiseRetireEntries {name} {key} {world} {error} {value}
    nameEq keyEq (Bind current observed :: rest) n fiber present | (No _) =
      rewrite provisionsDisjointRetireEntries {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq
        (componentProvisions (fiberComponent observed)) rest n fiber present in
      cong (provisionsDisjointFrom @{keyEq}
        (componentProvisions (fiberComponent observed)) rest &&)
        (pairwiseRetireEntries {name = name} {key = key} {world = world}
          {error = error} {value = value} nameEq keyEq rest n fiber present)

public export
ParentStepValid : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> Nat -> List name ->
  Fiber name key value world error -> Registry name key value world error -> Type
ParentStepValid nameEq fuel seen fiber fibers = case fiberParent fiber of
  Root => True = True
  ChildOf parent => if elemDec @{nameEq} parent seen
    then False = True
    else parentChainInvariant @{nameEq} fuel (parent :: seen) parent fibers = True

0 reducedParentStepValid :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (fuel : Nat) -> (seen : List name) ->
  (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  (case fiberParent fiber of
    Root => True
    ChildOf parent => if elemDec @{nameEq} parent seen then False
      else parentChainInvariant @{nameEq} fuel (parent :: seen) parent fibers) =
    True ->
  ParentStepValid nameEq fuel seen fiber fibers
reducedParentStepValid nameEq fuel seen
  (MkFiber component Root retired table lifecycle) fibers valid = valid
reducedParentStepValid {name} nameEq fuel seen
  (MkFiber component (ChildOf parent) retired table lifecycle) fibers valid
  with (elemDec @{nameEq} parent seen)
  reducedParentStepValid nameEq fuel seen
    (MkFiber component (ChildOf parent) retired table lifecycle) fibers valid |
    True = valid
  reducedParentStepValid nameEq fuel seen
    (MkFiber component (ChildOf parent) retired table lifecycle) fibers valid |
    False = valid

0 normalizedChildParentStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (fuel : Nat) -> (parent : name) ->
  (seen : List name) -> (ancestor : name) ->
  (component : Component key value world error) -> (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (fibers : Registry name key value world error) ->
  (if (case decEq @{nameEq} ancestor parent of
        Yes Refl => True
        No _ => elemDec @{nameEq} ancestor seen)
    then False
    else parentChainInvariant @{nameEq} fuel (ancestor :: parent :: seen)
      ancestor fibers) = True ->
  ParentStepValid nameEq fuel (parent :: seen)
    (MkFiber component (ChildOf ancestor) retired table lifecycle) fibers
normalizedChildParentStep nameEq fuel parent seen ancestor component retired
  table lifecycle fibers valid with (decEq @{nameEq} ancestor parent)
  normalizedChildParentStep nameEq fuel parent seen parent component retired
    table lifecycle fibers valid | (Yes Refl) = valid
  normalizedChildParentStep nameEq fuel parent seen ancestor component retired
    table lifecycle fibers valid | (No distinct)
    with (elemDec @{nameEq} ancestor seen)
    normalizedChildParentStep nameEq fuel parent seen ancestor component retired
      table lifecycle fibers valid | (No distinct) | True = valid
    normalizedChildParentStep nameEq fuel parent seen ancestor component retired
      table lifecycle fibers valid | (No distinct) | False = valid

0 normalizedExposedParentStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (fuel : Nat) -> (parent : name) ->
  (seen : List name) -> (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  (case fiberParent fiber of
    Root => True
    ChildOf ancestor => if (case decEq @{nameEq} ancestor parent of
      Yes Refl => True
      No _ => elemDec @{nameEq} ancestor seen)
      then False else parentChainInvariant @{nameEq} fuel
        (ancestor :: parent :: seen) ancestor fibers) = True ->
  ParentStepValid nameEq fuel (parent :: seen) fiber fibers
normalizedExposedParentStep nameEq fuel parent seen
  (MkFiber component Root retired table lifecycle) fibers valid = valid
normalizedExposedParentStep nameEq fuel parent seen
  (MkFiber component (ChildOf ancestor) retired table lifecycle) fibers valid
  with (decEq @{nameEq} ancestor parent)
  normalizedExposedParentStep nameEq fuel parent seen
    (MkFiber component (ChildOf parent) retired table lifecycle) fibers valid |
    (Yes Refl) = valid
  normalizedExposedParentStep nameEq fuel parent seen
    (MkFiber component (ChildOf ancestor) retired table lifecycle) fibers valid |
    (No distinct) with (elemDec @{nameEq} ancestor seen)
    normalizedExposedParentStep nameEq fuel parent seen
      (MkFiber component (ChildOf ancestor) retired table lifecycle) fibers valid |
      (No distinct) | True = valid
    normalizedExposedParentStep nameEq fuel parent seen
      (MkFiber component (ChildOf ancestor) retired table lifecycle) fibers valid |
      (No distinct) | False = valid

||| One cardinality-controlled deletion step, assuming the current source
||| lookup has already been exposed. Recursion is structural on `remaining`.
public export
0 parentChainDeleteKnown :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (remaining : Nat) ->
  (available, seen : List name) -> (current, removed : name) ->
  (removedFiber, currentFiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  length available = S remaining -> Elem current available ->
  Not (Elem removed available) -> Elem current seen ->
  AvailableComplete name key world error value nameEq seen available
    (deleteBinding @{nameEq} removed fibers) ->
  hasChild @{nameEq} {key = key} {value = value} {world = world} {error = error} removed fibers = False ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} removed fibers = Just removedFiber ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} current fibers = Just currentFiber ->
  (case fiberParent currentFiber of
    Root => True
    ChildOf parent => if elemDec @{nameEq} parent seen then False
      else parentChainInvariant @{nameEq} {key = key} {value = value}
        {world = world} {error = error} (S remaining) (parent :: seen)
        parent fibers) = True ->
  parentChainInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (S remaining) seen current
    (deleteBinding @{nameEq} removed fibers) = True
parentChainDeleteKnown {name} {key} {world} {error} {value}
  nameEq Z available seen current removed removedFiber
  (MkFiber component Root retired table lifecycle) fibers
  lengthOk currentAvailable removedAbsent currentSeen complete noChild present
  currentLookup sourceValid =
    let currentDistinct : Not (current = removed)
        currentDistinct same = removedAbsent
          (replace {p = \candidate => Elem candidate available} same currentAvailable)
        targetLookup = trans
          (lookupDeleteOther current removed currentDistinct fibers) currentLookup
    in rewrite targetLookup in Refl
parentChainDeleteKnown {name} {key} {world} {error} {value}
  nameEq Z available seen current removed removedFiber
  (MkFiber component (ChildOf parent) retired table lifecycle) fibers
  lengthOk currentAvailable removedAbsent currentSeen complete noChild present
  currentLookup sourceValid
  with (elemDec @{nameEq} parent seen) proof parentSeen
  parentChainDeleteKnown {name} {key} {world} {error} {value}
    nameEq Z available seen current removed removedFiber
    (MkFiber component (ChildOf parent) retired table lifecycle) fibers
    lengthOk currentAvailable removedAbsent currentSeen complete noChild present
    currentLookup sourceValid | True = void (falseCannotBeTrue sourceValid)
  parentChainDeleteKnown {name} {key} {world} {error} {value}
    nameEq Z available seen current removed removedFiber
    (MkFiber component (ChildOf parent) retired table lifecycle) fibers
    lengthOk currentAvailable removedAbsent currentSeen complete noChild present
    currentLookup sourceValid | False
    with (lookupFiber @{nameEq} parent fibers) proof parentLookup
    parentChainDeleteKnown {name} {key} {world} {error} {value}
      nameEq Z available seen current removed removedFiber
      (MkFiber component (ChildOf parent) retired table lifecycle) fibers
      lengthOk currentAvailable removedAbsent currentSeen complete noChild present
      currentLookup sourceValid | False | Nothing =
        void (falseCannotBeTrue sourceValid)
    parentChainDeleteKnown {name} {key} {world} {error} {value}
      nameEq Z available seen current removed removedFiber
      (MkFiber component (ChildOf parent) retired table lifecycle) fibers
      lengthOk currentAvailable removedAbsent currentSeen complete noChild present
      currentLookup sourceValid | False | Just parentFiber =
        let 0 parentNotSeen : Not (Elem parent seen)
            parentNotSeen = elemDecFalseNotElem parent seen parentSeen
            0 parentNotRemoved : Not (parent = removed)
            parentNotRemoved = \same =>
              noChildLookupParentDistinct {name = name} {key = key}
                {world = world} {error = error} {value = value} nameEq removed
                current (MkFiber component (ChildOf parent) retired table lifecycle)
                fibers noChild currentLookup (cong ChildOf same)
            targetParentLookup = trans
              (lookupDeleteOther parent removed parentNotRemoved fibers) parentLookup
            0 parentAvailable : Elem parent available
            parentAvailable = complete parent parentNotSeen parentFiber
              targetParentLookup
            0 shrunk : AvailabilityShrink name key world error value nameEq Z
              available seen current parent removed
              (deleteBinding @{nameEq} removed fibers)
            shrunk = shrinkAvailability {name = name} {key = key}
              {world = world} {error = error} {value = value} nameEq Z available
              seen current parent removed (deleteBinding @{nameEq} removed fibers)
              lengthOk currentAvailable removedAbsent currentSeen parentNotSeen
              parentAvailable complete
        in void (elemLengthZeroImpossible (removeName current available)
          (shrinkLength shrunk) (shrinkParent shrunk))
parentChainDeleteKnown {name} {key} {world} {error} {value}
  nameEq (S remaining) available seen current removed removedFiber
  (MkFiber component Root retired table lifecycle) fibers
  lengthOk currentAvailable removedAbsent currentSeen complete noChild present
  currentLookup sourceValid =
    let currentDistinct : Not (current = removed)
        currentDistinct same = removedAbsent
          (replace {p = \candidate => Elem candidate available} same currentAvailable)
        targetLookup = trans
          (lookupDeleteOther current removed currentDistinct fibers) currentLookup
    in rewrite targetLookup in Refl
parentChainDeleteKnown {name} {key} {world} {error} {value}
  nameEq (S remaining) available seen current removed removedFiber
  (MkFiber component (ChildOf parent) retired table lifecycle) fibers
  lengthOk currentAvailable removedAbsent currentSeen complete noChild present
  currentLookup sourceValid
  with (elemDec @{nameEq} parent seen) proof parentSeen
  parentChainDeleteKnown {name} {key} {world} {error} {value}
    nameEq (S remaining) available seen current removed removedFiber (MkFiber component (ChildOf parent) retired table lifecycle)
    fibers lengthOk currentAvailable removedAbsent currentSeen complete noChild
    present currentLookup sourceValid | True = void (falseCannotBeTrue sourceValid)
  parentChainDeleteKnown {name} {key} {world} {error} {value}
    nameEq (S remaining) available seen current removed removedFiber (MkFiber component (ChildOf parent) retired table lifecycle)
    fibers lengthOk currentAvailable removedAbsent currentSeen complete noChild
    present currentLookup sourceValid | False
    with (lookupFiber @{nameEq} parent fibers) proof parentLookup
    parentChainDeleteKnown {name} {key} {world} {error} {value}
      nameEq (S remaining) available seen current removed removedFiber (MkFiber component (ChildOf parent) retired table lifecycle)
      fibers lengthOk currentAvailable removedAbsent currentSeen complete noChild
      present currentLookup sourceValid | False | Nothing =
        void (falseCannotBeTrue sourceValid)
    parentChainDeleteKnown {name} {key} {world} {error} {value}
      nameEq (S remaining) available seen current removed removedFiber (MkFiber component (ChildOf parent) retired table lifecycle)
      fibers lengthOk currentAvailable removedAbsent currentSeen complete noChild
      present currentLookup sourceValid | False | Just parentFiber with (fiberParent parentFiber) proof nextParentShape
      parentChainDeleteKnown {name} {key} {world} {error} {value}
        nameEq (S remaining) available seen current removed removedFiber (MkFiber component (ChildOf parent) retired table lifecycle)
        fibers lengthOk currentAvailable removedAbsent currentSeen complete noChild
        present currentLookup sourceValid | False | Just parentFiber | Root =
          let currentDistinct : Not (current = removed)
              currentDistinct same = removedAbsent
                (replace {p = \candidate => Elem candidate available} same
                  currentAvailable)
              targetLookup = trans
                (lookupDeleteOther current removed currentDistinct fibers) currentLookup
              0 parentNotSeen : Not (Elem parent seen)
              parentNotSeen = elemDecFalseNotElem parent seen parentSeen
              0 parentNotRemoved : Not (parent = removed)
              parentNotRemoved = \same =>
                noChildLookupParentDistinct {name = name} {key = key}
                  {world = world} {error = error} {value = value} nameEq removed
                  current (MkFiber component (ChildOf parent) retired table lifecycle) fibers noChild currentLookup
                  (cong ChildOf same)
              targetParentLookup = trans
                (lookupDeleteOther parent removed parentNotRemoved fibers) parentLookup
              0 parentAvailable : Elem parent available
              parentAvailable = complete parent parentNotSeen parentFiber
                targetParentLookup
              0 shrunk : AvailabilityShrink name key world error value nameEq
                (S remaining) available seen current parent removed
                (deleteBinding @{nameEq} removed fibers)
              shrunk = shrinkAvailability {name = name} {key = key}
                {world = world} {error = error} {value = value} nameEq (S remaining)
                available seen current parent removed
                (deleteBinding @{nameEq} removed fibers) lengthOk currentAvailable
                removedAbsent currentSeen parentNotSeen parentAvailable complete
          in rewrite targetLookup in rewrite parentSeen in
            parentChainDeleteKnown {name = name} {key = key} {world = world}
              {error = error} {value = value} nameEq remaining
              (removeName current available) (parent :: seen) parent removed
              removedFiber parentFiber fibers (shrinkLength shrunk)
              (shrinkParent shrunk) (shrinkRemovedAbsent shrunk) Here
              (shrinkComplete shrunk) noChild present parentLookup
              (rewrite nextParentShape in Refl)
      parentChainDeleteKnown {name} {key} {world} {error} {value}
        nameEq (S remaining) available seen current removed removedFiber (MkFiber component (ChildOf parent) retired table lifecycle)
        fibers lengthOk currentAvailable removedAbsent currentSeen complete noChild
        present currentLookup sourceValid | False | Just parentFiber | ChildOf ancestor with (elemDec @{nameEq} ancestor (parent :: seen)) proof ancestorSeen
        parentChainDeleteKnown {name} {key} {world} {error} {value}
          nameEq (S remaining) available seen current removed removedFiber (MkFiber component (ChildOf parent) retired table lifecycle)
          fibers lengthOk currentAvailable removedAbsent currentSeen complete noChild
          present currentLookup sourceValid | False | Just parentFiber | ChildOf ancestor | True =
            void (falseCannotBeTrue sourceValid)
        parentChainDeleteKnown {name} {key} {world} {error} {value}
          nameEq (S remaining) available seen current removed removedFiber (MkFiber component (ChildOf parent) retired table lifecycle)
          fibers lengthOk currentAvailable removedAbsent currentSeen complete noChild
          present currentLookup sourceValid | False | Just parentFiber | ChildOf ancestor | False =
            let currentDistinct : Not (current = removed)
                currentDistinct same = removedAbsent
                  (replace {p = \candidate => Elem candidate available} same
                    currentAvailable)
                targetLookup = trans
                  (lookupDeleteOther current removed currentDistinct fibers) currentLookup
                0 parentNotSeen : Not (Elem parent seen)
                parentNotSeen = elemDecFalseNotElem parent seen parentSeen
                0 parentNotRemoved : Not (parent = removed)
                parentNotRemoved = \same =>
                  noChildLookupParentDistinct {name = name} {key = key}
                    {world = world} {error = error} {value = value} nameEq removed
                    current (MkFiber component (ChildOf parent) retired table lifecycle) fibers noChild currentLookup
                    (cong ChildOf same)
                targetParentLookup = trans
                  (lookupDeleteOther parent removed parentNotRemoved fibers) parentLookup
                0 parentAvailable : Elem parent available
                parentAvailable = complete parent parentNotSeen parentFiber
                  targetParentLookup
                0 shrunk : AvailabilityShrink name key world error value nameEq
                  (S remaining) available seen current parent removed
                  (deleteBinding @{nameEq} removed fibers)
                shrunk = shrinkAvailability {name = name} {key = key}
                  {world = world} {error = error} {value = value} nameEq (S remaining)
                  available seen current parent removed
                  (deleteBinding @{nameEq} removed fibers) lengthOk currentAvailable
                  removedAbsent currentSeen parentNotSeen parentAvailable complete
            in rewrite targetLookup in rewrite parentSeen in
              parentChainDeleteKnown {name = name} {key = key} {world = world}
                {error = error} {value = value} nameEq remaining
                (removeName current available) (parent :: seen) parent removed
                removedFiber parentFiber fibers (shrinkLength shrunk)
                (shrinkParent shrunk) (shrinkRemovedAbsent shrunk) Here
                (shrinkComplete shrunk) noChild present parentLookup
                (rewrite nextParentShape in rewrite ancestorSeen in sourceValid)

||| Expose the source lookup and discharge the known-fiber cardinal step.
public export
0 parentChainDeleteAvailable :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (remaining : Nat) ->
  (available, seen : List name) -> (current, removed : name) ->
  (removedFiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  length available = S remaining -> Elem current available ->
  Not (Elem removed available) -> Elem current seen ->
  AvailableComplete name key world error value nameEq seen available
    (deleteBinding @{nameEq} removed fibers) ->
  hasChild @{nameEq} {key = key} {value = value} {world = world} {error = error} removed fibers = False ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} removed fibers = Just removedFiber ->
  parentChainInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (S (S remaining)) seen current fibers = True ->
  parentChainInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (S remaining) seen current
    (deleteBinding @{nameEq} removed fibers) = True
parentChainDeleteAvailable {name} {key} {world} {error} {value}
  nameEq remaining available seen current removed removedFiber fibers lengthOk
  currentAvailable removedAbsent currentSeen complete noChild present valid
  with (lookupFiber @{nameEq} current fibers) proof currentLookup
  parentChainDeleteAvailable {name} {key} {world} {error} {value}
    nameEq remaining available seen current removed removedFiber fibers lengthOk
    currentAvailable removedAbsent currentSeen complete noChild present valid |
    Nothing = void (falseCannotBeTrue valid)
  parentChainDeleteAvailable {name} {key} {world} {error} {value}
    nameEq remaining available seen current removed removedFiber fibers lengthOk
    currentAvailable removedAbsent currentSeen complete noChild present valid |
    Just currentFiber with (fiberParent currentFiber) proof parentShape
    parentChainDeleteAvailable {name} {key} {world} {error} {value}
      nameEq remaining available seen current removed removedFiber fibers lengthOk
      currentAvailable removedAbsent currentSeen complete noChild present valid |
      Just currentFiber | Root =
        parentChainDeleteKnown {name = name} {key = key} {world = world}
          {error = error} {value = value} nameEq remaining available seen current
          removed removedFiber currentFiber fibers lengthOk currentAvailable
          removedAbsent currentSeen complete noChild present currentLookup
          (rewrite parentShape in Refl)
    parentChainDeleteAvailable {name} {key} {world} {error} {value}
      nameEq remaining available seen current removed removedFiber fibers lengthOk
      currentAvailable removedAbsent currentSeen complete noChild present valid |
      Just currentFiber | ChildOf parent
      with (elemDec @{nameEq} parent seen) proof parentSeen
      parentChainDeleteAvailable {name} {key} {world} {error} {value}
        nameEq remaining available seen current removed removedFiber fibers lengthOk
        currentAvailable removedAbsent currentSeen complete noChild present valid |
        Just currentFiber | ChildOf parent | True =
          void (falseCannotBeTrue valid)
      parentChainDeleteAvailable {name} {key} {world} {error} {value}
        nameEq remaining available seen current removed removedFiber fibers lengthOk
        currentAvailable removedAbsent currentSeen complete noChild present valid |
        Just currentFiber | ChildOf parent | False =
          parentChainDeleteKnown {name = name} {key = key} {world = world}
            {error = error} {value = value} nameEq remaining available seen current
            removed removedFiber currentFiber fibers lengthOk currentAvailable
            removedAbsent currentSeen complete noChild present currentLookup
            (rewrite parentShape in rewrite parentSeen in valid)

0 bindingKeyElem : (entry : Binding key value) ->
  (entries : List (Binding key value)) ->
  Elem entry entries -> Elem (bindingKey entry) (bindingKeys entries)
bindingKeyElem entry [] present impossible
bindingKeyElem entry (entry :: rest) Here = Here
bindingKeyElem entry (other :: rest) (There later) =
  There (bindingKeyElem entry rest later)

0 localLookupJustElem : DecEq key => (wanted : key) ->
  (entries : List (Binding key value)) -> (found : value wanted) ->
  lookupEntries wanted entries = Just found -> Elem wanted (bindingKeys entries)
localLookupJustElem wanted [] found present = case present of Refl impossible
localLookupJustElem wanted (Bind current value :: rest) found present
  with (decEq wanted current)
  localLookupJustElem current (Bind current value :: rest) found present |
    (Yes Refl) = Here
  localLookupJustElem wanted (Bind current value :: rest) found present |
    (No _) = There (localLookupJustElem wanted rest found present)

0 registryAvailabilityComplete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (seen : List name) ->
  (fibers : Registry name key value world error) ->
  AvailableComplete name key world error value nameEq seen
    (bindingKeys (registryFibers {value = value} {world = world} {error = error} fibers)) fibers
registryAvailabilityComplete {key} {world} {error} {value} nameEq seen fibers candidate notSeen found present =
  localLookupJustElem candidate (registryFibers {value = value} {world = world} {error = error} fibers) found
    (lookupFiberEntries nameEq candidate found fibers present)

||| Deleting an entry from the checked list leaves every remaining source chain
||| certificate available at the original fuel.
public export
0 chainsEntriesDeleteSameRegistry :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (fuel : Nat) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (removed : name) -> (fibers : Registry name key value world error) ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fuel entries fibers = True ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fuel (deleteEntries @{nameEq} removed entries)
    fibers = True
chainsEntriesDeleteSameRegistry {key} {world} {error} {value} nameEq fuel [] removed fibers valid = Refl
chainsEntriesDeleteSameRegistry {name} {key} {world} {error} {value}
  nameEq fuel (Bind current observed :: rest) removed fibers valid
  with (decEq @{nameEq} removed current)
  chainsEntriesDeleteSameRegistry {name} {key} {world} {error} {value}
    nameEq fuel (Bind removed observed :: rest) removed fibers valid |
    (Yes Refl) = andTrueRight _ _ valid
  chainsEntriesDeleteSameRegistry {name} {key} {world} {error} {value}
    nameEq fuel (Bind current observed :: rest) removed fibers valid |
    (No _) = andBothTrue _ _ (andTrueLeft _ _ valid)
      (chainsEntriesDeleteSameRegistry {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq fuel rest removed fibers
        (andTrueRight _ _ valid))

0 bindingKeysLength : (entries : List (Binding key value)) ->
  length (bindingKeys entries) = length entries
bindingKeysLength [] = Refl
bindingKeysLength (Bind k v :: rest) = cong S (bindingKeysLength rest)

public export
EntrySubset : {key : Type} -> {value : key -> Type} -> List (Binding key value) -> List (Binding key value) -> Type
EntrySubset scan full = (entry : Binding key value) ->
  Elem entry scan -> Elem entry full

0 chainsRegistryDeleteCardinal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (remaining : Nat) ->
  (scan, full : List (Binding name (FiberAt name key value world error))) ->
  EntrySubset scan full -> (removed : name) ->
  (removedFiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  registryFibers {value = value} {world = world} {error = error}
    (deleteBinding @{nameEq} removed fibers) = full ->
  length full = remaining ->
  Not (Elem removed (bindingKeys full)) ->
  hasChild @{nameEq} {key = key} {value = value} {world = world} {error = error} removed fibers = False ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} removed fibers = Just removedFiber ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (S (S remaining)) scan fibers = True ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (S remaining) scan
    (deleteBinding @{nameEq} removed fibers) = True
chainsRegistryDeleteCardinal {key} {world} {error} {value} nameEq remaining [] full subset removed removedFiber
  fibers targetEntriesEq lengthOk removedAbsent noChild present valid = Refl
chainsRegistryDeleteCardinal {name} {key} {world} {error} {value}
  nameEq remaining (entry@(Bind current observed) :: rest) full subset removed
  removedFiber fibers targetEntriesEq lengthOk removedAbsent noChild present valid =
  let 0 currentInFull : Elem entry full
      currentInFull = subset entry Here
      0 currentInKeys : Elem current (bindingKeys full)
      currentInKeys = bindingKeyElem entry full currentInFull
      currentDistinct : Not (current = removed)
      currentDistinct same = removedAbsent
        (replace {p = \candidate => Elem candidate (bindingKeys full)} same
          currentInKeys)
      0 available : List name
      available = current :: bindingKeys full
      0 availableLength : length available = S remaining
      availableLength = cong S (trans (bindingKeysLength full) lengthOk)
      0 availableCurrent : Elem current available
      availableCurrent = Here
      0 availableRemovedAbsent : Not (Elem removed available)
      availableRemovedAbsent occurrence = case occurrence of
        Here => currentDistinct Refl
        There later => removedAbsent later
      0 availableComplete : AvailableComplete name key world error value nameEq
        [current] available (deleteBinding @{nameEq} removed fibers)
      availableComplete candidate notSeen found foundLookup =
        There (replace {p = \entries => Elem candidate (bindingKeys entries)}
          targetEntriesEq
          (registryAvailabilityComplete {name = name} {key = key}
            {world = world} {error = error} {value = value} nameEq [current]
            (deleteBinding @{nameEq} removed fibers) candidate notSeen found
            foundLookup))
      0 targetHead : parentChainInvariant @{nameEq} {key = key} {value = value}
        {world = world} {error = error} (S remaining) [current] current
        (deleteBinding @{nameEq} removed fibers) = True
      targetHead = parentChainDeleteAvailable {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq remaining available
        [current] current removed removedFiber fibers availableLength availableCurrent
        availableRemovedAbsent Here availableComplete noChild present
        (andTrueLeft _ _ valid)
      0 tailSubset : EntrySubset rest full
      tailSubset tailEntry tailElem = subset tailEntry (There tailElem)
      0 targetTail : chainsInvariant @{nameEq} {key = key} {value = value}
        {world = world} {error = error} (S remaining) rest
        (deleteBinding @{nameEq} removed fibers) = True
      targetTail = chainsRegistryDeleteCardinal {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq remaining rest full
        tailSubset removed removedFiber fibers targetEntriesEq lengthOk removedAbsent noChild present
        (andTrueRight _ _ valid)
  in andBothTrue _ _ targetHead targetTail

||| Connect the exact one-entry length decrement to the cardinal chain fold.
public export
0 chainsInvariantDeleteCardinal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  (removed : name) -> (removedFiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  hasChild @{nameEq} {key = key} {value = value} {world = world} {error = error} removed fibers = False ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} removed fibers = Just removedFiber ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (S (length (registryFibers {value = value} {world = world} {error = error} fibers)))
    (registryFibers {value = value} {world = world} {error = error} fibers) fibers = True ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world}
    {error = error} (S (length (registryFibers {value = value} {world = world} {error = error} (deleteBinding @{nameEq} removed fibers))))
    (registryFibers {value = value} {world = world} {error = error} (deleteBinding @{nameEq} removed fibers))
    (deleteBinding @{nameEq} removed fibers) = True
chainsInvariantDeleteCardinal {name} {key} {world} {error} {value}
  nameEq removed removedFiber fibers@(MkCoeffectContext entries unique)
  noChild present valid =
  let 0 entryPresent : (lookupEntries @{nameEq}
        {value = FiberAt name key value world error} removed entries =
        Just removedFiber)
      entryPresent = lookupFiberEntries nameEq removed removedFiber fibers present
      0 targetEntries : List (Binding name (FiberAt name key value world error))
      targetEntries = deleteEntries @{nameEq} removed entries
      0 sourceLength : S (length targetEntries) = length entries
      sourceLength = deleteEntriesPresentLength removed removedFiber entries entryPresent
      0 sourceFuelEq : S (S (length targetEntries)) = S (length entries)
      sourceFuelEq = cong S sourceLength
      0 sourceTargetChains : chainsInvariant @{nameEq} {key = key}
        {value = value} {world = world} {error = error} (S (length entries)) targetEntries fibers = True
      sourceTargetChains = chainsEntriesDeleteSameRegistry {name = name}
        {key = key} {world = world} {error = error} {value = value} nameEq
        (S (length entries)) entries removed fibers valid
      0 normalizedSource : chainsInvariant @{nameEq} {key = key}
        {value = value} {world = world} {error = error} (S (S (length targetEntries))) targetEntries fibers = True
      normalizedSource = replace
        {p = \fuel => chainsInvariant @{nameEq} {key = key} {value = value}
          {world = world} {error = error} fuel targetEntries fibers = True}
        (sym sourceFuelEq) sourceTargetChains
      0 identitySubset : EntrySubset targetEntries targetEntries
      identitySubset entry occurrence = occurrence
  in chainsRegistryDeleteCardinal {name = name} {key = key} {world = world}
    {error = error} {value = value} nameEq (length targetEntries) targetEntries
    targetEntries identitySubset removed removedFiber fibers Refl Refl
    (deletedKeyNotElem removed entries unique) noChild present normalizedSource

0 parentInvariantDeleteDistinct :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (parent : Parent name) -> (removed : name) ->
  (fibers : Registry name key value world error) ->
  Not (parent = ChildOf removed) ->
  parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} parent fibers = True ->
  parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} parent (deleteBinding @{nameEq} removed fibers) = True
parentInvariantDeleteDistinct {key} {world} {error} {value} nameEq Root removed fibers distinct valid = Refl
parentInvariantDeleteDistinct {name} {key} {world} {error} {value}
  nameEq (ChildOf parent) removed fibers distinct valid =
    let parentDistinct : Not (parent = removed)
        parentDistinct same = distinct (cong ChildOf same)
    in rewrite lookupDeleteOther parent removed parentDistinct fibers in valid

0 parentsRegistryDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (removed : name) -> (fibers : Registry name key value world error) ->
  hasChildIn @{nameEq} {key = key} {value = value} {world = world} {error = error} removed entries = False ->
  parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} entries fibers = True ->
  parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} entries (deleteBinding @{nameEq} removed fibers) = True
parentsRegistryDelete {key} {world} {error} {value} nameEq [] removed fibers noChild valid = Refl
parentsRegistryDelete {name} {key} {world} {error} {value}
  nameEq (Bind current observed :: rest) removed fibers noChild valid =
  let headDistinct = noChildHeadParentDistinct nameEq removed current observed rest
        noChild
      targetHead = parentInvariantDeleteDistinct {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq
        (fiberParent observed) removed fibers headDistinct (andTrueLeft _ _ valid)
      targetTail = parentsRegistryDelete {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq rest removed fibers
        (boolOrRightFalse
          (isChildOf @{nameEq} removed (Bind current observed))
          (hasChildIn @{nameEq} {key = key} {value = value} {world = world} {error = error} removed rest) noChild)
        (andTrueRight _ _ valid)
  in andBothTrue _ _ targetHead targetTail

||| Parent closure is preserved when the no-child guard removes a leaf.
public export
0 parentsInvariantDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (removed : name) -> (fibers : Registry name key value world error) ->
  hasChildIn @{nameEq} {key = key} {value = value} {world = world} {error = error} removed entries = False ->
  parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} entries fibers = True ->
  parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (deleteEntries @{nameEq} removed entries)
    (deleteBinding @{nameEq} removed fibers) = True
parentsInvariantDelete {key} {world} {error} {value} nameEq [] removed fibers noChild valid = Refl
parentsInvariantDelete {name} {key} {world} {error} {value}
  nameEq (Bind current observed :: rest) removed fibers noChild valid
  with (decEq @{nameEq} removed current)
  parentsInvariantDelete {name} {key} {world} {error} {value}
    nameEq (Bind removed observed :: rest) removed fibers noChild valid |
    (Yes Refl) = parentsRegistryDelete {name = name} {key = key}
      {world = world} {error = error} {value = value} nameEq rest removed fibers
      (boolOrRightFalse
        (isChildOf @{nameEq} removed (Bind removed observed))
        (hasChildIn @{nameEq} {key = key} {value = value} {world = world} {error = error} removed rest) noChild)
      (andTrueRight _ _ valid)
  parentsInvariantDelete {name} {key} {world} {error} {value}
    nameEq (Bind current observed :: rest) removed fibers noChild valid |
    (No _) =
      let headDistinct = noChildHeadParentDistinct nameEq removed current observed
            rest noChild
          targetHead = parentInvariantDeleteDistinct {name = name} {key = key}
            {world = world} {error = error} {value = value} nameEq
            (fiberParent observed) removed fibers headDistinct
            (andTrueLeft _ _ valid)
          targetTail = parentsInvariantDelete {name = name} {key = key}
            {world = world} {error = error} {value = value} nameEq rest removed
            fibers
            (boolOrRightFalse
              (isChildOf @{nameEq} removed (Bind current observed))
              (hasChildIn @{nameEq} {key = key} {value = value} {world = world} {error = error} removed rest) noChild)
            (andTrueRight _ _ valid)
      in andBothTrue _ _ targetHead targetTail

||| Removing an entry cannot introduce a provision overlap.
public export
0 provisionsDisjointDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provision : CoeffectSpec key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (removed : name) ->
  provisionsDisjointFrom @{keyEq} {value = value} {world = world}
    {error = error} provision entries = True ->
  provisionsDisjointFrom @{keyEq} {value = value} {world = world}
    {error = error} provision (deleteEntries @{nameEq} removed entries) = True
provisionsDisjointDelete nameEq keyEq provision [] removed valid = Refl
provisionsDisjointDelete {name} {key} {world} {error} {value}
  nameEq keyEq provision (Bind current fiber :: rest) removed valid
  with (decEq @{nameEq} removed current)
  provisionsDisjointDelete {name} {key} {world} {error} {value}
    nameEq keyEq provision (Bind removed fiber :: rest) removed valid |
    (Yes Refl) = andTrueRight _ _ valid
  provisionsDisjointDelete {name} {key} {world} {error} {value}
    nameEq keyEq provision (Bind current fiber :: rest) removed valid |
    (No _) = andBothTrue _ _ (andTrueLeft _ _ valid)
      (provisionsDisjointDelete {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq keyEq provision rest removed
        (andTrueRight _ _ valid))

||| Pairwise provision disjointness is downward closed under deletion.
public export
0 pairwiseProvisionDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (removed : name) ->
  pairwiseProvisionInvariant @{keyEq} {value = value} {world = world}
    {error = error} entries = True ->
  pairwiseProvisionInvariant @{keyEq} {value = value} {world = world}
    {error = error} (deleteEntries @{nameEq} removed entries) = True
pairwiseProvisionDelete nameEq keyEq [] removed valid = Refl
pairwiseProvisionDelete {name} {key} {world} {error} {value}
  nameEq keyEq (Bind current fiber :: rest) removed valid
  with (decEq @{nameEq} removed current)
  pairwiseProvisionDelete {name} {key} {world} {error} {value}
    nameEq keyEq (Bind removed fiber :: rest) removed valid | (Yes Refl) =
      andTrueRight _ _ valid
  pairwiseProvisionDelete {name} {key} {world} {error} {value}
    nameEq keyEq (Bind current fiber :: rest) removed valid | (No _) =
      andBothTrue _ _
        (provisionsDisjointDelete {name = name} {key = key} {world = world}
          {error = error} {value = value} nameEq keyEq
          (componentProvisions (fiberComponent fiber)) rest removed
          (andTrueLeft _ _ valid))
        (pairwiseProvisionDelete {name = name} {key = key} {world = world}
          {error = error} {value = value} nameEq keyEq rest removed
          (andTrueRight _ _ valid))

public export
0 viewProvidersHeadStable :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {deps : List key} -> (nameEq : DecEq name) ->
  (provider : name) -> (k : key) -> (rest : View name deps) -> (fibers : Registry name key value world error) ->
  (providerFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} provider fibers = Just providerFiber ->
  viewProvidersInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fibers (ProviderView {k = k} provider rest) = True ->
  stableProvider (fiberLifecycle providerFiber) = True
viewProvidersHeadStable {name} {key} {world} {error} {value}
  nameEq provider k rest fibers providerFiber present valid
  with (lookupFiber @{nameEq} provider fibers)
  viewProvidersHeadStable {name} {key} {world} {error} {value}
    nameEq provider k rest fibers providerFiber present valid | Nothing =
      case present of Refl impossible
  viewProvidersHeadStable {name} {key} {world} {error} {value}
    nameEq provider k rest fibers providerFiber present valid | Just observed =
      case present of Refl => andTrueLeft _ _ valid

||| A committed view cannot name an Inactive fiber as a provider; deleting such
||| a fiber therefore preserves the installed/stable provider certificate.
public export
0 viewProvidersInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (deps : List key) -> (view : View name deps) ->
  (removed : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) -> (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} removed fibers =
    Just (MkFiber component parent retired table (Inactive outcome)) ->
  viewProvidersInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fibers view = True ->
  viewProvidersInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} (deleteBinding @{nameEq} removed fibers)
    view = True
viewProvidersInactiveDelete {key} {world} {error} {value}
  nameEq [] EmptyView removed component parent retired table outcome fibers
  present valid = Refl
viewProvidersInactiveDelete {name} {key} {world} {error} {value}
  nameEq (k :: ks) (ProviderView provider rest) removed component parent retired
  table outcome fibers present valid with (decEq @{nameEq} provider removed)
  viewProvidersInactiveDelete {name} {key} {world} {error} {value}
    nameEq (k :: ks) (ProviderView removed rest) removed component parent retired
    table outcome fibers present valid | (Yes Refl) =
      let 0 sourceHead : (stableProvider {key = key} {value = value}
            {world = world} {error = error} {name = name}
            {deps = dependencies (componentDependencies component)}
            {provision = componentProvisions component} (Inactive outcome) = True)
          sourceHead = viewProvidersHeadStable {name = name} {key = key}
            {world = world} {error = error} {value = value} nameEq removed k rest
            fibers (MkFiber component parent retired table (Inactive outcome))
            present valid
      in void (falseCannotBeTrue sourceHead)
  viewProvidersInactiveDelete {name} {key} {world} {error} {value}
    nameEq (k :: ks) (ProviderView provider rest) removed component parent retired
    table outcome fibers present valid | (No distinct)
    with (lookupFiber @{nameEq} provider fibers) proof providerLookup
    viewProvidersInactiveDelete {name} {key} {world} {error} {value}
      nameEq (k :: ks) (ProviderView provider rest) removed component parent retired
      table outcome fibers present valid | (No distinct) | Nothing =
        void (falseCannotBeTrue valid)
    viewProvidersInactiveDelete {name} {key} {world} {error} {value}
      nameEq (k :: ks) (ProviderView provider rest) removed component parent retired
      table outcome fibers present valid | (No distinct) | Just providerFiber =
        let targetLookup = trans
              (lookupDeleteOther provider removed distinct fibers) providerLookup
            sourceHead = andTrueLeft _ _ valid
            sourceTail = andTrueRight _ _ valid
            targetTail = viewProvidersInactiveDelete {name = name} {key = key}
              {world = world} {error = error} {value = value} nameEq ks rest
              removed component parent retired table outcome fibers present sourceTail
        in rewrite targetLookup in andBothTrue _ _ sourceHead targetTail

||| Deleting a distinct fiber leaves a provider-owned value lookup unchanged.
public export
0 valueFromProviderInactiveDeleteOther :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider, removed : name) -> Not (provider = removed) -> (k : key) ->
  (fibers : Registry name key value world error) ->
  valueFromProvider @{nameEq} @{keyEq} {value = value} {world = world} {error = error} provider k
    (deleteBinding @{nameEq} removed fibers) =
  valueFromProvider @{nameEq} @{keyEq} {value = value} {world = world} {error = error} provider k fibers
valueFromProviderInactiveDeleteOther {key} {world} {error} {value}
  nameEq keyEq provider removed distinct k fibers
  with (lookupFiber @{nameEq} provider fibers) proof original
  valueFromProviderInactiveDeleteOther {key} {world} {error} {value}
    nameEq keyEq provider removed distinct k fibers | Nothing =
      rewrite lookupDeleteOther provider removed distinct fibers in
      rewrite original in Refl
  valueFromProviderInactiveDeleteOther {key} {world} {error} {value}
    nameEq keyEq provider removed distinct k fibers | Just providerFiber =
      rewrite lookupDeleteOther provider removed distinct fibers in
      rewrite original in Refl

public export
0 viewProvidersTailValid :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {deps : List key} -> (nameEq : DecEq name) ->
  (provider : name) -> (k : key) -> (rest : View name deps) ->
  (fibers : Registry name key value world error) ->
  viewProvidersInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fibers (ProviderView {k = k} provider rest) =
    True ->
  viewProvidersInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fibers rest = True
viewProvidersTailValid {name} {key} {world} {error} {value}
  nameEq provider k rest fibers valid with (lookupFiber @{nameEq} provider fibers)
  viewProvidersTailValid {name} {key} {world} {error} {value}
    nameEq provider k rest fibers valid | Nothing =
      void (falseCannotBeTrue valid)
  viewProvidersTailValid {name} {key} {world} {error} {value}
    nameEq provider k rest fibers valid | Just providerFiber =
      andTrueRight _ _ valid

||| All value observations of a valid committed view survive deletion of an
||| Inactive fiber.
public export
0 resolveCommittedValuesInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  (removed : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) -> (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} removed fibers =
    Just (MkFiber component parent retired table (Inactive outcome)) ->
  viewProvidersInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fibers view = True ->
  resolveCommittedValues @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps view
    (deleteBinding @{nameEq} removed fibers) =
  resolveCommittedValues @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps view fibers
resolveCommittedValuesInactiveDelete {key} {world} {error} {value}
  nameEq keyEq [] EmptyView removed component parent retired table outcome fibers
  present providersValid = Refl
resolveCommittedValuesInactiveDelete {name} {key} {world} {error} {value}
  nameEq keyEq (k :: ks) (ProviderView provider rest) removed component parent
  retired table outcome fibers present providersValid
  with (decEq @{nameEq} provider removed)
  resolveCommittedValuesInactiveDelete {name} {key} {world} {error} {value}
    nameEq keyEq (k :: ks) (ProviderView removed rest) removed component parent
    retired table outcome fibers present providersValid | (Yes Refl) =
      let 0 sourceHead : (stableProvider {key = key} {value = value}
            {world = world} {error = error} {name = name}
            {deps = dependencies (componentDependencies component)}
            {provision = componentProvisions component} (Inactive outcome) = True)
          sourceHead = viewProvidersHeadStable {name = name} {key = key}
            {world = world} {error = error} {value = value} nameEq removed k rest
            fibers (MkFiber component parent retired table (Inactive outcome))
            present providersValid
      in void (falseCannotBeTrue sourceHead)
  resolveCommittedValuesInactiveDelete {name} {key} {world} {error} {value}
    nameEq keyEq (k :: ks) (ProviderView provider rest) removed component parent
    retired table outcome fibers present providersValid | (No distinct)
    with (valueFromProvider @{nameEq} @{keyEq} provider k fibers) proof original
    resolveCommittedValuesInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq (k :: ks) (ProviderView provider rest) removed component parent
      retired table outcome fibers present providersValid | (No distinct) | Nothing =
        let target = trans (valueFromProviderInactiveDeleteOther
              {name = name} {key = key} {world = world} {error = error}
              {value = value} nameEq keyEq provider removed distinct k fibers)
              original
        in rewrite target in Refl
    resolveCommittedValuesInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq (k :: ks) (ProviderView provider rest) removed component parent
      retired table outcome fibers present providersValid | (No distinct) | Just v =
        let target = trans (valueFromProviderInactiveDeleteOther
              {name = name} {key = key} {world = world} {error = error}
              {value = value} nameEq keyEq provider removed distinct k fibers)
              original
            tailValid = viewProvidersTailValid {name = name} {key = key}
              {world = world} {error = error} {value = value} nameEq provider k
              rest fibers providersValid
            tailFrame = resolveCommittedValuesInactiveDelete {name = name}
              {key = key} {world = world} {error = error} {value = value}
              nameEq keyEq ks rest removed component parent retired table outcome
              fibers present tailValid
        in rewrite target in cong (map (OneDepValue v)) tailFrame

public export
0 viewBindingsInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  (removed : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) -> (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} removed fibers =
    Just (MkFiber component parent retired table (Inactive outcome)) ->
  viewBindingsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps view fibers = True ->
  viewBindingsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps view
    (deleteBinding @{nameEq} removed fibers) = True
viewBindingsInactiveDelete {name} {key} {world} {error} {value}
  nameEq keyEq deps view removed component parent retired table outcome fibers
  present valid =
  let sourceProviders = andTrueLeft _ _ valid
      sourceValues = andTrueRight _ _ valid
      targetProviders = viewProvidersInactiveDelete {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq deps view removed
        component parent retired table outcome fibers present sourceProviders
      valuesFrame = resolveCommittedValuesInactiveDelete {name = name}
        {key = key} {world = world} {error = error} {value = value} nameEq keyEq
        deps view removed component parent retired table outcome fibers present
        sourceProviders
      targetValues = trans (cong isJust valuesFrame) sourceValues
  in andBothTrue _ _ targetProviders targetValues

public export
0 fiberViewInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (observed : Fiber name key value world error) ->
  (removed : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) -> (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} removed fibers =
    Just (MkFiber component parent retired table (Inactive outcome)) ->
  fiberViewInvariant @{nameEq} @{keyEq} observed fibers = True ->
  fiberViewInvariant @{nameEq} @{keyEq} observed
    (deleteBinding @{nameEq} removed fibers) = True
fiberViewInactiveDelete {name} {key} {world} {error} {value}
  nameEq keyEq (MkFiber observedComponent observedParent observedRetired
    observedTable (Inactive observedOutcome)) removed component parent retired
    table outcome fibers present valid = Refl
fiberViewInactiveDelete {name} {key} {world} {error} {value}
  nameEq keyEq (MkFiber observedComponent observedParent observedRetired
    observedTable (Reloading rest accumulator view)) removed component parent retired
    table outcome fibers present valid =
      viewBindingsInactiveDelete {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq keyEq
        (dependencies (componentDependencies observedComponent)) view removed
        component parent retired table outcome fibers present valid
fiberViewInactiveDelete {name} {key} {world} {error} {value}
  nameEq keyEq (MkFiber observedComponent observedParent observedRetired
    observedTable (Active accumulator view)) removed component parent retired table
    outcome fibers present valid =
      viewBindingsInactiveDelete {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq keyEq
        (dependencies (componentDependencies observedComponent)) view removed
        component parent retired table outcome fibers present valid
fiberViewInactiveDelete {name} {key} {world} {error} {value}
  nameEq keyEq (MkFiber observedComponent observedParent observedRetired
    observedTable (Unloading accumulator view observedOutcome)) removed component
    parent retired table outcome fibers present valid =
      viewBindingsInactiveDelete {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq keyEq
        (dependencies (componentDependencies observedComponent)) view removed
        component parent retired table outcome fibers present valid

0 viewsRegistryInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (removed : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) -> (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} removed fibers =
    Just (MkFiber component parent retired table (Inactive outcome)) ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries fibers = True ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries
    (deleteBinding @{nameEq} removed fibers) = True
viewsRegistryInactiveDelete {key} {world} {error} {value}
  nameEq keyEq [] removed component parent retired table outcome fibers present valid =
    Refl
viewsRegistryInactiveDelete {name} {key} {world} {error} {value}
  nameEq keyEq (Bind current observed :: rest) removed component parent retired table
  outcome fibers present valid =
  andBothTrue _ _
    (fiberViewInactiveDelete {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq keyEq observed removed component
      parent retired table outcome fibers present (andTrueLeft _ _ valid))
    (viewsRegistryInactiveDelete {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq keyEq rest removed component parent
      retired table outcome fibers present (andTrueRight _ _ valid))

0 viewsEntriesDeleteSameRegistry :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (removed : name) -> (fibers : Registry name key value world error) ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries fibers = True ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (deleteEntries @{nameEq} removed entries)
    fibers = True
viewsEntriesDeleteSameRegistry {key} {world} {error} {value}
  nameEq keyEq [] removed fibers valid = Refl
viewsEntriesDeleteSameRegistry {name} {key} {world} {error} {value}
  nameEq keyEq (Bind current observed :: rest) removed fibers valid
  with (decEq @{nameEq} removed current)
  viewsEntriesDeleteSameRegistry {name} {key} {world} {error} {value}
    nameEq keyEq (Bind removed observed :: rest) removed fibers valid |
    (Yes Refl) = andTrueRight _ _ valid
  viewsEntriesDeleteSameRegistry {name} {key} {world} {error} {value}
    nameEq keyEq (Bind current observed :: rest) removed fibers valid |
    (No _) = andBothTrue _ _ (andTrueLeft _ _ valid)
      (viewsEntriesDeleteSameRegistry {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq keyEq rest removed fibers
        (andTrueRight _ _ valid))

||| Removing an Inactive fiber preserves committed views in all remaining
||| registry entries.
public export
0 viewsInvariantInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (removed : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) -> (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} removed fibers =
    Just (MkFiber component parent retired table (Inactive outcome)) ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (registryFibers {value = value} {world = world} {error = error} fibers) fibers = True ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} (registryFibers {value = value} {world = world} {error = error} (deleteBinding @{nameEq} removed fibers))
    (deleteBinding @{nameEq} removed fibers) = True
viewsInvariantInactiveDelete {name} {key} {world} {error} {value}
  nameEq keyEq removed component parent retired table outcome
  fibers@(MkCoeffectContext entries unique) present valid =
  let sourceRemaining = viewsEntriesDeleteSameRegistry {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq entries
        removed fibers valid
  in viewsRegistryInactiveDelete {name = name} {key = key} {world = world}
    {error = error} {value = value} nameEq keyEq
    (deleteEntries @{nameEq} removed entries) removed component parent retired table
    outcome fibers present sourceRemaining

public export
0 retireViewInvariant : (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  fiberViewInvariant @{nameEq} @{keyEq} (retireFiber fiber) fibers =
  fiberViewInvariant @{nameEq} @{keyEq} fiber fibers
retireViewInvariant nameEq keyEq
  (MkFiber component parent retired table (Inactive outcome)) fibers = Refl
retireViewInvariant nameEq keyEq
  (MkFiber component parent retired table (Reloading rest accumulator view)) fibers = Refl
retireViewInvariant nameEq keyEq
  (MkFiber component parent retired table (Active accumulator view)) fibers = Refl
retireViewInvariant nameEq keyEq
  (MkFiber component parent retired table (Unloading accumulator view outcome)) fibers = Refl

public export
0 viewsRegistryRetire :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  (present : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} n fibers = Just fiber) ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries fibers = True ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries
    (replaceBinding @{nameEq} n (retireFiber fiber) fibers) = True
viewsRegistryRetire {key} {world} {error} {value} nameEq keyEq [] n fiber fibers present valid = Refl
viewsRegistryRetire {name} {key} {world} {error} {value}
  nameEq keyEq (Bind current observed :: rest) n fiber fibers present valid =
    andBothTrue _ _
      (trans (fiberViewRetireRegistry {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq observed n
        fiber fibers present) (andTrueLeft _ _ valid))
      (viewsRegistryRetire {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq keyEq rest n fiber fibers present
        (andTrueRight _ _ valid))

public export
0 viewsEntriesRetire :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (registry : Registry name key value world error) ->
  lookupEntries @{nameEq} {value = FiberAt name key value world error}
    n entries = Just fiber ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries registry = True ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} (replaceEntries @{nameEq} n (retireFiber fiber) entries) registry = True
viewsEntriesRetire {key} {world} {error} {value} nameEq keyEq [] n fiber registry present valid =
  case present of Refl impossible
viewsEntriesRetire {name} {key} {world} {error} {value}
  nameEq keyEq (Bind current observed :: rest) n fiber registry present valid
  with (decEq @{nameEq} n current)
  viewsEntriesRetire {name} {key} {world} {error} {value}
    nameEq keyEq (Bind n observed :: rest) n fiber registry present valid |
    (Yes Refl) = case present of
      Refl => andBothTrue _ _
        (trans (retireViewInvariant {name = name} {key = key} {world = world}
          {error = error} {value = value} nameEq keyEq observed registry)
          (andTrueLeft _ _ valid))
        (andTrueRight _ _ valid)
  viewsEntriesRetire {name} {key} {world} {error} {value}
    nameEq keyEq (Bind current observed :: rest) n fiber registry present valid |
    (No _) = andBothTrue _ _ (andTrueLeft _ _ valid)
      (viewsEntriesRetire {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq keyEq rest n fiber registry present
        (andTrueRight _ _ valid))

||| ORetire preserves all four clauses of Definition 58.
public export
0 registryWellFormedRetire :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (ambient : world) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  (present : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} n fibers = Just fiber) ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (MkSystemState ambient fibers) = True ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
    (MkSystemState ambient (replaceBinding @{nameEq} n (retireFiber fiber) fibers)) = True
registryWellFormedRetire {name} {key} {world} {error} {value}
  nameEq keyEq ambient n fiber fibers@(MkCoeffectContext entries unique)
  present valid =
  let entryPresent = lookupFiberEntries nameEq n fiber fibers present
      sourceParents = andFourFirst
        (parentsInvariant @{nameEq} entries fibers)
        (chainsInvariant @{nameEq} (S (length entries)) entries fibers)
        (pairwiseProvisionInvariant @{keyEq} entries)
        (viewsInvariant @{nameEq} @{keyEq} entries fibers) valid
      sourceChains = andFourSecond
        (parentsInvariant @{nameEq} entries fibers)
        (chainsInvariant @{nameEq} (S (length entries)) entries fibers)
        (pairwiseProvisionInvariant @{keyEq} entries)
        (viewsInvariant @{nameEq} @{keyEq} entries fibers) valid
      sourcePairwise = andFourThird
        (parentsInvariant @{nameEq} entries fibers)
        (chainsInvariant @{nameEq} (S (length entries)) entries fibers)
        (pairwiseProvisionInvariant @{keyEq} entries)
        (viewsInvariant @{nameEq} @{keyEq} entries fibers) valid
      sourceViews = andFourFourth
        (parentsInvariant @{nameEq} entries fibers)
        (chainsInvariant @{nameEq} (S (length entries)) entries fibers)
        (pairwiseProvisionInvariant @{keyEq} entries)
        (viewsInvariant @{nameEq} @{keyEq} entries fibers) valid
      parentsFramed = parentsRegistryRetire {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq entries n fiber
        fibers present sourceParents
      targetParents = parentsEntriesRetire {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq entries n fiber
        (replaceBinding @{nameEq} n (retireFiber fiber) fibers)
        entryPresent parentsFramed
      chainsFramed = chainsRegistryRetire {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq (S (length entries)) entries n
        fiber fibers present sourceChains
      targetChains = chainsEntriesRetire {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq (S (length entries)) entries n
        fiber (replaceBinding @{nameEq} n (retireFiber fiber) fibers)
        entryPresent chainsFramed
      targetPairwise = trans (pairwiseRetireEntries {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq entries n
        fiber entryPresent) sourcePairwise
      viewsFramed = viewsRegistryRetire {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq entries n
        fiber fibers present sourceViews
      targetViews = viewsEntriesRetire {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq entries n
        fiber (replaceBinding @{nameEq} n (retireFiber fiber) fibers)
        entryPresent viewsFramed in
    rewrite replaceEntriesLength n (retireFiber fiber) entries in
      andBothTrue _ _ targetParents
        (andBothTrue _ _ targetChains
          (andBothTrue _ _ targetPairwise targetViews))

||| ORemove preserves all four clauses of Definition 58 when its leaf is
||| Inactive. The retired guard is operational but irrelevant to well-formedness.
public export
0 registryWellFormedInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (ambient : world) ->
  (removed : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) -> (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} removed fibers =
    Just (MkFiber component parent retired table (Inactive outcome)) ->
  hasChild @{nameEq} {key = key} {value = value} {world = world} {error = error} removed fibers = False ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (MkSystemState ambient fibers) = True ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} (MkSystemState ambient (deleteBinding @{nameEq} removed fibers)) = True
registryWellFormedInactiveDelete {name} {key} {world} {error} {value}
  nameEq keyEq ambient removed component parent retired table outcome
  fibers@(MkCoeffectContext entries unique) present noChild valid =
  let sourceParents = andFourFirst
        (parentsInvariant @{nameEq} entries fibers)
        (chainsInvariant @{nameEq} (S (length entries)) entries fibers)
        (pairwiseProvisionInvariant @{keyEq} entries)
        (viewsInvariant @{nameEq} @{keyEq} entries fibers) valid
      sourceChains = andFourSecond
        (parentsInvariant @{nameEq} entries fibers)
        (chainsInvariant @{nameEq} (S (length entries)) entries fibers)
        (pairwiseProvisionInvariant @{keyEq} entries)
        (viewsInvariant @{nameEq} @{keyEq} entries fibers) valid
      sourcePairwise = andFourThird
        (parentsInvariant @{nameEq} entries fibers)
        (chainsInvariant @{nameEq} (S (length entries)) entries fibers)
        (pairwiseProvisionInvariant @{keyEq} entries)
        (viewsInvariant @{nameEq} @{keyEq} entries fibers) valid
      sourceViews = andFourFourth
        (parentsInvariant @{nameEq} entries fibers)
        (chainsInvariant @{nameEq} (S (length entries)) entries fibers)
        (pairwiseProvisionInvariant @{keyEq} entries)
        (viewsInvariant @{nameEq} @{keyEq} entries fibers) valid
      targetParents = parentsInvariantDelete {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq entries removed
        fibers noChild sourceParents
      targetChains = chainsInvariantDeleteCardinal {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq removed
        (MkFiber component parent retired table (Inactive outcome)) fibers noChild
        present sourceChains
      targetPairwise = pairwiseProvisionDelete {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq entries
        removed sourcePairwise
      targetViews = viewsInvariantInactiveDelete {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq removed
        component parent retired table outcome fibers present sourceViews
  in andBothTrue _ _ targetParents
    (andBothTrue _ _ targetChains (andBothTrue _ _ targetPairwise targetViews))

0 setFiberRuntimeProvision :
  (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  componentProvisions (fiberComponent
    (setFiberRuntime fiber newTable newLifecycle)) =
  componentProvisions (fiberComponent fiber)
setFiberRuntimeProvision
  (MkFiber component parent retired oldTable oldLifecycle) newTable
  newLifecycle = Refl

0 setFiberRuntimeParent :
  (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  fiberParent (setFiberRuntime fiber newTable newLifecycle) = fiberParent fiber
setFiberRuntimeParent (MkFiber component parent retired oldTable oldLifecycle)
  newTable newLifecycle = Refl

0 lookupRuntimeReplaced :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (n : name) ->
  (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} n fibers = Just fiber ->
  lookupFiber @{nameEq} n
    (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers) =
    Just (setFiberRuntime fiber newTable newLifecycle)
lookupRuntimeReplaced nameEq n fiber newTable newLifecycle
  (MkCoeffectContext entries unique) present =
  lookupReplaceEntries n fiber (setFiberRuntime fiber newTable newLifecycle)
    entries present

||| A runtime replacement preserves the component, parent, retirement bit, and
||| provision. This frame packages the only lookup fact needed by parent chains.
public export
record RuntimeLookupFrame (nameEq : DecEq name) (current, n : name)
  (fiber, observed : Fiber name key value world error)
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber)))
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)))
  (fibers : Registry name key value world error) where
  constructor MkRuntimeLookupFrame
  framedRuntimeFiber : Fiber name key value world error
  0 framedRuntimeLookup : lookupFiber @{nameEq} current
    (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers) =
    Just framedRuntimeFiber
  0 framedRuntimeParent : fiberParent framedRuntimeFiber = fiberParent observed

0 runtimeLookupFrame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (current, n : name) ->
  (fiber, observed : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} current fibers = Just observed ->
  lookupFiber @{nameEq} n fibers = Just fiber ->
  RuntimeLookupFrame nameEq current n fiber observed newTable newLifecycle fibers
runtimeLookupFrame {name} {key} {world} {error} {value}
  nameEq current n fiber observed newTable newLifecycle
  fibers@(MkCoeffectContext entries unique) currentLookup present
  with (decEq @{nameEq} current n)
  runtimeLookupFrame {name} {key} {world} {error} {value}
    nameEq n n fiber observed newTable newLifecycle
    fibers@(MkCoeffectContext entries unique) currentLookup present | (Yes Refl) =
      case justValuesEqual (trans (sym currentLookup) present) of
        Refl => MkRuntimeLookupFrame (setFiberRuntime fiber newTable newLifecycle)
          (lookupReplaceEntries n fiber
            (setFiberRuntime fiber newTable newLifecycle) entries present)
          (setFiberRuntimeParent fiber newTable newLifecycle)
  runtimeLookupFrame {name} {key} {world} {error} {value}
    nameEq current n fiber observed newTable newLifecycle
    fibers@(MkCoeffectContext entries unique) currentLookup present | (No distinct) =
      MkRuntimeLookupFrame observed
        (trans (lookupReplaceOtherEntries current n distinct
          (setFiberRuntime fiber newTable newLifecycle) entries) currentLookup)
        Refl

0 parentInvariantRuntimeRegistry :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (parent : Parent name) -> (n : name) ->
  (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Just fiber ->
  parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} parent fibers = True ->
  parentInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} parent
    (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers) = True
parentInvariantRuntimeRegistry nameEq Root n fiber newTable newLifecycle fibers
  present valid = Refl
parentInvariantRuntimeRegistry {name} {key} {world} {error} {value}
  nameEq (ChildOf parent) n fiber newTable newLifecycle fibers present valid
  with (decEq @{nameEq} parent n)
  parentInvariantRuntimeRegistry {name} {key} {world} {error} {value}
    nameEq (ChildOf n) n fiber newTable newLifecycle fibers present valid |
    (Yes Refl) = rewrite lookupRuntimeReplaced nameEq n fiber newTable
      newLifecycle fibers present in Refl
  parentInvariantRuntimeRegistry {name} {key} {world} {error} {value}
    nameEq (ChildOf parent) n fiber newTable newLifecycle fibers present valid |
    (No distinct) = rewrite lookupReplaceOther parent n distinct
      (setFiberRuntime fiber newTable newLifecycle) fibers in valid

0 parentsRegistryRuntime :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Just fiber ->
  parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} entries fibers = True ->
  parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} entries
    (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers) = True
parentsRegistryRuntime nameEq [] n fiber newTable newLifecycle fibers present valid =
  Refl
parentsRegistryRuntime {name} {key} {world} {error} {value}
  nameEq (Bind current observed :: rest) n fiber newTable newLifecycle fibers
  present valid = andBothTrue _ _
    (parentInvariantRuntimeRegistry {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq (fiberParent observed) n fiber
      newTable newLifecycle fibers present (andTrueLeft _ _ valid))
    (parentsRegistryRuntime {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq rest n fiber newTable newLifecycle
      fibers present (andTrueRight _ _ valid))

0 parentsEntriesRuntime :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (registry : Registry name key value world error) ->
  lookupEntries @{nameEq} n entries = Just fiber ->
  parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} entries registry = True ->
  parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error}
    (replaceEntries @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) entries) registry = True
parentsEntriesRuntime nameEq [] n fiber newTable newLifecycle registry present valid =
  case present of Refl impossible
parentsEntriesRuntime {name} {key} {world} {error} {value}
  nameEq (Bind current observed :: rest) n fiber newTable newLifecycle registry
  present valid with (decEq @{nameEq} n current)
  parentsEntriesRuntime {name} {key} {world} {error} {value}
    nameEq (Bind n observed :: rest) n fiber newTable newLifecycle registry
    present valid | (Yes Refl) = case present of
      Refl => rewrite setFiberRuntimeParent observed newTable newLifecycle in
        andBothTrue _ _ (andTrueLeft _ _ valid) (andTrueRight _ _ valid)
  parentsEntriesRuntime {name} {key} {world} {error} {value}
    nameEq (Bind current observed :: rest) n fiber newTable newLifecycle registry
    present valid | (No _) = andBothTrue _ _ (andTrueLeft _ _ valid)
      (parentsEntriesRuntime {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq rest n fiber newTable newLifecycle
        registry present (andTrueRight _ _ valid))

0 parentChainRuntimeRegistry :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (fuel : Nat) -> (seen : List name) ->
  (current, n : name) -> (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Just fiber ->
  parentChainInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fuel seen current fibers = True ->
  parentChainInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fuel seen current
    (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers) = True
parentChainRuntimeRegistry nameEq Z seen current n fiber newTable newLifecycle fibers
  present valid = void (falseCannotBeTrue valid)
parentChainRuntimeRegistry {name} {key} {world} {error} {value}
  nameEq (S fuel) seen current n fiber newTable newLifecycle fibers present valid
  with (lookupFiber @{nameEq} current fibers) proof currentLookup
  parentChainRuntimeRegistry {name} {key} {world} {error} {value}
    nameEq (S fuel) seen current n fiber newTable newLifecycle fibers present valid |
    Nothing = void (falseCannotBeTrue valid)
  parentChainRuntimeRegistry {name} {key} {world} {error} {value}
    nameEq (S fuel) seen current n fiber newTable newLifecycle fibers present valid |
    Just observed with (fiberParent observed) proof parentShape
    parentChainRuntimeRegistry {name} {key} {world} {error} {value}
      nameEq (S fuel) seen current n fiber newTable newLifecycle fibers present valid |
      Just observed | Root =
        let frame = runtimeLookupFrame {name = name} {key = key} {world = world}
              {error = error} {value = value} nameEq current n fiber observed
              newTable newLifecycle fibers currentLookup present
        in rewrite framedRuntimeLookup frame in rewrite framedRuntimeParent frame in
          rewrite parentShape in Refl
    parentChainRuntimeRegistry {name} {key} {world} {error} {value}
      nameEq (S fuel) seen current n fiber newTable newLifecycle fibers present valid |
      Just observed | ChildOf parent
      with (elemDec @{nameEq} parent seen) proof parentSeen
      parentChainRuntimeRegistry {name} {key} {world} {error} {value}
        nameEq (S fuel) seen current n fiber newTable newLifecycle fibers present valid |
        Just observed | ChildOf parent | True = void (falseCannotBeTrue valid)
      parentChainRuntimeRegistry {name} {key} {world} {error} {value}
        nameEq (S fuel) seen current n fiber newTable newLifecycle fibers present valid |
        Just observed | ChildOf parent | False =
          let frame = runtimeLookupFrame {name = name} {key = key} {world = world}
                {error = error} {value = value} nameEq current n fiber observed
                newTable newLifecycle fibers currentLookup present
              recursive = parentChainRuntimeRegistry {name = name} {key = key}
                {world = world} {error = error} {value = value} nameEq fuel
                (parent :: seen) parent n fiber newTable newLifecycle fibers
                present valid
          in rewrite framedRuntimeLookup frame in
            rewrite framedRuntimeParent frame in rewrite parentShape in
            rewrite parentSeen in recursive

0 chainsRegistryRuntime :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (fuel : Nat) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Just fiber ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fuel entries fibers = True ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fuel entries
    (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers) = True
chainsRegistryRuntime nameEq fuel [] n fiber newTable newLifecycle fibers present
  valid = Refl
chainsRegistryRuntime {name} {key} {world} {error} {value}
  nameEq fuel (Bind current observed :: rest) n fiber newTable newLifecycle fibers
  present valid = andBothTrue _ _
    (parentChainRuntimeRegistry {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq fuel [current] current n fiber
      newTable newLifecycle fibers present (andTrueLeft _ _ valid))
    (chainsRegistryRuntime {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq fuel rest n fiber newTable
      newLifecycle fibers present (andTrueRight _ _ valid))

0 chainsEntriesRuntime :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (fuel : Nat) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (registry : Registry name key value world error) ->
  lookupEntries @{nameEq} n entries = Just fiber ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fuel entries registry = True ->
  chainsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fuel
    (replaceEntries @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) entries) registry = True
chainsEntriesRuntime nameEq fuel [] n fiber newTable newLifecycle registry present
  valid = case present of Refl impossible
chainsEntriesRuntime {name} {key} {world} {error} {value}
  nameEq fuel (Bind current observed :: rest) n fiber newTable newLifecycle registry
  present valid with (decEq @{nameEq} n current)
  chainsEntriesRuntime {name} {key} {world} {error} {value}
    nameEq fuel (Bind n observed :: rest) n fiber newTable newLifecycle registry
    present valid | (Yes Refl) = case present of Refl => valid
  chainsEntriesRuntime {name} {key} {world} {error} {value}
    nameEq fuel (Bind current observed :: rest) n fiber newTable newLifecycle registry
    present valid | (No _) = andBothTrue _ _ (andTrueLeft _ _ valid)
      (chainsEntriesRuntime {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq fuel rest n fiber newTable
        newLifecycle registry present (andTrueRight _ _ valid))

0 provisionsDisjointRuntimeEntries :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provision : CoeffectSpec key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  lookupEntries @{nameEq} n entries = Just fiber ->
  provisionsDisjointFrom @{keyEq} {value = value} {world = world} {error = error} provision
    (replaceEntries @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) entries) =
  provisionsDisjointFrom @{keyEq} {value = value} {world = world} {error = error} provision entries
provisionsDisjointRuntimeEntries nameEq keyEq provision [] n fiber newTable
  newLifecycle present = case present of Refl impossible
provisionsDisjointRuntimeEntries {name} {key} {world} {error} {value}
  nameEq keyEq provision (Bind current observed :: rest) n fiber newTable
  newLifecycle present with (decEq @{nameEq} n current)
  provisionsDisjointRuntimeEntries {name} {key} {world} {error} {value}
    nameEq keyEq provision (Bind n observed :: rest) n fiber newTable newLifecycle
    present | (Yes Refl) = case present of
      Refl => rewrite setFiberRuntimeProvision observed newTable newLifecycle in
        Refl
  provisionsDisjointRuntimeEntries {name} {key} {world} {error} {value}
    nameEq keyEq provision (Bind current observed :: rest) n fiber newTable
    newLifecycle present | (No _) = cong
      (not (provisionOverlap @{keyEq} provision
        (componentProvisions (fiberComponent observed))) &&)
      (provisionsDisjointRuntimeEntries {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq provision
        rest n fiber newTable newLifecycle present)

0 pairwiseRuntimeEntries :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  lookupEntries @{nameEq} n entries = Just fiber ->
  pairwiseProvisionInvariant @{keyEq} {value = value} {world = world} {error = error}
    (replaceEntries @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) entries) =
  pairwiseProvisionInvariant @{keyEq} {value = value} {world = world} {error = error} entries
pairwiseRuntimeEntries nameEq keyEq [] n fiber newTable newLifecycle present =
  case present of Refl impossible
pairwiseRuntimeEntries {name} {key} {world} {error} {value}
  nameEq keyEq (Bind current observed :: rest) n fiber newTable newLifecycle present
  with (decEq @{nameEq} n current)
  pairwiseRuntimeEntries {name} {key} {world} {error} {value}
    nameEq keyEq (Bind n observed :: rest) n fiber newTable newLifecycle present |
    (Yes Refl) = case present of
      Refl => rewrite setFiberRuntimeProvision observed newTable newLifecycle in
        Refl
  pairwiseRuntimeEntries {name} {key} {world} {error} {value}
    nameEq keyEq (Bind current observed :: rest) n fiber newTable newLifecycle present |
    (No _) = rewrite provisionsDisjointRuntimeEntries {name = name} {key = key}
      {world = world} {error = error} {value = value} nameEq keyEq
      (componentProvisions (fiberComponent observed)) rest n fiber newTable
      newLifecycle present in cong
        (provisionsDisjointFrom @{keyEq}
          (componentProvisions (fiberComponent observed)) rest &&)
        (pairwiseRuntimeEntries {name = name} {key = key} {world = world}
          {error = error} {value = value} nameEq keyEq rest n fiber newTable
          newLifecycle present)

||| Assemble the three structural clauses for an arbitrary runtime replacement;
||| the caller supplies the committed-view clause, which is rule-specific.
public export
0 registryWellFormedRuntimeReplace :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (ambient : world) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Just fiber ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (MkSystemState ambient fibers) = True ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
    (registryFibers {value = value} {world = world} {error = error} (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers))
    (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers) = True ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} (MkSystemState ambient (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers)) = True
registryWellFormedRuntimeReplace {name} {key} {world} {error} {value}
  nameEq keyEq ambient n fiber newTable newLifecycle
  fibers@(MkCoeffectContext entries unique) present valid targetViews =
  let entryPresent = lookupFiberEntries nameEq n fiber fibers present
      sourceParents = andFourFirst
        (parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} entries fibers)
        (chainsInvariant @{nameEq} (S (length entries)) entries fibers)
        (pairwiseProvisionInvariant @{keyEq} {value = value} {world = world} {error = error} entries)
        (viewsInvariant @{nameEq} @{keyEq} entries fibers) valid
      sourceChains = andFourSecond
        (parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} entries fibers)
        (chainsInvariant @{nameEq} (S (length entries)) entries fibers)
        (pairwiseProvisionInvariant @{keyEq} {value = value} {world = world} {error = error} entries)
        (viewsInvariant @{nameEq} @{keyEq} entries fibers) valid
      sourcePairwise = andFourThird
        (parentsInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} entries fibers)
        (chainsInvariant @{nameEq} (S (length entries)) entries fibers)
        (pairwiseProvisionInvariant @{keyEq} {value = value} {world = world} {error = error} entries)
        (viewsInvariant @{nameEq} @{keyEq} entries fibers) valid
      framedParents = parentsRegistryRuntime {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq entries n fiber
        newTable newLifecycle fibers present sourceParents
      targetParents = parentsEntriesRuntime {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq entries n fiber
        newTable newLifecycle
        (replaceBinding @{nameEq} n
          (setFiberRuntime fiber newTable newLifecycle) fibers)
        entryPresent framedParents
      framedChains = chainsRegistryRuntime {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq
        (S (length entries)) entries n fiber newTable newLifecycle fibers present
        sourceChains
      targetChains = chainsEntriesRuntime {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq
        (S (length entries)) entries n fiber newTable newLifecycle
        (replaceBinding @{nameEq} n
          (setFiberRuntime fiber newTable newLifecycle) fibers)
        entryPresent framedChains
      targetPairwise = trans (pairwiseRuntimeEntries {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq entries n
        fiber newTable newLifecycle entryPresent) sourcePairwise
  in rewrite replaceEntriesLength n
      (setFiberRuntime fiber newTable newLifecycle) entries in
    andBothTrue _ _ targetParents
      (andBothTrue _ _ targetChains
        (andBothTrue _ _ targetPairwise targetViews))

0 viewProvidersUnstableRuntime :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (deps : List key) -> (view : View name deps) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Just fiber ->
  stableProvider (fiberLifecycle fiber) = False ->
  viewProvidersInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fibers view = True ->
  viewProvidersInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error}
    (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers) view = True
viewProvidersUnstableRuntime {key} {world} {error} {value}
  nameEq [] EmptyView n fiber newTable newLifecycle fibers present unstable valid =
    Refl
viewProvidersUnstableRuntime {name} {key} {world} {error} {value}
  nameEq (k :: ks) (ProviderView provider rest) n fiber newTable newLifecycle
  fibers present unstable valid with (decEq @{nameEq} provider n)
  viewProvidersUnstableRuntime {name} {key} {world} {error} {value}
    nameEq (k :: ks) (ProviderView n rest) n fiber newTable newLifecycle fibers
    present unstable valid | (Yes Refl) =
      let sourceHead = viewProvidersHeadStable {name = name} {key = key}
            {world = world} {error = error} {value = value} nameEq n k rest
            fibers fiber present valid
      in void (falseCannotBeTrue (trans (sym unstable) sourceHead))
  viewProvidersUnstableRuntime {name} {key} {world} {error} {value}
    nameEq (k :: ks) (ProviderView provider rest) n fiber newTable newLifecycle
    fibers present unstable valid | (No distinct)
    with (lookupFiber @{nameEq} provider fibers) proof providerLookup
    viewProvidersUnstableRuntime {name} {key} {world} {error} {value}
      nameEq (k :: ks) (ProviderView provider rest) n fiber newTable newLifecycle
      fibers present unstable valid | (No distinct) | Nothing =
        void (falseCannotBeTrue valid)
    viewProvidersUnstableRuntime {name} {key} {world} {error} {value}
      nameEq (k :: ks) (ProviderView provider rest) n fiber newTable newLifecycle
      fibers present unstable valid | (No distinct) | Just providerFiber =
        let targetLookup = trans (lookupReplaceOther provider n distinct
              (setFiberRuntime fiber newTable newLifecycle) fibers) providerLookup
            sourceHead = andTrueLeft _ _ valid
            sourceTail = andTrueRight _ _ valid
            targetTail = viewProvidersUnstableRuntime {name = name} {key = key}
              {world = world} {error = error} {value = value} nameEq ks rest n
              fiber newTable newLifecycle fibers present unstable sourceTail
        in rewrite targetLookup in andBothTrue _ _ sourceHead targetTail

0 valueFromProviderRuntimeOther :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider, n : name) -> Not (provider = n) -> (k : key) ->
  (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (fibers : Registry name key value world error) ->
  valueFromProvider @{nameEq} @{keyEq} {value = value} {world = world} {error = error} provider k
    (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers) =
  valueFromProvider @{nameEq} @{keyEq} {value = value} {world = world} {error = error} provider k fibers
valueFromProviderRuntimeOther {key} {world} {error} {value}
  nameEq keyEq provider n distinct k fiber newTable newLifecycle fibers
  with (lookupFiber @{nameEq} provider fibers) proof original
  valueFromProviderRuntimeOther {key} {world} {error} {value}
    nameEq keyEq provider n distinct k fiber newTable newLifecycle fibers |
    Nothing = rewrite lookupReplaceOther provider n distinct
      (setFiberRuntime fiber newTable newLifecycle) fibers in
      rewrite original in Refl
  valueFromProviderRuntimeOther {key} {world} {error} {value}
    nameEq keyEq provider n distinct k fiber newTable newLifecycle fibers |
    Just providerFiber = rewrite lookupReplaceOther provider n distinct
      (setFiberRuntime fiber newTable newLifecycle) fibers in
      rewrite original in Refl

0 resolveCommittedValuesUnstableRuntime :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Just fiber ->
  stableProvider (fiberLifecycle fiber) = False ->
  viewProvidersInvariant @{nameEq} {key = key} {value = value} {world = world} {error = error} fibers view = True ->
  resolveCommittedValues @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps view
    (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers) =
  resolveCommittedValues @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps view fibers
resolveCommittedValuesUnstableRuntime {key} {world} {error} {value}
  nameEq keyEq [] EmptyView n fiber newTable newLifecycle fibers present unstable
  providersValid = Refl
resolveCommittedValuesUnstableRuntime {name} {key} {world} {error} {value}
  nameEq keyEq (k :: ks) (ProviderView provider rest) n fiber newTable
  newLifecycle fibers present unstable providersValid
  with (decEq @{nameEq} provider n)
  resolveCommittedValuesUnstableRuntime {name} {key} {world} {error} {value}
    nameEq keyEq (k :: ks) (ProviderView n rest) n fiber newTable newLifecycle
    fibers present unstable providersValid | (Yes Refl) =
      let sourceHead = viewProvidersHeadStable {name = name} {key = key}
            {world = world} {error = error} {value = value} nameEq n k rest
            fibers fiber present providersValid
      in void (falseCannotBeTrue (trans (sym unstable) sourceHead))
  resolveCommittedValuesUnstableRuntime {name} {key} {world} {error} {value}
    nameEq keyEq (k :: ks) (ProviderView provider rest) n fiber newTable
    newLifecycle fibers present unstable providersValid | (No distinct)
    with (valueFromProvider @{nameEq} @{keyEq} {value = value} {world = world} {error = error} provider k fibers) proof original
    resolveCommittedValuesUnstableRuntime {name} {key} {world} {error} {value}
      nameEq keyEq (k :: ks) (ProviderView provider rest) n fiber newTable
      newLifecycle fibers present unstable providersValid | (No distinct) |
      Nothing =
        let target = trans (valueFromProviderRuntimeOther {name = name}
              {key = key} {world = world} {error = error} {value = value}
              nameEq keyEq provider n distinct k fiber newTable newLifecycle fibers)
              original
        in rewrite target in Refl
    resolveCommittedValuesUnstableRuntime {name} {key} {world} {error} {value}
      nameEq keyEq (k :: ks) (ProviderView provider rest) n fiber newTable
      newLifecycle fibers present unstable providersValid | (No distinct) |
      Just v =
        let target = trans (valueFromProviderRuntimeOther {name = name}
              {key = key} {world = world} {error = error} {value = value}
              nameEq keyEq provider n distinct k fiber newTable newLifecycle fibers)
              original
            tailValid = viewProvidersTailValid {name = name} {key = key}
              {world = world} {error = error} {value = value} nameEq provider k
              rest fibers providersValid
            tailFrame = resolveCommittedValuesUnstableRuntime {name = name}
              {key = key} {world = world} {error = error} {value = value}
              nameEq keyEq ks rest n fiber newTable newLifecycle fibers present
              unstable tailValid
        in rewrite target in cong (map (OneDepValue v)) tailFrame

public export
0 viewBindingsUnstableRuntime :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Just fiber ->
  stableProvider (fiberLifecycle fiber) = False ->
  viewBindingsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps view fibers = True ->
  viewBindingsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps view
    (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers) = True
viewBindingsUnstableRuntime {name} {key} {world} {error} {value}
  nameEq keyEq deps view n fiber newTable newLifecycle fibers present unstable
  valid =
  let sourceProviders = andTrueLeft _ _ valid
      sourceValues = andTrueRight _ _ valid
      targetProviders = viewProvidersUnstableRuntime {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq deps view n fiber
        newTable newLifecycle fibers present unstable sourceProviders
      valuesFrame = resolveCommittedValuesUnstableRuntime {name = name}
        {key = key} {world = world} {error = error} {value = value} nameEq keyEq
        deps view n fiber newTable newLifecycle fibers present unstable
        sourceProviders
      targetValues = trans (cong isJust valuesFrame) sourceValues
  in andBothTrue _ _ targetProviders targetValues

0 fiberViewUnstableRuntime :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (observed : Fiber name key value world error) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Just fiber ->
  stableProvider (fiberLifecycle fiber) = False ->
  fiberViewInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} observed fibers = True ->
  fiberViewInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} observed
    (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers) = True
fiberViewUnstableRuntime {name} {key} {world} {error} {value}
  nameEq keyEq (MkFiber component parent retired table (Inactive outcome)) n fiber
  newTable newLifecycle fibers present unstable valid = Refl
fiberViewUnstableRuntime {name} {key} {world} {error} {value}
  nameEq keyEq (MkFiber component parent retired table
    (Reloading rest accumulator view)) n fiber newTable newLifecycle fibers present
    unstable valid = viewBindingsUnstableRuntime {name = name} {key = key}
      {world = world} {error = error} {value = value} nameEq keyEq
      (dependencies (componentDependencies component)) view n fiber newTable
      newLifecycle fibers present unstable valid
fiberViewUnstableRuntime {name} {key} {world} {error} {value}
  nameEq keyEq (MkFiber component parent retired table (Active accumulator view))
  n fiber newTable newLifecycle fibers present unstable valid =
    viewBindingsUnstableRuntime {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq keyEq
      (dependencies (componentDependencies component)) view n fiber newTable
      newLifecycle fibers present unstable valid
fiberViewUnstableRuntime {name} {key} {world} {error} {value}
  nameEq keyEq (MkFiber component parent retired table
    (Unloading accumulator view outcome)) n fiber newTable newLifecycle fibers
    present unstable valid = viewBindingsUnstableRuntime {name = name} {key = key}
      {world = world} {error = error} {value = value} nameEq keyEq
      (dependencies (componentDependencies component)) view n fiber newTable
      newLifecycle fibers present unstable valid

0 viewsRegistryUnstableRuntime :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Just fiber ->
  stableProvider (fiberLifecycle fiber) = False ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries fibers = True ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries
    (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers) = True
viewsRegistryUnstableRuntime nameEq keyEq [] n fiber newTable newLifecycle fibers
  present unstable valid = Refl
viewsRegistryUnstableRuntime {name} {key} {world} {error} {value}
  nameEq keyEq (Bind current observed :: rest) n fiber newTable newLifecycle fibers
  present unstable valid = andBothTrue _ _
    (fiberViewUnstableRuntime {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq keyEq observed n fiber newTable
      newLifecycle fibers present unstable (andTrueLeft _ _ valid))
    (viewsRegistryUnstableRuntime {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq keyEq rest n fiber newTable
      newLifecycle fibers present unstable (andTrueRight _ _ valid))

0 viewsEntriesRuntimeTarget :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (fiber, replacement : Fiber name key value world error) ->
  (registry : Registry name key value world error) ->
  lookupEntries @{nameEq} n entries = Just fiber ->
  fiberViewInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} replacement registry = True ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries registry = True ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
    (replaceEntries @{nameEq} n replacement entries) registry = True
viewsEntriesRuntimeTarget nameEq keyEq [] n fiber replacement registry present
  targetSelected valid = case present of Refl impossible
viewsEntriesRuntimeTarget {name} {key} {world} {error} {value}
  nameEq keyEq (Bind current observed :: rest) n fiber replacement registry present
  targetSelected valid with (decEq @{nameEq} n current)
  viewsEntriesRuntimeTarget {name} {key} {world} {error} {value}
    nameEq keyEq (Bind n observed :: rest) n fiber replacement registry present
    targetSelected valid | (Yes Refl) = case present of
      Refl => andBothTrue _ _ targetSelected (andTrueRight _ _ valid)
  viewsEntriesRuntimeTarget {name} {key} {world} {error} {value}
    nameEq keyEq (Bind current observed :: rest) n fiber replacement registry present
    targetSelected valid | (No _) = andBothTrue _ _ (andTrueLeft _ _ valid)
      (viewsEntriesRuntimeTarget {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq keyEq rest n fiber replacement
        registry present targetSelected (andTrueRight _ _ valid))

public export
0 viewsInvariantLookup :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : name) -> (fiber : Fiber name key value world error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (registry : Registry name key value world error) ->
  lookupEntries @{nameEq} wanted entries = Just fiber ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries registry = True ->
  fiberViewInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} fiber registry = True
viewsInvariantLookup nameEq keyEq wanted fiber [] registry present valid =
  case present of Refl impossible
viewsInvariantLookup {name} {key} {world} {error} {value}
  nameEq keyEq wanted fiber (Bind current observed :: rest) registry present valid
  with (decEq @{nameEq} wanted current)
  viewsInvariantLookup {name} {key} {world} {error} {value}
    nameEq keyEq current fiber (Bind current observed :: rest) registry present
    valid | (Yes Refl) = case justValuesEqual present of
      Refl => andTrueLeft _ _ valid
  viewsInvariantLookup {name} {key} {world} {error} {value}
    nameEq keyEq wanted fiber (Bind current observed :: rest) registry present
    valid | (No _) = viewsInvariantLookup {name = name} {key = key}
      {world = world} {error = error} {value = value} nameEq keyEq wanted fiber
      rest registry present (andTrueRight _ _ valid)

public export
0 viewsInvariantUnstableRuntimeReplace :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = Just fiber ->
  stableProvider (fiberLifecycle fiber) = False ->
  fiberViewInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
    (setFiberRuntime fiber newTable newLifecycle)
    (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers) = True ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (registryFibers {value = value} {world = world} {error = error} fibers) fibers = True ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
    (registryFibers {value = value} {world = world} {error = error} (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers))
    (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers) = True
viewsInvariantUnstableRuntimeReplace {name} {key} {world} {error} {value}
  nameEq keyEq n fiber newTable newLifecycle
  fibers@(MkCoeffectContext entries unique) present unstable targetSelected valid =
  let entryPresent = lookupFiberEntries nameEq n fiber fibers present
      framed = viewsRegistryUnstableRuntime {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq entries n fiber
        newTable newLifecycle fibers present unstable valid
  in viewsEntriesRuntimeTarget {name = name} {key = key} {world = world}
    {error = error} {value = value} nameEq keyEq entries n fiber
    (setFiberRuntime fiber newTable newLifecycle)
    (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers)
    entryPresent targetSelected framed

0 viewProvidersRuntimeExcluded :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (deps : List key) -> (view : View name deps) ->
  (n : name) -> viewContains @{nameEq} n view = False ->
  (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (fibers : Registry name key value world error) ->
  viewProvidersInvariant @{nameEq} {key = key} {value = value} {world = world}
    {error = error}
    (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers) view =
  viewProvidersInvariant @{nameEq} {key = key} {value = value} {world = world}
    {error = error} fibers view
viewProvidersRuntimeExcluded nameEq [] EmptyView n excluded fiber newTable
  newLifecycle fibers = Refl
viewProvidersRuntimeExcluded {name} {key} {world} {error} {value}
  nameEq (k :: ks) (ProviderView provider rest) n excluded fiber newTable
  newLifecycle fibers with (decEq @{nameEq} n provider)
  viewProvidersRuntimeExcluded {name} {key} {world} {error} {value}
    nameEq (k :: ks) (ProviderView n rest) n excluded fiber newTable newLifecycle
    fibers | (Yes Refl) = void (trueNotFalse excluded)
  viewProvidersRuntimeExcluded {name} {key} {world} {error} {value}
    nameEq (k :: ks) (ProviderView provider rest) n excluded fiber newTable
    newLifecycle fibers | (No notSame)
    with (lookupFiber @{nameEq} provider fibers) proof original
    viewProvidersRuntimeExcluded {name} {key} {world} {error} {value}
      nameEq (k :: ks) (ProviderView provider rest) n excluded fiber newTable
      newLifecycle fibers | (No notSame) | Nothing =
        let distinct : Not (provider = n)
            distinct same = notSame (sym same)
        in rewrite lookupReplaceOther provider n distinct
          (setFiberRuntime fiber newTable newLifecycle) fibers in
          rewrite original in Refl
    viewProvidersRuntimeExcluded {name} {key} {world} {error} {value}
      nameEq (k :: ks) (ProviderView provider rest) n excluded fiber newTable
      newLifecycle fibers | (No notSame) | Just providerFiber =
        let distinct : Not (provider = n)
            distinct same = notSame (sym same)
        in rewrite lookupReplaceOther provider n distinct
          (setFiberRuntime fiber newTable newLifecycle) fibers in
          rewrite original in cong (stableProvider (fiberLifecycle providerFiber) &&)
            (viewProvidersRuntimeExcluded {name = name} {key = key}
              {world = world} {error = error} {value = value} nameEq ks rest n
              excluded fiber newTable newLifecycle fibers)

0 resolveCommittedValuesRuntimeExcluded :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  (n : name) -> viewContains @{nameEq} n view = False ->
  (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (fibers : Registry name key value world error) ->
  resolveCommittedValues @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} deps view
    (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers) =
  resolveCommittedValues @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} deps view fibers
resolveCommittedValuesRuntimeExcluded nameEq keyEq [] EmptyView n excluded fiber
  newTable newLifecycle fibers = Refl
resolveCommittedValuesRuntimeExcluded {name} {key} {world} {error} {value}
  nameEq keyEq (k :: ks) (ProviderView provider rest) n excluded fiber newTable
  newLifecycle fibers with (decEq @{nameEq} n provider)
  resolveCommittedValuesRuntimeExcluded {name} {key} {world} {error} {value}
    nameEq keyEq (k :: ks) (ProviderView n rest) n excluded fiber newTable
    newLifecycle fibers | (Yes Refl) = void (trueNotFalse excluded)
  resolveCommittedValuesRuntimeExcluded {name} {key} {world} {error} {value}
    nameEq keyEq (k :: ks) (ProviderView provider rest) n excluded fiber newTable
    newLifecycle fibers | (No notSame)
    with (valueFromProvider @{nameEq} @{keyEq} provider k fibers) proof original
    resolveCommittedValuesRuntimeExcluded {name} {key} {world} {error} {value}
      nameEq keyEq (k :: ks) (ProviderView provider rest) n excluded fiber newTable
      newLifecycle fibers | (No notSame) | Nothing =
        let distinct : Not (provider = n)
            distinct same = notSame (sym same)
            target = trans (valueFromProviderRuntimeOther {name = name}
              {key = key} {world = world} {error = error} {value = value}
              nameEq keyEq provider n distinct k fiber newTable newLifecycle fibers)
              original
        in rewrite target in Refl
    resolveCommittedValuesRuntimeExcluded {name} {key} {world} {error} {value}
      nameEq keyEq (k :: ks) (ProviderView provider rest) n excluded fiber newTable
      newLifecycle fibers | (No notSame) | Just v =
        let distinct : Not (provider = n)
            distinct same = notSame (sym same)
            target = trans (valueFromProviderRuntimeOther {name = name}
              {key = key} {world = world} {error = error} {value = value}
              nameEq keyEq provider n distinct k fiber newTable newLifecycle fibers)
              original
        in rewrite target in cong (map (OneDepValue v))
          (resolveCommittedValuesRuntimeExcluded {name = name} {key = key}
            {world = world} {error = error} {value = value} nameEq keyEq ks rest
            n excluded fiber newTable newLifecycle fibers)

public export
0 viewBindingsRuntimeExcluded :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  (n : name) -> viewContains @{nameEq} n view = False ->
  (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (fibers : Registry name key value world error) ->
  viewBindingsInvariant @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} deps view
    (replaceBinding @{nameEq} n
      (setFiberRuntime fiber newTable newLifecycle) fibers) =
  viewBindingsInvariant @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} deps view fibers
viewBindingsRuntimeExcluded {name} {key} {world} {error} {value}
  nameEq keyEq deps view n excluded fiber newTable newLifecycle fibers =
  rewrite viewProvidersRuntimeExcluded {name = name} {key = key} {world = world}
    {error = error} {value = value} nameEq deps view n excluded fiber newTable
    newLifecycle fibers in
  rewrite cong isJust (resolveCommittedValuesRuntimeExcluded {name = name}
    {key = key} {world = world} {error = error} {value = value} nameEq keyEq
    deps view n excluded fiber newTable newLifecycle fibers) in Refl

0 reliedHeadReloadingOther :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (n, current : name) -> Not (current = n) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  reliedHead @{nameEq} n n
    (Bind current (MkFiber component parent retired table
      (Reloading remaining accumulator view))) = viewContains @{nameEq} n view
reliedHeadReloadingOther nameEq n current distinct component parent retired table
  remaining accumulator view with (decEq @{nameEq} current n)
  reliedHeadReloadingOther nameEq n n distinct component parent retired table
    remaining accumulator view | (Yes Refl) = void (distinct Refl)
  reliedHeadReloadingOther nameEq n current distinct component parent retired table
    remaining accumulator view | (No _) = Refl

0 reliedHeadActiveOther :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (n, current : name) -> Not (current = n) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  reliedHead @{nameEq} n n
    (Bind current (MkFiber component parent retired table
      (Active accumulator view))) = viewContains @{nameEq} n view
reliedHeadActiveOther nameEq n current distinct component parent retired table
  accumulator view with (decEq @{nameEq} current n)
  reliedHeadActiveOther nameEq n n distinct component parent retired table
    accumulator view | (Yes Refl) = void (distinct Refl)
  reliedHeadActiveOther nameEq n current distinct component parent retired table
    accumulator view | (No _) = Refl

0 reliedHeadUnloadingOther :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (n, current : name) -> Not (current = n) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (outcome : Maybe error) ->
  reliedHead @{nameEq} n n
    (Bind current (MkFiber component parent retired table
      (Unloading accumulator view outcome))) = viewContains @{nameEq} n view
reliedHeadUnloadingOther nameEq n current distinct component parent retired table
  accumulator view outcome with (decEq @{nameEq} current n)
  reliedHeadUnloadingOther nameEq n n distinct component parent retired table
    accumulator view outcome | (Yes Refl) = void (distinct Refl)
  reliedHeadUnloadingOther nameEq n current distinct component parent retired table
    accumulator view outcome | (No _) = Refl

0 fiberViewUnloadOther :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (n, current : name) -> Not (current = n) ->
  (observed : Fiber name key value world error) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (outcome : Maybe error) ->
  (newTable : OwnedTable key value (componentProvisions component)) ->
  (fibers : Registry name key value world error) ->
  reliedOnBy @{nameEq} {key = key} {value = value} {world = world} {error = error} n n (Bind current observed :: rest) = False ->
  fiberViewInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} observed fibers = True ->
  fiberViewInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} observed
    (replaceBinding @{nameEq} n
      (MkFiber component parent retired newTable (Inactive outcome)) fibers) = True
fiberViewUnloadOther nameEq keyEq n current distinct
  (MkFiber ownComponent ownParent ownRetired ownTable (Inactive ownOutcome)) rest
  component parent retired table accumulator view outcome newTable fibers relied
  valid = Refl
fiberViewUnloadOther {name} {key} {world} {error} {value}
  nameEq keyEq n current distinct
  (MkFiber ownComponent ownParent ownRetired ownTable
    (Reloading remaining ownAccumulator ownView)) rest component parent retired
  table accumulator view outcome newTable fibers relied valid =
  let headFalse = boolOrLeftFalse _ _ relied
      excluded = trans (sym (reliedHeadReloadingOther {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq n current distinct
        ownComponent ownParent ownRetired ownTable remaining ownAccumulator
        ownView)) headFalse
  in trans (viewBindingsRuntimeExcluded {name = name} {key = key}
      {world = world} {error = error} {value = value} nameEq keyEq
      (dependencies (componentDependencies ownComponent)) ownView n excluded
      (MkFiber component parent retired table (Unloading accumulator view outcome))
      newTable (Inactive outcome) fibers) valid
fiberViewUnloadOther {name} {key} {world} {error} {value}
  nameEq keyEq n current distinct
  (MkFiber ownComponent ownParent ownRetired ownTable
    (Active ownAccumulator ownView)) rest component parent retired table
  accumulator view outcome newTable fibers relied valid =
  let headFalse = boolOrLeftFalse _ _ relied
      excluded = trans (sym (reliedHeadActiveOther {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq n current distinct
        ownComponent ownParent ownRetired ownTable ownAccumulator ownView))
        headFalse
  in trans (viewBindingsRuntimeExcluded {name = name} {key = key}
      {world = world} {error = error} {value = value} nameEq keyEq
      (dependencies (componentDependencies ownComponent)) ownView n excluded
      (MkFiber component parent retired table (Unloading accumulator view outcome))
      newTable (Inactive outcome) fibers) valid
fiberViewUnloadOther {name} {key} {world} {error} {value}
  nameEq keyEq n current distinct
  (MkFiber ownComponent ownParent ownRetired ownTable
    (Unloading ownAccumulator ownView ownOutcome)) rest component parent retired
  table accumulator view outcome newTable fibers relied valid =
  let headFalse = boolOrLeftFalse _ _ relied
      excluded = trans (sym (reliedHeadUnloadingOther {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq n current distinct
        ownComponent ownParent ownRetired ownTable ownAccumulator ownView
        ownOutcome)) headFalse
  in trans (viewBindingsRuntimeExcluded {name = name} {key = key}
      {world = world} {error = error} {value = value} nameEq keyEq
      (dependencies (componentDependencies ownComponent)) ownView n excluded
      (MkFiber component parent retired table (Unloading accumulator view outcome))
      newTable (Inactive outcome) fibers) valid

0 viewsEntriesUnloadAfter :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  Not (Elem n (bindingKeys entries)) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (outcome : Maybe error) ->
  (newTable : OwnedTable key value (componentProvisions component)) ->
  (fibers : Registry name key value world error) ->
  reliedOnBy @{nameEq} {key = key} {value = value} {world = world} {error = error} n n entries = False ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries fibers = True ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries
    (replaceBinding @{nameEq} n
      (MkFiber component parent retired newTable (Inactive outcome)) fibers) = True
viewsEntriesUnloadAfter nameEq keyEq n [] absent component parent retired table
  accumulator view outcome newTable fibers relied valid = Refl
viewsEntriesUnloadAfter {name} {key} {world} {error} {value}
  nameEq keyEq n (Bind current observed :: rest) absent component parent retired
  table accumulator view outcome newTable fibers relied valid =
  let distinct : Not (current = n)
      distinct same = absent
        (replace {p = \candidate => Elem candidate
          (current :: bindingKeys rest)} same Here)
      0 targetHead : (fiberViewInvariant @{nameEq} @{keyEq} {value = value}
        {world = world} {error = error} observed
        (replaceBinding @{nameEq} n
          (MkFiber component parent retired newTable (Inactive outcome)) fibers) =
        True)
      targetHead = fiberViewUnloadOther {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq n current
        distinct observed rest component parent retired table accumulator view
        outcome newTable fibers relied (andTrueLeft _ _ valid)
      tailAbsent : Not (Elem n (bindingKeys rest))
      tailAbsent later = absent (There later)
      0 tailRelied : (reliedOnBy @{nameEq} {key = key} {value = value}
        {world = world} {error = error} n n rest = False)
      tailRelied = boolOrRightFalse
        (reliedHead @{nameEq} n n (Bind current observed))
        (reliedOnBy @{nameEq} {key = key} {value = value} {world = world} {error = error} n n rest) relied
      0 targetTail : (viewsInvariant @{nameEq} @{keyEq} {value = value}
        {world = world} {error = error} rest
        (replaceBinding @{nameEq} n
          (MkFiber component parent retired newTable (Inactive outcome)) fibers) =
        True)
      targetTail = viewsEntriesUnloadAfter {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq n rest
        tailAbsent component parent retired table accumulator view outcome newTable
        fibers tailRelied (andTrueRight _ _ valid)
  in andBothTrue _ _ targetHead targetTail

0 viewsEntriesUnloadBefore :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  UniqueKeys (bindingKeys entries) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (outcome : Maybe error) ->
  (newTable : OwnedTable key value (componentProvisions component)) ->
  (fibers : Registry name key value world error) ->
  lookupEntries @{nameEq} n entries =
    Just (MkFiber component parent retired table
      (Unloading accumulator view outcome)) ->
  reliedOnBy @{nameEq} {key = key} {value = value} {world = world} {error = error} n n entries = False ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries fibers = True ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
    (replaceEntries @{nameEq} n
      (MkFiber component parent retired newTable (Inactive outcome)) entries)
    (replaceBinding @{nameEq} n
      (MkFiber component parent retired newTable (Inactive outcome)) fibers) = True
viewsEntriesUnloadBefore nameEq keyEq n [] UniqueNil component parent retired table
  accumulator view outcome newTable fibers present relied valid =
  case present of Refl impossible
viewsEntriesUnloadBefore {name} {key} {world} {error} {value}
  nameEq keyEq n (Bind current observed :: rest) (UniqueCons headFresh tailUnique)
  component parent retired table accumulator view outcome newTable fibers present
  relied valid with (decEq @{nameEq} n current)
  viewsEntriesUnloadBefore {name} {key} {world} {error} {value}
    nameEq keyEq current (Bind current observed :: rest)
    (UniqueCons headFresh tailUnique) component parent retired table accumulator view
    outcome newTable fibers present relied valid | (Yes Refl) = case present of
      Refl =>
        let 0 tailRelied : (reliedOnBy @{nameEq} {key = key} {value = value}
              {world = world} {error = error} current current rest = False)
            tailRelied = boolOrRightFalse
              (reliedHead @{nameEq} current current
                (Bind current (MkFiber component parent retired table
                  (Unloading accumulator view outcome))))
              (reliedOnBy @{nameEq} current current rest) relied
            0 targetTail : (viewsInvariant @{nameEq} @{keyEq} {value = value}
              {world = world} {error = error} rest
              (replaceBinding @{nameEq} current
                (MkFiber component parent retired newTable (Inactive outcome))
                fibers) = True)
            targetTail = viewsEntriesUnloadAfter {name = name} {key = key}
              {world = world} {error = error} {value = value} nameEq keyEq current
              rest headFresh component parent retired table accumulator view
              outcome newTable fibers tailRelied (andTrueRight _ _ valid)
        in andBothTrue _ _ Refl targetTail
  viewsEntriesUnloadBefore {name} {key} {world} {error} {value}
    nameEq keyEq n (Bind current observed :: rest) (UniqueCons headFresh tailUnique)
    component parent retired table accumulator view outcome newTable fibers present
    relied valid | (No notSame) =
      let distinct : Not (current = n)
          distinct same = notSame (sym same)
          0 targetHead : (fiberViewInvariant @{nameEq} @{keyEq} {value = value}
            {world = world} {error = error} observed
            (replaceBinding @{nameEq} n
              (MkFiber component parent retired newTable (Inactive outcome))
              fibers) = True)
          targetHead = fiberViewUnloadOther {name = name} {key = key}
            {world = world} {error = error} {value = value} nameEq keyEq n current
            distinct observed rest component parent retired table accumulator view
            outcome newTable fibers relied (andTrueLeft _ _ valid)
          0 tailRelied : (reliedOnBy @{nameEq} {key = key} {value = value}
            {world = world} {error = error} n n rest = False)
          tailRelied = boolOrRightFalse
            (reliedHead @{nameEq} n n (Bind current observed))
            (reliedOnBy @{nameEq} {key = key} {value = value} {world = world} {error = error} n n rest) relied
          0 targetTail : (viewsInvariant @{nameEq} @{keyEq} {value = value}
            {world = world} {error = error}
            (replaceEntries @{nameEq} n
              (MkFiber component parent retired newTable (Inactive outcome)) rest)
            (replaceBinding @{nameEq} n
              (MkFiber component parent retired newTable (Inactive outcome))
              fibers) = True)
          targetTail = viewsEntriesUnloadBefore {name = name} {key = key}
            {world = world} {error = error} {value = value} nameEq keyEq n rest
            tailUnique component parent retired table accumulator view outcome
            newTable fibers present tailRelied (andTrueRight _ _ valid)
      in andBothTrue _ _ targetHead targetTail

public export
0 viewsInvariantUnloadingInactive :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (outcome : Maybe error) ->
  (newTable : OwnedTable key value (componentProvisions component)) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers =
    Just (MkFiber component parent retired table
      (Unloading accumulator view outcome)) ->
  relied @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers = False ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (registryFibers {value = value} {world = world} {error = error} fibers) fibers = True ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
    (registryFibers {value = value} {world = world} {error = error} (replaceBinding @{nameEq} n
      (MkFiber component parent retired newTable (Inactive outcome)) fibers))
    (replaceBinding @{nameEq} n
      (MkFiber component parent retired newTable (Inactive outcome)) fibers) = True
viewsInvariantUnloadingInactive {name} {key} {world} {error} {value}
  nameEq keyEq n component parent retired table accumulator view outcome newTable
  fibers@(MkCoeffectContext entries unique) present notRelied valid =
  viewsEntriesUnloadBefore {name = name} {key = key} {world = world}
    {error = error} {value = value} nameEq keyEq n entries unique component parent
    retired table accumulator view outcome newTable fibers present notRelied valid

0 viewProvidersActiveUnload :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (deps : List key) -> (observed : View name deps) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} n fibers =
    Just (MkFiber component parent retired table (Active accumulator view)) ->
  viewProvidersInvariant @{nameEq} {key = key} {value = value} {world = world}
    {error = error}
    (replaceBinding @{nameEq} n
      (MkFiber component parent retired table
        (Unloading accumulator view Nothing)) fibers) observed =
  viewProvidersInvariant @{nameEq} {key = key} {value = value} {world = world}
    {error = error} fibers observed
viewProvidersActiveUnload nameEq [] EmptyView n component parent retired table
  accumulator view fibers present = Refl
viewProvidersActiveUnload {name} {key} {world} {error} {value}
  nameEq (k :: ks) (ProviderView provider rest) n component parent retired table
  accumulator view fibers present with (decEq @{nameEq} provider n)
  viewProvidersActiveUnload {name} {key} {world} {error} {value}
    nameEq (k :: ks) (ProviderView n rest) n component parent retired table
    accumulator view fibers present | (Yes Refl) =
      rewrite lookupRuntimeReplaced nameEq n
        (MkFiber component parent retired table (Active accumulator view)) table
        (Unloading accumulator view Nothing) fibers present in
      rewrite present in cong (True &&)
        (viewProvidersActiveUnload {name = name} {key = key} {world = world}
          {error = error} {value = value} nameEq ks rest n component parent
          retired table accumulator view fibers present)
  viewProvidersActiveUnload {name} {key} {world} {error} {value}
    nameEq (k :: ks) (ProviderView provider rest) n component parent retired table
    accumulator view fibers present | (No distinct)
    with (lookupFiber @{nameEq} provider fibers) proof original
    viewProvidersActiveUnload {name} {key} {world} {error} {value}
      nameEq (k :: ks) (ProviderView provider rest) n component parent retired table
      accumulator view fibers present | (No distinct) | Nothing =
        rewrite lookupReplaceOther provider n distinct
          (MkFiber component parent retired table
            (Unloading accumulator view Nothing)) fibers in
        rewrite original in Refl
    viewProvidersActiveUnload {name} {key} {world} {error} {value}
      nameEq (k :: ks) (ProviderView provider rest) n component parent retired table
      accumulator view fibers present | (No distinct) | Just providerFiber =
        rewrite lookupReplaceOther provider n distinct
          (MkFiber component parent retired table
            (Unloading accumulator view Nothing)) fibers in
        rewrite original in cong (stableProvider (fiberLifecycle providerFiber) &&)
          (viewProvidersActiveUnload {name = name} {key = key} {world = world}
            {error = error} {value = value} nameEq ks rest n component parent
            retired table accumulator view fibers present)

public export
0 valueFromProviderActiveUnload :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider : name) -> (k : key) -> (n : name) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} n fibers =
    Just (MkFiber component parent retired table (Active accumulator view)) ->
  valueFromProvider @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} provider k
    (replaceBinding @{nameEq} n
      (MkFiber component parent retired table
        (Unloading accumulator view Nothing)) fibers) =
  valueFromProvider @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} provider k fibers
valueFromProviderActiveUnload {name} {key} {world} {error} {value}
  nameEq keyEq provider k n component parent retired table accumulator view fibers
  present with (decEq @{nameEq} provider n)
  valueFromProviderActiveUnload {name} {key} {world} {error} {value}
    nameEq keyEq n k n component parent retired table accumulator view fibers
    present | (Yes Refl) =
      rewrite lookupRuntimeReplaced nameEq n
        (MkFiber component parent retired table (Active accumulator view)) table
        (Unloading accumulator view Nothing) fibers present in
      rewrite present in Refl
  valueFromProviderActiveUnload {name} {key} {world} {error} {value}
    nameEq keyEq provider k n component parent retired table accumulator view fibers
    present | (No distinct) with (lookupFiber @{nameEq} provider fibers) proof original
    valueFromProviderActiveUnload {name} {key} {world} {error} {value}
      nameEq keyEq provider k n component parent retired table accumulator view fibers
      present | (No distinct) | Nothing =
        rewrite lookupReplaceOther provider n distinct
          (MkFiber component parent retired table
            (Unloading accumulator view Nothing)) fibers in
        rewrite original in Refl
    valueFromProviderActiveUnload {name} {key} {world} {error} {value}
      nameEq keyEq provider k n component parent retired table accumulator view fibers
      present | (No distinct) | Just providerFiber =
        rewrite lookupReplaceOther provider n distinct
          (MkFiber component parent retired table
            (Unloading accumulator view Nothing)) fibers in
        rewrite original in Refl

0 resolveCommittedValuesActiveUnload :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (observed : View name deps) -> (n : name) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers =
    Just (MkFiber component parent retired table (Active accumulator view)) ->
  resolveCommittedValues @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps observed
    (replaceBinding @{nameEq} n
      (MkFiber component parent retired table
        (Unloading accumulator view Nothing)) fibers) =
  resolveCommittedValues @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps observed fibers
resolveCommittedValuesActiveUnload nameEq keyEq [] EmptyView n component parent
  retired table accumulator view fibers present = Refl
resolveCommittedValuesActiveUnload {name} {key} {world} {error} {value}
  nameEq keyEq (k :: ks) (ProviderView provider rest) n component parent retired
  table accumulator view fibers present
  with (valueFromProvider @{nameEq} @{keyEq} provider k fibers) proof original
  resolveCommittedValuesActiveUnload {name} {key} {world} {error} {value}
    nameEq keyEq (k :: ks) (ProviderView provider rest) n component parent retired
    table accumulator view fibers present | Nothing =
      let target = trans (valueFromProviderActiveUnload {name = name} {key = key}
            {world = world} {error = error} {value = value} nameEq keyEq provider
            k n component parent retired table accumulator view fibers present)
            original
      in rewrite target in Refl
  resolveCommittedValuesActiveUnload {name} {key} {world} {error} {value}
    nameEq keyEq (k :: ks) (ProviderView provider rest) n component parent retired
    table accumulator view fibers present | Just v =
      let target = trans (valueFromProviderActiveUnload {name = name} {key = key}
            {world = world} {error = error} {value = value} nameEq keyEq provider
            k n component parent retired table accumulator view fibers present)
            original
      in rewrite target in cong (map (OneDepValue v))
        (resolveCommittedValuesActiveUnload {name = name} {key = key}
          {world = world} {error = error} {value = value} nameEq keyEq ks rest n
          component parent retired table accumulator view fibers present)

0 viewBindingsActiveUnload :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (observed : View name deps) -> (n : name) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers =
    Just (MkFiber component parent retired table (Active accumulator view)) ->
  viewBindingsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps observed
    (replaceBinding @{nameEq} n
      (MkFiber component parent retired table
        (Unloading accumulator view Nothing)) fibers) =
  viewBindingsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps observed fibers
viewBindingsActiveUnload {name} {key} {world} {error} {value}
  nameEq keyEq deps observed n component parent retired table accumulator view
  fibers present =
    rewrite viewProvidersActiveUnload {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq deps observed n component parent
      retired table accumulator view fibers present in
    rewrite cong isJust (resolveCommittedValuesActiveUnload {name = name}
      {key = key} {world = world} {error = error} {value = value} nameEq keyEq
      deps observed n component parent retired table accumulator view fibers
      present) in Refl

0 fiberViewActiveUnload :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (observed : Fiber name key value world error) -> (n : name) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers =
    Just (MkFiber component parent retired table (Active accumulator view)) ->
  fiberViewInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} observed
    (replaceBinding @{nameEq} n
      (MkFiber component parent retired table
        (Unloading accumulator view Nothing)) fibers) =
  fiberViewInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} observed fibers
fiberViewActiveUnload nameEq keyEq
  (MkFiber ownComponent ownParent ownRetired ownTable (Inactive outcome)) n
  component parent retired table accumulator view fibers present = Refl
fiberViewActiveUnload {name} {key} {world} {error} {value}
  nameEq keyEq (MkFiber ownComponent ownParent ownRetired ownTable
    (Reloading rest ownAccumulator ownView)) n component parent retired table
    accumulator view fibers present = viewBindingsActiveUnload {name = name}
      {key = key} {world = world} {error = error} {value = value} nameEq keyEq
      (dependencies (componentDependencies ownComponent)) ownView n component
      parent retired table accumulator view fibers present
fiberViewActiveUnload {name} {key} {world} {error} {value}
  nameEq keyEq (MkFiber ownComponent ownParent ownRetired ownTable
    (Active ownAccumulator ownView)) n component parent retired table accumulator
    view fibers present = viewBindingsActiveUnload {name = name} {key = key}
      {world = world} {error = error} {value = value} nameEq keyEq
      (dependencies (componentDependencies ownComponent)) ownView n component
      parent retired table accumulator view fibers present
fiberViewActiveUnload {name} {key} {world} {error} {value}
  nameEq keyEq (MkFiber ownComponent ownParent ownRetired ownTable
    (Unloading ownAccumulator ownView outcome)) n component parent retired table
    accumulator view fibers present = viewBindingsActiveUnload {name = name}
      {key = key} {world = world} {error = error} {value = value} nameEq keyEq
      (dependencies (componentDependencies ownComponent)) ownView n component
      parent retired table accumulator view fibers present

0 viewsRegistryActiveUnload :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (n : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers =
    Just (MkFiber component parent retired table (Active accumulator view)) ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries
    (replaceBinding @{nameEq} n
      (MkFiber component parent retired table
        (Unloading accumulator view Nothing)) fibers) =
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries fibers
viewsRegistryActiveUnload nameEq keyEq [] n component parent retired table
  accumulator view fibers present = Refl
viewsRegistryActiveUnload {name} {key} {world} {error} {value}
  nameEq keyEq (Bind current observed :: rest) n component parent retired table
  accumulator view fibers present =
    rewrite fiberViewActiveUnload {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq keyEq observed n component parent
      retired table accumulator view fibers present in
    rewrite viewsRegistryActiveUnload {name = name} {key = key}
      {world = world} {error = error} {value = value} nameEq keyEq rest n
      component parent retired table accumulator view fibers present in Refl

public export
0 viewsInvariantActiveUnload :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers =
    Just (MkFiber component parent retired table (Active accumulator view)) ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (registryFibers {value = value} {world = world} {error = error} fibers) fibers = True ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
    (registryFibers {value = value} {world = world} {error = error} (replaceBinding @{nameEq} n
      (MkFiber component parent retired table
        (Unloading accumulator view Nothing)) fibers))
    (replaceBinding @{nameEq} n
      (MkFiber component parent retired table
        (Unloading accumulator view Nothing)) fibers) = True
viewsInvariantActiveUnload {name} {key} {world} {error} {value}
  nameEq keyEq n component parent retired table accumulator view
  fibers@(MkCoeffectContext entries unique) present valid =
  let entryPresent = lookupFiberEntries nameEq n
        (MkFiber component parent retired table (Active accumulator view)) fibers
        present
      framed = trans (viewsRegistryActiveUnload {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq entries n
        component parent retired table accumulator view fibers present) valid
      sourceSelected = viewsInvariantLookup {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq n
        (MkFiber component parent retired table (Active accumulator view)) entries
        fibers entryPresent valid
      targetSelected = trans (viewBindingsActiveUnload {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq
        (dependencies (componentDependencies component)) view n component parent
        retired table accumulator view fibers present) sourceSelected
  in viewsEntriesRuntimeTarget {name = name} {key = key} {world = world}
    {error = error} {value = value} nameEq keyEq entries n
    (MkFiber component parent retired table (Active accumulator view))
    (MkFiber component parent retired table
      (Unloading accumulator view Nothing))
    (replaceBinding @{nameEq} n
      (MkFiber component parent retired table
        (Unloading accumulator view Nothing)) fibers)
    entryPresent targetSelected framed

0 activeIsStable :
  (lifecycle : Lifecycle key value world error name deps provision) ->
  isActive lifecycle = True -> stableProvider lifecycle = True
activeIsStable (Inactive outcome) active = void (falseCannotBeTrue active)
activeIsStable (Reloading rest accumulator view) active =
  void (falseCannotBeTrue active)
activeIsStable (Active accumulator view) active = Refl
activeIsStable (Unloading accumulator view outcome) active =
  void (falseCannotBeTrue active)

0 lookupEntriesHead : (keyEq : DecEq key) -> (k : key) -> (v : value k) ->
  (rest : List (Binding key value)) ->
  lookupEntries @{keyEq} k (Bind k v :: rest) = Just v
lookupEntriesHead keyEq k v rest with (decEq @{keyEq} k k)
  lookupEntriesHead keyEq k v rest | (Yes Refl) = Refl
  lookupEntriesHead keyEq k v rest | (No contra) = void (contra Refl)

0 lookupEntriesOtherHead : (keyEq : DecEq key) ->
  (wanted, current : key) -> Not (wanted = current) ->
  (v : value current) -> (rest : List (Binding key value)) ->
  lookupEntries @{keyEq} wanted (Bind current v :: rest) =
  lookupEntries @{keyEq} wanted rest
lookupEntriesOtherHead keyEq wanted current distinct v rest
  with (decEq @{keyEq} wanted current)
  lookupEntriesOtherHead keyEq current current distinct v rest | (Yes Refl) =
    void (distinct Refl)
  lookupEntriesOtherHead keyEq wanted current distinct v rest | (No _) = Refl

record ProviderEntrySound (name, key, world, error : Type)
  (value : key -> Type) (nameEq : DecEq name) (keyEq : DecEq key)
  (k : key) (provider : name)
  (entries : List (Binding name (FiberAt name key value world error))) where
  constructor MkProviderEntrySound
  soundProviderFiber : Fiber name key value world error
  0 soundProviderLookup : lookupEntries @{nameEq} provider entries =
    Just soundProviderFiber
  0 soundProviderActive : isActive (fiberLifecycle soundProviderFiber) = True
  0 soundProviderStable : stableProvider
    (fiberLifecycle soundProviderFiber) = True
  0 soundProviderValue : isJust (lookupBinding @{keyEq} k
    (ownedValues (fiberTable soundProviderFiber))) = True

0 providerInSound :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (k : key) ->
  (provider : name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  UniqueKeys (bindingKeys entries) ->
  providerIn @{nameEq} @{keyEq} {value = value} {world = world} {error = error} k entries = Just provider ->
  ProviderEntrySound name key world error value nameEq keyEq k provider entries
providerInSound nameEq keyEq k provider [] UniqueNil found =
  case found of Refl impossible
providerInSound {name} {key} {world} {error} {value}
  nameEq keyEq k provider (Bind current fiber :: rest)
  (UniqueCons headFresh tailUnique) found
  with (isActive (fiberLifecycle fiber) &&
    memberKey @{keyEq} k (ownedValues (fiberTable fiber))) proof usable
  providerInSound {name} {key} {world} {error} {value}
    nameEq keyEq k provider (Bind current fiber :: rest)
    (UniqueCons headFresh tailUnique) found | True =
      case justValuesEqual found of
        Refl =>
          let active = andTrueLeft _ _ usable
          in MkProviderEntrySound fiber
            (lookupEntriesHead nameEq current fiber rest) active
            (activeIsStable (fiberLifecycle fiber) active)
            (andTrueRight _ _ usable)
  providerInSound {name} {key} {world} {error} {value}
    nameEq keyEq k provider (Bind current fiber :: rest)
    (UniqueCons headFresh tailUnique) found | False =
      let tailSound = providerInSound {name = name} {key = key} {world = world}
            {error = error} {value = value} nameEq keyEq k provider rest
            tailUnique found
          providerInTail = localLookupJustElem provider rest
            (soundProviderFiber tailSound) (soundProviderLookup tailSound)
          distinct : Not (provider = current)
          distinct same = headFresh
            (replace {p = \candidate => Elem candidate (bindingKeys rest)} same
              providerInTail)
          liftedLookup = trans
            (lookupEntriesOtherHead nameEq provider current distinct fiber rest)
            (soundProviderLookup tailSound)
      in MkProviderEntrySound (soundProviderFiber tailSound) liftedLookup
        (soundProviderActive tailSound) (soundProviderStable tailSound)
        (soundProviderValue tailSound)

public export
record ProviderOfSound (name, key, world, error : Type)
  (value : key -> Type) (nameEq : DecEq name) (keyEq : DecEq key)
  (k : key) (provider : name)
  (fibers : Registry name key value world error) where
  constructor MkProviderOfSound
  providerOfFiber : Fiber name key value world error
  0 providerOfLookup : lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} provider fibers =
    Just providerOfFiber
  0 providerOfActive : isActive (fiberLifecycle providerOfFiber) = True
  0 providerOfStable : stableProvider (fiberLifecycle providerOfFiber) = True
  0 providerOfValue : isJust (valueFromProvider @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
    provider k fibers) = True

public export
0 providerOfSound :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (k : key) ->
  (provider : name) -> (fibers : Registry name key value world error) ->
  providerOf @{nameEq} @{keyEq} {value = value} {world = world} {error = error} k fibers = Just provider ->
  ProviderOfSound name key world error value nameEq keyEq k provider fibers
providerOfSound {name} {key} {world} {error} {value}
  nameEq keyEq k provider fibers@(MkCoeffectContext entries unique) found =
  let entrySound = providerInSound {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq keyEq k provider entries unique
        found
      0 valuePresent : (isJust (valueFromProvider @{nameEq} @{keyEq}
        {value = value} {world = world} {error = error} provider k fibers) = True)
      valuePresent = rewrite soundProviderLookup entrySound in
        soundProviderValue entrySound
  in MkProviderOfSound (soundProviderFiber entrySound)
    (soundProviderLookup entrySound) (soundProviderActive entrySound)
    (soundProviderStable entrySound) valuePresent

public export
0 isJustTrueWitness : (candidate : Maybe a) -> isJust candidate = True ->
  (witness : a ** candidate = Just witness)
isJustTrueWitness Nothing valid = void (falseCannotBeTrue valid)
isJustTrueWitness (Just witness) valid = (witness ** Refl)

||| A view returned by target resolution has stable providers and all requested
||| values, exactly the strengthened Definition-58 committed-view clause.
public export
0 resolveViewBindingsSound :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  (fibers : Registry name key value world error) ->
  resolveView @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps fibers = Just view ->
  viewBindingsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} deps view fibers = True
resolveViewBindingsSound nameEq keyEq [] EmptyView fibers resolved = Refl
resolveViewBindingsSound {name} {key} {world} {error} {value}
  nameEq keyEq (k :: ks) view fibers resolved
  with (providerOf @{nameEq} @{keyEq} {value = value} {world = world} {error = error} k fibers) proof providerFound
  resolveViewBindingsSound {name} {key} {world} {error} {value}
    nameEq keyEq (k :: ks) view fibers resolved | Nothing =
      case resolved of Refl impossible
  resolveViewBindingsSound {name} {key} {world} {error} {value}
    nameEq keyEq (k :: ks) view fibers resolved | Just provider
    with (resolveView @{nameEq} @{keyEq} ks fibers) proof tailFound
    resolveViewBindingsSound {name} {key} {world} {error} {value}
      nameEq keyEq (k :: ks) view fibers resolved | Just provider | Nothing =
        case resolved of Refl impossible
    resolveViewBindingsSound {name} {key} {world} {error} {value}
      nameEq keyEq (k :: ks) view fibers resolved | Just provider | Just rest =
        case justValuesEqual resolved of
          Refl =>
            let providerSound = providerOfSound {name = name} {key = key}
                  {world = world} {error = error} {value = value} nameEq keyEq k
                  provider fibers providerFound
                tailSound = resolveViewBindingsSound {name = name} {key = key}
                  {world = world} {error = error} {value = value} nameEq keyEq ks
                  rest fibers tailFound
                0 providersHead : (stableProvider
                  (fiberLifecycle (providerOfFiber providerSound)) = True)
                providersHead = providerOfStable providerSound
                0 providersTail : (viewProvidersInvariant @{nameEq}
                  {key = key} {value = value} {world = world} {error = error}
                  fibers rest = True)
                providersTail = andTrueLeft _ _ tailSound
                0 valuesTail : (isJust (resolveCommittedValues @{nameEq} @{keyEq}
                  {value = value} {world = world} {error = error} ks rest fibers) =
                  True)
                valuesTail = andTrueRight _ _ tailSound
                0 valuesHead : (isJust (valueFromProvider @{nameEq} @{keyEq}
                  {value = value} {world = world} {error = error} provider k
                  fibers) = True)
                valuesHead = providerOfValue providerSound
            in case isJustTrueWitness
              (valueFromProvider @{nameEq} @{keyEq} {value = value}
                {world = world} {error = error} provider k fibers)
              valuesHead of
              (v ** valueEquation) => case isJustTrueWitness
                (resolveCommittedValues @{nameEq} @{keyEq} {value = value}
                  {world = world} {error = error} ks rest fibers)
                valuesTail of
                (tailValues ** tailEquation) =>
                  let 0 allProviders : (viewProvidersInvariant @{nameEq}
                        {key = key} {value = value} {world = world}
                        {error = error} fibers (ProviderView provider rest) = True)
                      allProviders = rewrite providerOfLookup providerSound in
                        andBothTrue _ _ providersHead providersTail
                      0 allValues : (isJust (resolveCommittedValues @{nameEq}
                        @{keyEq} {value = value} {world = world} {error = error}
                        (k :: ks) (ProviderView provider rest) fibers) = True)
                      allValues = rewrite valueEquation in
                        rewrite tailEquation in Refl
                  in andBothTrue _ _ allProviders allValues

public export
0 targetFiberBindingsSound :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  targetFiber @{nameEq} @{keyEq} {value = value} {world = world} {error = error} fiber fibers = Just view ->
  viewBindingsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
    (dependencies (componentDependencies (fiberComponent fiber))) view fibers =
    True
targetFiberBindingsSound {name} {key} {world} {error} {value}
  nameEq keyEq fiber fibers view target with (retired fiber)
  targetFiberBindingsSound {name} {key} {world} {error} {value}
    nameEq keyEq fiber fibers view target | True = case target of Refl impossible
  targetFiberBindingsSound {name} {key} {world} {error} {value}
    nameEq keyEq fiber fibers view target | False =
      resolveViewBindingsSound {name = name} {key = key} {world = world}
        {error = error} {value = value} nameEq keyEq
        (dependencies (componentDependencies (fiberComponent fiber))) view fibers
        target

||| Runtime-checked rule application used by the proof-indexed LTS. `applyAction`
||| remains the raw ten-rule evaluator; this wrapper rejects a malformed target
||| rather than admitting it into a proof trace.
public export
checkedApplyAction : DecEq name => DecEq key =>
  Action name key value world error ->
  SystemState name key value world error ->
  Maybe (RuleTag, SystemState name key value world error)
checkedApplyAction action before = case applyAction action before of
  Nothing => Nothing
  Just (tag, afterState) =>
    if registryWellFormed afterState then Just (tag, afterState) else Nothing

||| An indexed transition exists only when the executable checked evaluator
||| produced its exact endpoint.
public export
data Transition : SystemState name key value world error ->
                  SystemState name key value world error -> Type where
  Fired : (nameEq : DecEq name) -> (keyEq : DecEq key) ->
          (action : Action name key value world error) -> (tag : RuleTag) ->
          checkedApplyAction @{nameEq} @{keyEq} action before =
            Just (tag, afterState) ->
          Transition before afterState

public export
record TransitionResult (before : SystemState name key value world error) where
  constructor MkTransitionResult
  transitionAfter : SystemState name key value world error
  transitionRule : RuleTag
  checkedTransition : Transition before transitionAfter

||| Execute and package a proof-indexed transition when the checked evaluator
||| accepts the rule.
public export
fire : (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  Action name key value world error ->
  (before : SystemState name key value world error) ->
  Maybe (TransitionResult before)
fire nameEq keyEq action before
  with (checkedApplyAction @{nameEq} @{keyEq} action before) proof fired
  fire nameEq keyEq action before | Nothing = Nothing
  fire nameEq keyEq action before | Just (tag, afterState) =
    Just (MkTransitionResult afterState tag
      (Fired nameEq keyEq action tag fired))

public export
data Transitions : SystemState name key value world error ->
                   SystemState name key value world error -> Type where
  NoTransitions : Transitions state state
  MoreTransitions : Transition first middle -> Transitions middle finalState ->
                    Transitions first finalState

public export
transitionAction : {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> Action name key value world error
transitionAction (Fired _ _ action _ _) = action

public export
transitionTag : {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> RuleTag
transitionTag (Fired _ _ _ tag _) = tag

public export
transitionActor : {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> name
transitionActor transition = case transitionAction transition of
  OInsert n _ _ => n
  ORetire n => n
  ORemove n => n
  LBegin n => n
  LAdvance n => n
  LDivert n => n
  LLeave n => n
  LUnload n => n

public export
appendTransitions : Transitions first middle -> Transitions middle finalState ->
  Transitions first finalState
appendTransitions NoTransitions suffix = suffix
appendTransitions (MoreTransitions step rest) suffix =
  MoreTransitions step (appendTransitions rest suffix)

public export
installedAt : DecEq name => name ->
  SystemState name key value world error -> Bool
installedAt n state = case lookupFiber n (registry state) of
  Nothing => False
  Just fiber => installed (fiberLifecycle fiber)

||| Executable grouping of maximal installed intervals in a snapshot log.
public export
episodes : DecEq name => name ->
  List (SystemState name key value world error) ->
  List (List (SystemState name key value world error))
episodes n states = go states []
  where
  go : List (SystemState name key value world error) ->
       List (SystemState name key value world error) ->
       List (List (SystemState name key value world error))
  go [] [] = []
  go [] current = [reverse current]
  go (state :: rest) current =
    if installedAt n state
      then go rest (state :: current)
      else case current of
        [] => go rest []
        _ => reverse current :: go rest []

public export
0 retireFiberExact :
  (component : Component key value world error) ->
  (parent : Parent name) -> (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  retireFiber (MkFiber component parent retired table lifecycle) =
    MkFiber component parent True table lifecycle
retireFiberExact component parent retired table lifecycle = Refl

0 calculusJustInjective : Just left = Just right -> left = right
calculusJustInjective Refl = Refl

public export
0 reliedOnByLookupTrue :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (provider, consumer : name) ->
  (fiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} consumer fibers = Just fiber ->
  reliedHead @{nameEq} {key = key} {value = value} {world = world}
    {error = error} provider provider
    (the (Binding name (\_ => Fiber name key value world error))
      (Bind consumer fiber)) = True ->
  relied @{nameEq} {key = key} {value = value} {world = world}
    {error = error} provider fibers = True
reliedOnByLookupTrue {name} {key} {world} {error} {value}
  nameEq provider consumer fiber fibers@(MkCoeffectContext entries unique)
  found headTrue = go entries
    (lookupFiberEntries nameEq consumer fiber fibers found)
  where
    go : (remaining : List
      (Binding name (\_ => Fiber name key value world error))) ->
      lookupEntries @{nameEq} consumer remaining = Just fiber ->
      reliedOnBy @{nameEq} {key = key} {value = value} {world = world}
        {error = error} provider provider remaining = True
    go [] present = case present of Refl impossible
    go (Bind current observed :: rest) present
      with (decEq @{nameEq} consumer current)
      go (Bind current observed :: rest) present | Yes equal = case equal of
        Refl => case calculusJustInjective present of
          Refl => rewrite headTrue in Refl
      go (Bind current observed :: rest) present | No distinct
      with (reliedHead @{nameEq} {key = key} {value = value} {world = world}
        {error = error} provider provider (Bind current observed))
        go (Bind current observed :: rest) present | No distinct | False =
          go rest present
        go (Bind current observed :: rest) present | No distinct | True = Refl

