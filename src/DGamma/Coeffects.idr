module DGamma.Coeffects

import DGamma.Core
import DGamma.Effects
import Decidable.Equality
import Data.Maybe
import Data.List.Elem

%default total

||| A dependently typed key/value binding.
public export
data Binding : (key : Type) -> (value : key -> Type) -> Type where
  Bind : (k : key) -> value k -> Binding key value

public export
bindingKey : Binding key value -> key
bindingKey (Bind k _) = k

public export
bindingKeys : List (Binding key value) -> List key
bindingKeys = map bindingKey

||| Intrinsic uniqueness witness for a finite domain.
public export
data UniqueKeys : List key -> Type where
  UniqueNil : UniqueKeys []
  UniqueCons : Not (Elem k rest) -> UniqueKeys rest -> UniqueKeys (k :: rest)

||| Definition 22: a finite dependent partial function. Duplicate-key states
||| are excluded by the erased UniqueKeys field rather than by convention.
public export
record CoeffectContext (key : Type) (value : key -> Type) where
  constructor MkCoeffectContext
  bindings : List (Binding key value)
  0 uniqueBindings : UniqueKeys (bindingKeys bindings)

public export
emptyContext : CoeffectContext key value
emptyContext = MkCoeffectContext [] UniqueNil

public export
lookupEntries : DecEq key => (wanted : key) ->
  (entries : List (Binding key value)) -> Maybe (value wanted)
lookupEntries wanted [] = Nothing
lookupEntries wanted (Bind found val :: rest) with (decEq wanted found)
  lookupEntries wanted (Bind wanted val :: rest) | (Yes Refl) = Just val
  lookupEntries wanted (Bind found val :: rest) | (No _) =
    lookupEntries wanted rest

public export
lookupBinding : DecEq key => (wanted : key) ->
  CoeffectContext key value -> Maybe (value wanted)
lookupBinding wanted (MkCoeffectContext entries _) = lookupEntries wanted entries

public export
memberKey : DecEq key => key -> CoeffectContext key value -> Bool
memberKey wanted table = isJust (lookupBinding wanted table)

public export
0 lookupNothingNotElem : DecEq key => (wanted : key) ->
  (entries : List (Binding key value)) ->
  lookupEntries wanted entries = Nothing -> Not (Elem wanted (bindingKeys entries))
lookupNothingNotElem wanted [] absent elem impossible
lookupNothingNotElem wanted (Bind found val :: rest) absent elem
  with (decEq wanted found)
    lookupNothingNotElem found (Bind found val :: rest) absent elem | (Yes Refl) =
      case absent of Refl impossible
    lookupNothingNotElem found (Bind found val :: rest) absent Here | (No different) =
      void (different Refl)
    lookupNothingNotElem wanted (Bind found val :: rest) absent (There later) | (No _) =
      lookupNothingNotElem wanted rest absent later

public export
insertBinding : DecEq key => (k : key) -> value k ->
  (table : CoeffectContext key value) ->
  (0 absent : lookupBinding k table = Nothing) -> CoeffectContext key value
insertBinding k val (MkCoeffectContext entries unique) absent =
  MkCoeffectContext (Bind k val :: entries)
    (UniqueCons (lookupNothingNotElem k entries absent) unique)

public export
deleteEntries : DecEq key => key -> List (Binding key value) ->
  List (Binding key value)
deleteEntries wanted [] = []
deleteEntries wanted (Bind found val :: rest) with (decEq wanted found)
  deleteEntries wanted (Bind wanted val :: rest) | (Yes Refl) = rest
  deleteEntries wanted (Bind found val :: rest) | (No _) =
    Bind found val :: deleteEntries wanted rest

public export
0 elemDeleteLift : DecEq key => (wanted, present : key) ->
  (entries : List (Binding key value)) ->
  Elem present (bindingKeys (deleteEntries wanted entries)) ->
  Elem present (bindingKeys entries)
elemDeleteLift wanted present [] elem impossible
elemDeleteLift wanted present (Bind found val :: rest) elem
  with (decEq wanted found)
    elemDeleteLift found present (Bind found val :: rest) elem | (Yes Refl) = There elem
    elemDeleteLift wanted found (Bind found val :: rest) Here | (No _) = Here
    elemDeleteLift wanted present (Bind found val :: rest) (There later) | (No _) =
      There (elemDeleteLift wanted present rest later)

public export
0 deletePreservesUnique : DecEq key => (wanted : key) ->
  (entries : List (Binding key value)) -> UniqueKeys (bindingKeys entries) ->
  UniqueKeys (bindingKeys (deleteEntries wanted entries))
deletePreservesUnique wanted [] UniqueNil = UniqueNil
deletePreservesUnique wanted (Bind found val :: rest)
  (UniqueCons absent uniqueRest) with (decEq wanted found)
    deletePreservesUnique found (Bind found val :: rest)
      (UniqueCons absent uniqueRest) | (Yes Refl) = uniqueRest
    deletePreservesUnique wanted (Bind found val :: rest)
      (UniqueCons absent uniqueRest) | (No _) =
        UniqueCons (\present => absent (elemDeleteLift wanted found rest present))
                   (deletePreservesUnique wanted rest uniqueRest)

public export
deleteBinding : DecEq key => key -> CoeffectContext key value ->
  CoeffectContext key value
deleteBinding wanted (MkCoeffectContext entries unique) =
  MkCoeffectContext (deleteEntries wanted entries)
    (deletePreservesUnique wanted entries unique)

||| A coeffect-table undo token compares the runtime finite map; the erased
||| uniqueness witness is representation proof, not part of the recovered state.
public export
record CoeffectUndo {key : Type} {value : key -> Type}
                    (after, before : CoeffectContext key value) where
  constructor MkCoeffectUndo
  runCoeffectUndo : CoeffectContext key value -> Maybe (CoeffectContext key value)
  0 coeffectUndoValid :
    (restored : CoeffectContext key value **
      (runCoeffectUndo after = Just restored,
       bindings restored = bindings before))

public export
record CoeffectApplied {key : Type} {value : key -> Type}
                       (before : CoeffectContext key value) where
  constructor MkCoeffectApplied
  coeffectAfter : CoeffectContext key value
  coeffectUndo : CoeffectUndo coeffectAfter before

public export
0 deleteEntriesInserted : DecEq key => (k : key) -> (val : value k) ->
  (entries : List (Binding key value)) ->
  deleteEntries k (Bind k val :: entries) = entries
deleteEntriesInserted k val entries with (decEq k k)
  deleteEntriesInserted k val entries | (Yes Refl) = Refl
  deleteEntriesInserted k val entries | (No contra) = void (contra Refl)

public export
0 deleteInserted : DecEq key => (k : key) -> (val : value k) ->
  (table : CoeffectContext key value) ->
  (0 absent : lookupBinding k table = Nothing) ->
  bindings (deleteBinding k (insertBinding k val table absent)) = bindings table
deleteInserted k val (MkCoeffectContext entries unique) absent =
  deleteEntriesInserted k val entries

public export
setInverse : DecEq key => (k : key) ->
  CoeffectContext key value -> Maybe (CoeffectContext key value)
setInverse k later = case lookupBinding k later of
  Nothing => Nothing
  Just _ => Just (deleteBinding k later)

public export
0 lookupInserted : DecEq key => (k : key) -> (val : value k) ->
  (table : CoeffectContext key value) ->
  (absent : lookupBinding k table = Nothing) ->
  lookupBinding k (insertBinding k val table absent) = Just val
lookupInserted k val (MkCoeffectContext entries unique) absent with (decEq k k)
  lookupInserted k val (MkCoeffectContext entries unique) absent | (Yes Refl) = Refl
  lookupInserted k val (MkCoeffectContext entries unique) absent | (No contra) =
    void (contra Refl)

public export
0 setInverseRuns : DecEq key => (k : key) -> (val : value k) ->
  (before : CoeffectContext key value) ->
  (absent : lookupBinding k before = Nothing) ->
  setInverse k (insertBinding k val before absent) =
  Just (deleteBinding k (insertBinding k val before absent))
setInverseRuns k val before absent =
  rewrite lookupInserted k val before absent in Refl

||| Definition 23: get, with absence represented honestly by Maybe.
public export
get : DecEq key => (k : key) -> CoeffectContext key value -> Maybe (value k)
get = lookupBinding

||| Definition 23: safe partial set. On success it returns a state-indexed undo
||| token whose executable inverse removes exactly this key.
public export
setFresh : DecEq key => (k : key) -> value k ->
  (before : CoeffectContext key value) -> Maybe (CoeffectApplied before)
setFresh k val before with (lookupBinding k before) proof found
  setFresh k val before | Just _ = Nothing
  setFresh k val before | Nothing =
    Just (MkCoeffectApplied (insertBinding k val before found)
      (MkCoeffectUndo (setInverse k)
        (deleteBinding k (insertBinding k val before found) **
          (setInverseRuns k val before found,
           deleteInserted k val before found))))

public export
replaceEntries : DecEq key => (k : key) -> value k ->
  List (Binding key value) -> List (Binding key value)
replaceEntries k val [] = []
replaceEntries k val (Bind found old :: rest) with (decEq k found)
  replaceEntries k val (Bind k old :: rest) | (Yes Refl) = Bind k val :: rest
  replaceEntries k val (Bind found old :: rest) | (No _) =
    Bind found old :: replaceEntries k val rest

public export
0 replacePreservesKeys : {key : Type} -> {value : key -> Type} ->
  DecEq key => (k : key) -> (val : value k) ->
  (entries : List (Binding key value)) ->
  bindingKeys (replaceEntries k val entries) = bindingKeys entries
replacePreservesKeys k val [] = Refl
replacePreservesKeys k val (Bind found old :: rest) with (decEq k found)
  replacePreservesKeys found val (Bind found old :: rest) | (Yes Refl) = Refl
  replacePreservesKeys k val (Bind found old :: rest) | (No _) =
    cong (found ::) (replacePreservesKeys k val rest)

||| Replace a present binding while preserving every other key/domain proof.
public export
replaceBinding : DecEq key => (k : key) -> value k ->
  CoeffectContext key value -> CoeffectContext key value
replaceBinding k val (MkCoeffectContext entries unique) =
  MkCoeffectContext (replaceEntries k val entries)
    (replace {p = UniqueKeys}
      (sym (replacePreservesKeys k val entries)) unique)

public export
PartialMap : Type -> Type
PartialMap value = value -> Maybe value

public export
data PartialRelated : (value : Type) -> (value -> value -> Type) ->
  Maybe value -> Maybe value -> Type where
  PartialUndefined : PartialRelated value rel Nothing Nothing
  PartialDefined : rel left right ->
    PartialRelated value rel (Just left) (Just right)

public export
PartialMapsRelated : {value : Type} -> Equivalence value ->
  PartialMap value -> PartialMap value -> Type
PartialMapsRelated {value} eq left right = {x, y : value} -> relation eq x y ->
  PartialRelated value (relation eq) (left x) (right y)

public export
data OperationResultsRelated : (eq : Equivalence value) ->
  Maybe (value, PartialMap value, outcome) ->
  Maybe (value, PartialMap value, outcome) -> Type where
  ResultsUndefined : OperationResultsRelated eq Nothing Nothing
  ResultsDefined : relation eq nextLeft nextRight ->
    resultLeft = resultRight ->
    PartialMapsRelated eq undoLeft undoRight ->
    OperationResultsRelated eq
      (Just (nextLeft, undoLeft, resultLeft))
      (Just (nextRight, undoRight, resultRight))

||| Definition 24: a partial, witnessed operation that respects the key's
||| observational equivalence, including definedness, successors, inverses and
||| outcomes.
public export
record CoeffectOperation (value, argument, outcome : Type) where
  constructor MkCoeffectOperation
  valueEquivalence : Equivalence value
  runOperation : argument -> value ->
    Maybe (value, PartialMap value, outcome)
  0 operationWitness : (arg : argument) -> (before, after : value) ->
    (undo : PartialMap value) -> (result : outcome) ->
    runOperation arg before = Just (after, undo, result) ->
    undo after = Just before
  0 operationRespects : (arg : argument) -> {left, right : value} ->
    relation valueEquivalence left right ->
    OperationResultsRelated valueEquivalence
      (runOperation arg left) (runOperation arg right)

||| Definition 24's complete coeffect triple (V, ~=, A), with heterogeneous
||| argument and outcome types indexed by operation code.
public export
record CoeffectInterface (value : Type) where
  constructor MkCoeffectInterface
  coeffectEquivalence : Equivalence value
  OperationCode : Type
  OperationArgument : OperationCode -> Type
  OperationOutcome : OperationCode -> Type
  coeffectOperation : (code : OperationCode) ->
    CoeffectOperation value (OperationArgument code) (OperationOutcome code)
  0 operationUsesInterfaceEquivalence : (code : OperationCode) ->
    valueEquivalence (coeffectOperation code) = coeffectEquivalence

public export
0 lookupReplaceEntries : DecEq key => (k : key) ->
  (old, next : value k) -> (entries : List (Binding key value)) ->
  lookupEntries k entries = Just old ->
  lookupEntries k (replaceEntries k next entries) = Just next
lookupReplaceEntries k old next [] present impossible
lookupReplaceEntries k old next (Bind found val :: rest) present
  with (decEq k found) proof decided
    lookupReplaceEntries found old next (Bind found val :: rest) present |
      (Yes Refl) = rewrite decided in Refl
    lookupReplaceEntries k old next (Bind found val :: rest) present | (No _) =
      rewrite decided in lookupReplaceEntries k old next rest present

public export
0 replaceRestoreEntries : DecEq key => (k : key) ->
  (old, next : value k) -> (entries : List (Binding key value)) ->
  lookupEntries k entries = Just old ->
  replaceEntries k old (replaceEntries k next entries) = entries
replaceRestoreEntries k old next [] present impossible
replaceRestoreEntries k old next (Bind found val :: rest) present
  with (decEq k found) proof decided
    replaceRestoreEntries found old next (Bind found val :: rest) present |
      (Yes Refl) = rewrite decided in case present of Refl => Refl
    replaceRestoreEntries k old next (Bind found val :: rest) present | (No _) =
      rewrite decided in
        cong (Bind found val ::) (replaceRestoreEntries k old next rest present)

public export
liftedInverse : DecEq key => (k : key) -> PartialMap (value k) ->
  CoeffectContext key value -> Maybe (CoeffectContext key value)
liftedInverse k undo later =
  case lookupBinding k later of
    Nothing => Nothing
    Just now => case undo now of
      Nothing => Nothing
      Just prior => Just (replaceBinding k prior later)

||| State-indexed partial undo returned by a lifted operation. The executable
||| partial function and its application-state recovery certificate travel
||| together into the runtime path.
public export
record LiftedUndo {key : Type} {value : key -> Type}
                  (after, before : CoeffectContext key value) where
  constructor MkLiftedUndo
  runLiftedUndo : CoeffectContext key value -> Maybe (CoeffectContext key value)
  0 liftedUndoValid :
    (restored : CoeffectContext key value **
      (runLiftedUndo after = Just restored,
       bindings restored = bindings before))

public export
record LiftedOperationResult {key : Type} {value : key -> Type}
                             (before : CoeffectContext key value)
                             (outcome : Type) where
  constructor MkLiftedOperationResult
  liftedAfter : CoeffectContext key value
  liftedUndoToken : LiftedUndo liftedAfter before
  liftedOutcome : outcome

public export
liftedUndo : {key : Type} -> {value : key -> Type} ->
  {before : CoeffectContext key value} -> {outcome : Type} ->
  LiftedOperationResult {key} {value} before outcome ->
  CoeffectContext key value -> Maybe (CoeffectContext key value)
liftedUndo result = runLiftedUndo (liftedUndoToken result)

public export
makeLiftedUndo : DecEq key => (k : key) ->
  (op : CoeffectOperation (value k) argument outcome) ->
  (arg : argument) -> (table : CoeffectContext key value) ->
  (old, next : value k) -> (inverseMap : PartialMap (value k)) ->
  (result : outcome) ->
  (found : lookupBinding k table = Just old) ->
  (ran : runOperation op arg old = Just (next, inverseMap, result)) ->
  LiftedUndo (replaceBinding k next table) table
makeLiftedUndo k op arg (MkCoeffectContext entries unique)
  old next inverseMap result found ran =
    MkLiftedUndo (liftedInverse k inverseMap)
      (replaceBinding k old
        (replaceBinding k next (MkCoeffectContext entries unique)) **
       (inverseRuns, replaceRestoreEntries k old next entries found))
  where
  0 inverseRuns :
    liftedInverse k inverseMap
      (replaceBinding k next (MkCoeffectContext entries unique)) =
    Just (replaceBinding k old
      (replaceBinding k next (MkCoeffectContext entries unique)))
  inverseRuns =
    rewrite lookupReplaceEntries k old next entries found in
    rewrite operationWitness op arg old next inverseMap result ran in Refl

||| Definition 24, Equation 23: executable witnessed lift of a value operation
||| to the dependent table at one key. The lifted inverse remains partial.
public export
liftOperation : DecEq key => (k : key) ->
  CoeffectOperation (value k) argument outcome -> argument ->
  (table : CoeffectContext key value) ->
  Maybe (LiftedOperationResult table outcome)
liftOperation k op arg table with (lookupBinding k table) proof found
  liftOperation k op arg table | Nothing = Nothing
  liftOperation k op arg table | Just old with (runOperation op arg old) proof ran
    liftOperation k op arg table | Just old | Nothing = Nothing
    liftOperation k op arg table | Just old | Just (next, undo, result) =
      Just (MkLiftedOperationResult
        (replaceBinding k next table)
        (makeLiftedUndo k op arg table old next undo result found ran)
        result)

||| Definition 25: a finite set of dependencies with intrinsic uniqueness.
public export
record CoeffectSpec (key : Type) where
  constructor MkCoeffectSpec
  dependencies : List key
  0 uniqueDependencies : UniqueKeys dependencies

public export
emptySpec : CoeffectSpec key
emptySpec = MkCoeffectSpec [] UniqueNil

public export
extendSpec : (k : key) -> (spec : CoeffectSpec key) ->
  (0 fresh : Not (Elem k (dependencies spec))) -> CoeffectSpec key
extendSpec k (MkCoeffectSpec keys unique) fresh =
  MkCoeffectSpec (k :: keys) (UniqueCons fresh unique)

public export
satisfiesKeys : DecEq key => CoeffectContext key value -> List key -> Bool
satisfiesKeys table [] = True
satisfiesKeys table (k :: ks) = memberKey k table && satisfiesKeys table ks

||| Definition 25 / Equation 24: all declared keys are present.
public export
satisfies : DecEq key => CoeffectContext key value -> CoeffectSpec key -> Bool
satisfies table spec = satisfiesKeys table (dependencies spec)

||| Definition 26: notification classification.
public export
data Notification = Activating | Deactivating | Neutral

public export
Eq Notification where
  Activating == Activating = True
  Deactivating == Deactivating = True
  Neutral == Neutral = True
  _ == _ = False

public export
notify : DecEq key => CoeffectSpec key ->
  CoeffectContext key value -> CoeffectContext key value -> Notification
notify spec before after =
  case (satisfies before spec, satisfies after spec) of
    (False, True) => Activating
    (True, False) => Deactivating
    _ => Neutral

||| The local spatial-composability fact: satisfaction cannot be false when an
||| activation notification is produced.
public export
0 activatingMeansSatisfiedAfter : DecEq key =>
  (spec : CoeffectSpec key) -> (before, after : CoeffectContext key value) ->
  notify spec before after = Activating -> satisfies after spec = True
activatingMeansSatisfiedAfter spec before after prf with (satisfies before spec)
  activatingMeansSatisfiedAfter spec before after prf | False with (satisfies after spec)
    activatingMeansSatisfiedAfter spec before after Refl | False | True = Refl
    activatingMeansSatisfiedAfter spec before after prf | False | False impossible
  activatingMeansSatisfiedAfter spec before after prf | True with (satisfies after spec)
    activatingMeansSatisfiedAfter spec before after prf | True | True impossible
    activatingMeansSatisfiedAfter spec before after prf | True | False impossible

public export
0 deactivatingMeansUnsatisfiedAfter : DecEq key =>
  (spec : CoeffectSpec key) -> (before, after : CoeffectContext key value) ->
  notify spec before after = Deactivating -> satisfies after spec = False
deactivatingMeansUnsatisfiedAfter spec before after prf with (satisfies before spec)
  deactivatingMeansUnsatisfiedAfter spec before after prf | True with (satisfies after spec)
    deactivatingMeansUnsatisfiedAfter spec before after prf | True | False = Refl
    deactivatingMeansUnsatisfiedAfter spec before after prf | True | True impossible
  deactivatingMeansUnsatisfiedAfter spec before after prf | False with (satisfies after spec)
    deactivatingMeansUnsatisfiedAfter spec before after prf | False | True impossible
    deactivatingMeansUnsatisfiedAfter spec before after prf | False | False impossible

||| Definition 27: an operational realization records whether recovery executes
||| a partial inverse against mutated state or discards a derived child and
||| returns the untouched parent. The two constructors have observably distinct
||| recovery algorithms.
public export
data Realisation : Type -> Type where
  InPlaceRealisation : (before, after : state) ->
    (undo : PartialMap state) -> (0 valid : undo after = Just before) ->
    Realisation state
  DerivedRealisation : (parent, child : state) -> Realisation state

public export
recoverRealisation : Realisation state -> Maybe state
recoverRealisation (InPlaceRealisation before after undo valid) = undo after
recoverRealisation (DerivedRealisation parent child) = Just parent

public export
0 inPlaceRecovery :
  (realised : Realisation state) ->
  case realised of
    InPlaceRealisation before after undo valid =>
      recoverRealisation realised = Just before
    DerivedRealisation parent child => Unit
inPlaceRecovery (InPlaceRealisation before after undo valid) = valid
inPlaceRecovery (DerivedRealisation parent child) = ()

public export
0 derivedRecoveryDiscardsChild : (parent, child : state) ->
  recoverRealisation (DerivedRealisation parent child) = Just parent
derivedRecoveryDiscardsChild parent child = Refl

||| A homogeneous finite partial function with the same intrinsic uniqueness
||| as the dependent table.
public export
Assoc : Type -> Type -> Type
Assoc key item = CoeffectContext key (\_ => item)

public export
emptyAssoc : Assoc key item
emptyAssoc = emptyContext

public export
lookupAssoc : DecEq key => key -> Assoc key item -> Maybe item
lookupAssoc = lookupBinding

public export
putAssoc : DecEq key => (wanted : key) -> item -> Assoc key item -> Assoc key item
putAssoc wanted val table with (lookupAssoc wanted table) proof found
  putAssoc wanted val table | Just old = replaceBinding wanted val table
  putAssoc wanted val table | Nothing = insertBinding wanted val table found

||| Evidence for the paper's inclusion K into R. Injectivity prevents unrelated
||| keys from collapsing in the default realm.
public export
record RealmEmbedding (key, realm : Type) where
  constructor MkRealmEmbedding
  embedKey : key -> realm
  0 embedInjective : {left, right : key} ->
    embedKey left = embedKey right -> left = right

||| Definition 28: isolated coeffect context.
public export
record IsoContext (key, realm : Type) (value : realm -> Type) where
  constructor MkIsoContext
  defaultRealms : RealmEmbedding key realm
  realmOverrides : Assoc key realm
  realmBindings : CoeffectContext realm value

public export
resolveRealm : DecEq key => (k : key) -> IsoContext key realm value -> realm
resolveRealm k ctx = fromMaybe (embedKey (defaultRealms ctx) k)
                               (lookupAssoc k (realmOverrides ctx))

||| Definition 29: isolated get.
public export
isoGet : (DecEq key, DecEq realm) => (k : key) ->
  (ctx : IsoContext key realm value) -> Maybe (value (resolveRealm k ctx))
isoGet k ctx = lookupBinding (resolveRealm k ctx) (realmBindings ctx)

public export
record IsoSetResult {key, realm : Type} {value : realm -> Type}
                    (keyEq : DecEq key)
                    (before : IsoContext key realm value) where
  constructor MkIsoSetResult
  isoAfter : IsoContext key realm value
  isolatedKey : key
  installedRealm : realm
  0 realmMatchesAfter : resolveRealm @{keyEq} isolatedKey isoAfter = installedRealm
  isoTableUndo : CoeffectUndo (realmBindings isoAfter) (realmBindings before)

public export
runIsoUndo : {key, realm : Type} -> {value : realm -> Type} ->
  {keyEq : DecEq key} -> {before : IsoContext key realm value} ->
  DecEq realm => (result : IsoSetResult keyEq before) ->
  IsoContext key realm value -> Maybe (IsoContext key realm value)
runIsoUndo {keyEq} result later with (decEq (resolveRealm @{keyEq} (isolatedKey result) later)
                                    (installedRealm result))
  runIsoUndo result later | (No _) = Nothing
  runIsoUndo result later | (Yes sameRealm) =
    case runCoeffectUndo (isoTableUndo result) (realmBindings later) of
      Nothing => Nothing
      Just restored => Just (MkIsoContext (defaultRealms later)
        (realmOverrides later) restored)

public export
0 isoUndoValid : {keyEq : DecEq key} -> DecEq realm =>
  (result : IsoSetResult keyEq before) ->
  (restored : IsoContext key realm value **
    (runIsoUndo result (isoAfter result) = Just restored,
     bindings (realmBindings restored) = bindings (realmBindings before)))
isoUndoValid {keyEq} result with (decEq (resolveRealm @{keyEq} (isolatedKey result) (isoAfter result))
                               (installedRealm result)) proof decided
  isoUndoValid result | (No different) =
    void (different (realmMatchesAfter result))
  isoUndoValid result | (Yes sameRealm) with (coeffectUndoValid (isoTableUndo result))
    isoUndoValid result | (Yes sameRealm) |
      (restoredTable ** (undoRuns, restores)) =
        (MkIsoContext (defaultRealms (isoAfter result))
          (realmOverrides (isoAfter result)) restoredTable **
          (rewrite undoRuns in Refl, restores))

||| Definition 29: isolated set is indexed by its input context and retains the
||| witnessed base-table undo. The inverse is partial if realm resolution has
||| changed; `isoSet` never returns an unchecked total deletion.
public export
isoSet : (keyEq : DecEq key) -> DecEq realm => (k : key) ->
  (ctx : IsoContext key realm value) -> value (resolveRealm @{keyEq} k ctx) ->
  Maybe (IsoSetResult keyEq ctx)
isoSet keyEq k ctx val =
  case setFresh (resolveRealm @{keyEq} k ctx) val (realmBindings ctx) of
    Nothing => Nothing
    Just applied =>
      Just (MkIsoSetResult
        (MkIsoContext (defaultRealms ctx) (realmOverrides ctx)
          (coeffectAfter applied))
        k (resolveRealm @{keyEq} k ctx) Refl (coeffectUndo applied))

||| Definition 29: isolation is a derived realization; the old context is left
||| intact and a new one carries the override.
public export
isolate : DecEq key => key -> realm -> IsoContext key realm value ->
  IsoContext key realm value
isolate k realm ctx =
  MkIsoContext (defaultRealms ctx)
               (putAssoc k realm (realmOverrides ctx))
               (realmBindings ctx)

public export
isolateRealisation : DecEq key => key -> realm ->
  (ctx : IsoContext key realm value) -> Realisation (IsoContext key realm value)
isolateRealisation k realm ctx = DerivedRealisation ctx (isolate k realm ctx)

||| A family of metadata monoids, Definition 30.
public export
record MetadataMonoid {key : Type} (metadata : key -> Type) where
  constructor MkMetadataMonoid
  emptyMetadata : (k : key) -> metadata k
  mergeMetadata : (k : key) -> metadata k -> metadata k -> metadata k
  0 mergeLeftIdentity : (k : key) -> (x : metadata k) ->
    mergeMetadata k (emptyMetadata k) x = x
  0 mergeRightIdentity : (k : key) -> (x : metadata k) ->
    mergeMetadata k x (emptyMetadata k) = x
  0 mergeAssociative : (k : key) -> (x, y, z : metadata k) ->
    mergeMetadata k (mergeMetadata k x y) z =
    mergeMetadata k x (mergeMetadata k y z)

||| Update one slot of a dependent function.
public export
replaceDependent : DecEq key => (family : key -> Type) ->
  (target : key) -> family target -> ((k : key) -> family k) ->
  (k : key) -> family k
replaceDependent family target val old query with (decEq target query)
  replaceDependent family target val old target | (Yes Refl) = val
  replaceDependent family target val old query | (No _) = old query

||| Definition 30: intercepted coeffect context and interception specification.
public export
InterSpec : (key : Type) -> (metadata : key -> Type) -> Type
InterSpec key metadata = CoeffectContext key metadata

public export
record InterContext (key : Type) (metadata, value : key -> Type) where
  constructor MkInterContext
  ambientMetadata : (k : key) -> metadata k
  providerTable : CoeffectContext key (\k => metadata k -> value k)

||| Definition 31: provider access with component metadata taking the left and
||| ambient/context metadata taking the right (right-biased by the monoid's
||| interpretation).
public export
interGet : DecEq key => (k : key) -> MetadataMonoid metadata -> metadata k ->
  InterContext key metadata value -> Maybe (value k)
interGet k monoid declared ctx =
  case lookupBinding k (providerTable ctx) of
    Nothing => Nothing
    Just provider =>
      Just (provider (mergeMetadata monoid k declared (ambientMetadata ctx k)))

public export
record InterSetResult {key : Type} {metadata, value : key -> Type}
                      (before : InterContext key metadata value) where
  constructor MkInterSetResult
  interAfter : InterContext key metadata value
  interTableUndo : CoeffectUndo (providerTable interAfter) (providerTable before)

public export
runInterUndo : {key : Type} -> {metadata, value : key -> Type} ->
  {before : InterContext key metadata value} ->
  (result : InterSetResult before) ->
  InterContext key metadata value -> Maybe (InterContext key metadata value)
runInterUndo result later =
  case runCoeffectUndo (interTableUndo result) (providerTable later) of
    Nothing => Nothing
    Just restored => Just (MkInterContext (ambientMetadata later) restored)

public export
0 interUndoValid : (result : InterSetResult before) ->
  (restored : InterContext key metadata value **
    (runInterUndo result (interAfter result) = Just restored,
     bindings (providerTable restored) = bindings (providerTable before)))
interUndoValid result with (coeffectUndoValid (interTableUndo result))
  interUndoValid result | (restoredTable ** (undoRuns, restores)) =
    (MkInterContext (ambientMetadata (interAfter result)) restoredTable **
      (rewrite undoRuns in Refl, restores))

||| Definition 31: intercepted provider set retains an indexed witnessed partial
||| table undo rather than exporting an unchecked total function.
public export
interSet : DecEq key => (k : key) -> (metadata k -> value k) ->
  (ctx : InterContext key metadata value) -> Maybe (InterSetResult ctx)
interSet k provider ctx =
  case setFresh k provider (providerTable ctx) of
    Nothing => Nothing
    Just applied =>
      Just (MkInterSetResult
        (MkInterContext (ambientMetadata ctx) (coeffectAfter applied))
        (coeffectUndo applied))

||| Definition 31: interception is a derived realization.
public export
intercept : {key : Type} -> {metadata, value : key -> Type} ->
  DecEq key => (k : key) -> MetadataMonoid metadata -> metadata k ->
  InterContext key metadata value -> InterContext key metadata value
intercept k monoid extra ctx =
  let merged = mergeMetadata monoid k (ambientMetadata ctx k) extra
   in MkInterContext
        (replaceDependent metadata k merged (ambientMetadata ctx))
        (providerTable ctx)

public export
interceptRealisation : {key : Type} -> {metadata, value : key -> Type} ->
  DecEq key => (k : key) -> MetadataMonoid metadata -> metadata k ->
  (ctx : InterContext key metadata value) ->
  Realisation (InterContext key metadata value)
interceptRealisation k monoid extra ctx =
  DerivedRealisation ctx (intercept k monoid extra ctx)
