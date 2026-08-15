module DGamma.Coeffects

import DGamma.Core
import DGamma.Effects
import Decidable.Equality
import Data.Maybe

%default total

||| A dependently typed key/value binding.
public export
data Binding : (key : Type) -> (value : key -> Type) -> Type where
  Bind : (k : key) -> value k -> Binding key value

||| Definition 22: a finite dependent partial function.
public export
CoeffectContext : (key : Type) -> (value : key -> Type) -> Type
CoeffectContext key value = List (Binding key value)

public export
lookupBinding : DecEq key => (wanted : key) ->
  CoeffectContext key value -> Maybe (value wanted)
lookupBinding wanted [] = Nothing
lookupBinding wanted (Bind found val :: rest) with (decEq wanted found)
  lookupBinding wanted (Bind wanted val :: rest) | (Yes Refl) = Just val
  lookupBinding wanted (Bind found val :: rest) | (No _) =
    lookupBinding wanted rest

public export
memberKey : DecEq key => key -> CoeffectContext key value -> Bool
memberKey wanted table = isJust (lookupBinding wanted table)

public export
insertBinding : (k : key) -> value k -> CoeffectContext key value ->
  CoeffectContext key value
insertBinding k val table = Bind k val :: table

||| Delete the first binding at a key. Well-formed contexts contain no duplicate
||| keys, and setFresh below preserves that invariant.
public export
deleteBinding : DecEq key => key -> CoeffectContext key value ->
  CoeffectContext key value
deleteBinding wanted [] = []
deleteBinding wanted (Bind found val :: rest) with (decEq wanted found)
  deleteBinding wanted (Bind wanted val :: rest) | (Yes Refl) = rest
  deleteBinding wanted (Bind found val :: rest) | (No _) =
    Bind found val :: deleteBinding wanted rest

public export
0 deleteInserted : DecEq key => (k : key) -> (val : value k) ->
  (table : CoeffectContext key value) ->
  deleteBinding k (insertBinding k val table) = table
deleteInserted k val table with (decEq k k)
  deleteInserted k val table | (Yes Refl) = Refl
  deleteInserted k val table | (No contra) = void (contra Refl)

||| Definition 23: get, with absence represented honestly by Maybe.
public export
get : DecEq key => (k : key) -> CoeffectContext key value -> Maybe (value k)
get = lookupBinding

||| Definition 23: safe partial set. On success it returns a state-indexed undo
||| token whose executable inverse removes exactly this key.
public export
setFresh : DecEq key => (k : key) -> value k ->
  (before : CoeffectContext key value) -> Maybe (Applied before)
setFresh k val before =
  case lookupBinding k before of
    Just _ => Nothing
    Nothing => Just (MkApplied (insertBinding k val before)
                     (MkUndo (deleteBinding k) (deleteInserted k val before)))

||| Replace a present binding while preserving every other key.
public export
replaceBinding : DecEq key => (k : key) -> value k ->
  CoeffectContext key value -> CoeffectContext key value
replaceBinding k val [] = []
replaceBinding k val (Bind found old :: rest) with (decEq k found)
  replaceBinding k val (Bind k old :: rest) | (Yes Refl) = Bind k val :: rest
  replaceBinding k val (Bind found old :: rest) | (No _) =
    Bind found old :: replaceBinding k val rest

||| Definition 24: an operation offered by a coeffect value. Failure denotes a
||| violated precondition and produces no transition.
public export
record CoeffectOperation (value, argument, outcome : Type) where
  constructor MkCoeffectOperation
  runOperation : argument -> value -> Maybe (value, value -> value, outcome)
  0 operationWitness : (arg : argument) -> (before, after : value) ->
    (undo : value -> value) -> (result : outcome) ->
    runOperation arg before = Just (after, undo, result) -> undo after = before

||| Definition 24, Equation 23: executable lift of a value operation to the
||| dependent table at one key.
public export
liftOperation : DecEq key => (k : key) ->
  CoeffectOperation (value k) argument outcome -> argument ->
  CoeffectContext key value ->
  Maybe (CoeffectContext key value,
         CoeffectContext key value -> CoeffectContext key value,
         outcome)
liftOperation k op arg table =
  case lookupBinding k table of
    Nothing => Nothing
    Just old =>
      case runOperation op arg old of
        Nothing => Nothing
        Just (next, undo, result) =>
          Just (replaceBinding k next table,
                \later => case lookupBinding k later of
                  Nothing => later
                  Just now => replaceBinding k (undo now) later,
                result)

||| A specification is a finite set represented by a duplicate-free list.
||| The duplicate-free invariant is immaterial to satisfaction and is checked by
||| component well-formedness in the calculus.
public export
CoeffectSpec : Type -> Type
CoeffectSpec key = List key

||| Definition 25 / Equation 24: all declared keys are present.
public export
satisfies : DecEq key => CoeffectContext key value -> CoeffectSpec key -> Bool
satisfies table [] = True
satisfies table (k :: ks) = memberKey k table && satisfies table ks

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

||| Definition 27: the two runtime realizations of an effect.
public export
data Realisation = InPlace | Derived

||| A conventional homogeneous finite map used for realm overrides.
public export
Assoc : Type -> Type -> Type
Assoc key value = List (key, value)

public export
lookupAssoc : DecEq key => key -> Assoc key value -> Maybe value
lookupAssoc wanted [] = Nothing
lookupAssoc wanted ((found, val) :: rest) with (decEq wanted found)
  lookupAssoc wanted ((wanted, val) :: rest) | (Yes Refl) = Just val
  lookupAssoc wanted ((found, val) :: rest) | (No _) = lookupAssoc wanted rest

public export
putAssoc : DecEq key => key -> value -> Assoc key value -> Assoc key value
putAssoc wanted val [] = [(wanted, val)]
putAssoc wanted val ((found, old) :: rest) with (decEq wanted found)
  putAssoc wanted val ((wanted, old) :: rest) | (Yes Refl) = (wanted, val) :: rest
  putAssoc wanted val ((found, old) :: rest) | (No _) =
    (found, old) :: putAssoc wanted val rest

||| Definition 28: isolated coeffect context. baseRealm realizes the paper's
||| convention that an un-overridden key resolves to its own default realm.
public export
record IsoContext (key, realm : Type) (value : realm -> Type) where
  constructor MkIsoContext
  baseRealm : key -> realm
  realmOverrides : Assoc key realm
  realmBindings : CoeffectContext realm value

public export
resolveRealm : DecEq key => (k : key) -> IsoContext key realm value -> realm
resolveRealm k ctx = fromMaybe (baseRealm ctx k)
                               (lookupAssoc k (realmOverrides ctx))

||| Definition 29: isolated get.
public export
isoGet : (DecEq key, DecEq realm) => (k : key) ->
  (ctx : IsoContext key realm value) -> Maybe (value (resolveRealm k ctx))
isoGet k ctx = lookupBinding (resolveRealm k ctx) (realmBindings ctx)

||| Definition 29: isolation is a derived realization; the old context is left
||| intact and a new one carries the override.
public export
isolate : DecEq key => key -> realm -> IsoContext key realm value ->
  IsoContext key realm value
isolate k realm ctx =
  MkIsoContext (baseRealm ctx)
               (putAssoc k realm (realmOverrides ctx))
               (realmBindings ctx)

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

||| Definition 30: intercepted coeffect context.
public export
record InterContext (key : Type) (metadata, value : key -> Type) where
  constructor MkInterContext
  ambientMetadata : (k : key) -> metadata k
  providers : (k : key) -> Maybe (metadata k -> value k)

||| Definition 31: provider access with component metadata taking the left and
||| ambient/context metadata taking the right (right-biased by the monoid's
||| interpretation).
public export
interGet : (k : key) -> MetadataMonoid metadata -> metadata k ->
  InterContext key metadata value -> Maybe (value k)
interGet k monoid declared ctx =
  case providers ctx k of
    Nothing => Nothing
    Just provider =>
      Just (provider (mergeMetadata monoid k declared (ambientMetadata ctx k)))

||| Definition 31: interception is a derived realization.
public export
intercept : {key : Type} -> {metadata, value : key -> Type} ->
  DecEq key => (k : key) -> MetadataMonoid metadata -> metadata k ->
  InterContext key metadata value -> InterContext key metadata value
intercept k monoid extra ctx =
  let merged = mergeMetadata monoid k (ambientMetadata ctx k) extra
   in MkInterContext
        (replaceDependent metadata k merged (ambientMetadata ctx))
        (providers ctx)
