module DGamma.Unified

import DGamma.Core
import DGamma.Effects
import DGamma.Coeffects
import Decidable.Equality

%default total

||| Definition 32, represented at every finite level. The paper's literal
||| negative recursive domain equation cannot be declared as a strictly positive
||| Idris datatype; ContextTower n is its executable n-level approximation.
public export
record UnifiedLayer (lower, coeffects : Type) where
  constructor MkUnifiedLayer
  lowerState : lower
  lowerAccumulator : lower -> lower
  levelCoeffects : coeffects

||| Structural recursion on the height avoids the paper's non-strictly-positive
||| equation. This is explicitly a finite approximation, not an implementation
||| or proof of the paper's unguarded fixed point.
public export
ContextTower : Nat -> Type -> Type -> Type
ContextTower Z base coeffects = (base, coeffects)
ContextTower (S n) base coeffects = UnifiedLayer (ContextTower n base coeffects) coeffects

||| Existentially package any executable finite approximation to Gamma-infinity.
public export
data GammaInfinityApprox : Type -> Type -> Type where
  AtFiniteDepth : (depth : Nat) -> ContextTower depth base coeffects ->
                  GammaInfinityApprox base coeffects

public export
rootContext : base -> coeffects -> ContextTower Z base coeffects
rootContext base sigma = (base, sigma)

public export
contextLevel : ContextTower n base coeffects ->
  (ContextTower n base coeffects -> ContextTower n base coeffects) ->
  coeffects -> ContextTower (S n) base coeffects
contextLevel = MkUnifiedLayer

public export
towerCoeffects : (n : Nat) -> ContextTower n base coeffects -> coeffects
towerCoeffects Z (_, sigma) = sigma
towerCoeffects (S _) layer = levelCoeffects layer

public export
towerLower : ContextTower (S n) base coeffects -> ContextTower n base coeffects
towerLower = lowerState

public export
towerAccumulator : ContextTower (S n) base coeffects ->
  ContextTower n base coeffects -> ContextTower n base coeffects
towerAccumulator = lowerAccumulator

||| Relation lifted to Maybe, used to compare partial dependent functions.
public export
data MaybeRelated : (a : Type) -> (a -> a -> Type) -> Maybe a -> Maybe a -> Type where
  BothAbsent : MaybeRelated a rel Nothing Nothing
  BothPresent : rel x y -> MaybeRelated a rel (Just x) (Just y)

||| Definition 33: same domain and equivalent values, expressed pointwise.
public export
TableRelated : {key : Type} -> {value : key -> Type} ->
  DecEq key => ((k : key) -> Equivalence (value k)) ->
  CoeffectContext key value -> CoeffectContext key value -> Type
TableRelated {key} eqs left right = (k : key) ->
  MaybeRelated (value k) (relation (eqs k))
    (lookupBinding k left) (lookupBinding k right)

public export
0 maybeRelatedRefl : {a : Type} -> (eq : Equivalence a) -> (item : Maybe a) ->
  MaybeRelated a (relation eq) item item
maybeRelatedRefl eq Nothing = BothAbsent
maybeRelatedRefl eq (Just item) = BothPresent (reflexive eq item)

public export
0 maybeRelatedSym : {a : Type} -> (eq : Equivalence a) ->
  {left, right : Maybe a} -> MaybeRelated a (relation eq) left right ->
  MaybeRelated a (relation eq) right left
maybeRelatedSym eq BothAbsent = BothAbsent
maybeRelatedSym eq (BothPresent prf) = BothPresent (symmetric eq prf)

public export
0 maybeRelatedTrans : {a : Type} -> (eq : Equivalence a) ->
  {left, middle, right : Maybe a} ->
  MaybeRelated a (relation eq) left middle ->
  MaybeRelated a (relation eq) middle right ->
  MaybeRelated a (relation eq) left right
maybeRelatedTrans eq BothAbsent BothAbsent = BothAbsent
maybeRelatedTrans eq (BothPresent first) (BothPresent second) =
  BothPresent (transitive eq first second)

public export
0 tableRelatedRefl : {key : Type} -> {value : key -> Type} ->
  DecEq key => (eqs : (k : key) -> Equivalence (value k)) ->
  (table : CoeffectContext key value) -> TableRelated eqs table table
tableRelatedRefl eqs table k = maybeRelatedRefl (eqs k) (lookupBinding k table)

public export
0 tableRelatedSym : {key : Type} -> {value : key -> Type} ->
  DecEq key => (eqs : (k : key) -> Equivalence (value k)) ->
  {left, right : CoeffectContext key value} ->
  TableRelated eqs left right -> TableRelated eqs right left
tableRelatedSym eqs related k = maybeRelatedSym (eqs k) (related k)

public export
0 tableRelatedTrans : {key : Type} -> {value : key -> Type} ->
  DecEq key => (eqs : (k : key) -> Equivalence (value k)) ->
  {left, middle, right : CoeffectContext key value} ->
  TableRelated eqs left middle -> TableRelated eqs middle right ->
  TableRelated eqs left right
tableRelatedTrans eqs lm mr k = maybeRelatedTrans (eqs k) (lm k) (mr k)

public export
tableEquivalence : {key : Type} -> {value : key -> Type} -> DecEq key =>
  (eqs : (k : key) -> Equivalence (value k)) ->
  Equivalence (CoeffectContext key value)
tableEquivalence {key} {value} eqs = MkEquivalence (TableRelated eqs)
  (tableRelatedRefl eqs)
  (tableRelatedSym eqs)
  (tableRelatedTrans eqs)

||| Definition 33 on an arbitrary unified runtime state with a coeffect
||| projection.
public export
StateRelated : {state, key : Type} -> {value : key -> Type} ->
  DecEq key => (project : state -> CoeffectContext key value) ->
  ((k : key) -> Equivalence (value k)) -> state -> state -> Type
StateRelated project eqs left right = TableRelated eqs (project left) (project right)

||| Definition 36: a map respects an observational equivalence.
public export
MapRespects : {state : Type} -> Equivalence state -> (state -> state) -> Type
MapRespects {state} eq f = {x, y : state} -> relation eq x y -> relation eq (f x) (f y)

||| Definition 36: pointwise related maps.
public export
MapsRelated : {state : Type} -> Equivalence state -> (state -> state) -> (state -> state) -> Type
MapsRelated {state} eq f g = (x : state) -> relation eq (f x) (g x)

||| Runtime result of an effect witnessed up to an equivalence. Runtime fields
||| are unrestricted; all laws are erased.
public export
record RelResult {state : Type} (eq : Equivalence state) (before : state) where
  constructor MkRelResult
  next : state
  inverse : state -> state
  0 inverseWitness : relation eq (inverse next) before
  0 inverseRespects : MapRespects eq inverse

||| Definition 37: witnessed effect function up to observational equivalence.
public export
record RelEffStar (state : Type) (eq : Equivalence state) where
  constructor MkRelEffStar
  runRelEff : (before : state) -> RelResult eq before
  0 effectRespects : {x, y : state} -> relation eq x y ->
    (relation eq (next (runRelEff x)) (next (runRelEff y)),
     MapsRelated eq (inverse (runRelEff x)) (inverse (runRelEff y)))

public export
eraseRelEff : RelEffStar state eq -> EffFn state
eraseRelEff e x = let result = runRelEff e x in (next result, inverse result)

||| Equality-witnessed effects embed into witnessing up to any equivalence that
||| contains equality, in particular Definition 8 is recovered at equality.
public export
fromEffStar : (e : EffStar state) -> RelEffStar state (EqEquivalence {a = state})
fromEffStar e = MkRelEffStar run respects
  where
  run : (x : state) -> RelResult EqEquivalence x
  run x with (runEff e x) proof returned
    run x | (y, undo) = MkRelResult y undo
      (witnessedAt e x y undo returned)
      undoRespect
      where
      0 undoRespect : {left, right : state} -> left = right -> undo left = undo right
      undoRespect Refl = Refl

  0 respects : {x, y : state} -> x = y ->
    (next (run x) = next (run y),
     MapsRelated EqEquivalence (inverse (run x)) (inverse (run y)))
  respects Refl = (Refl, \_ => Refl)

||| The relational unit effect.
public export
relEta : (eq : Equivalence state) -> RelEffStar state eq
relEta eq = MkRelEffStar runUnit respectsUnit
  where
  runUnit : (x : state) -> RelResult eq x
  runUnit x = MkRelResult x (\v => v) (reflexive eq x) idRespect
    where
    0 idRespect : MapRespects eq (\v => v)
    idRespect related = related

  0 respectsUnit : {x, y : state} -> relation eq x y ->
    (relation eq (next (runUnit x)) (next (runUnit y)),
     MapsRelated eq (inverse (runUnit x)) (inverse (runUnit y)))
  respectsUnit related = (related, \probe => reflexive eq probe)

||| Lemma 38 / Theorem 11 relational core: witnessed, respectful effects remain
||| witnessed and respectful under diamond composition.
public export
relDiamond : RelEffStar state eq -> RelEffStar state eq -> RelEffStar state eq
relDiamond f g = MkRelEffStar runCombined respectsCombined
  where
  combineResult : (x : state) -> (rg : RelResult eq x) ->
    (rf : RelResult eq (next rg)) -> RelResult eq x
  combineResult x rg rf = MkRelResult
    (next rf) (inverse rg . inverse rf)
    (transitive eq (inverseRespects rg (inverseWitness rf))
                   (inverseWitness rg))
    (\related => inverseRespects rg (inverseRespects rf related))

  runCombined : (x : state) -> RelResult eq x
  runCombined x =
    let rg = runRelEff g x
     in combineResult x rg (runRelEff f (next rg))

  0 respectsCombined : {x, y : state} -> relation eq x y ->
    (relation eq (next (runCombined x)) (next (runCombined y)),
     MapsRelated eq (inverse (runCombined x)) (inverse (runCombined y)))
  respectsCombined {x} {y} related =
    let gRespect = effectRespects g related
        gNext = fst gRespect
        gUndo = snd gRespect
        fRespect = effectRespects f gNext
        fNext = fst fRespect
        fUndo = snd fRespect
        undos = \probe =>
          transitive eq
            (inverseRespects (runRelEff g x) (fUndo probe))
            (gUndo (inverse (runRelEff f (next (runRelEff g y))) probe))
     in (fNext, undos)

||| The relational soundness invariant of Lemma 38.
public export
record RelEffectStack (state : Type) (eq : Equivalence state)
                      (current, initial : state) where
  constructor MkRelEffectStack
  relAccumulator : state -> state
  0 relAccumulatorRespects : MapRespects eq relAccumulator
  0 relStackSound : relation eq (relAccumulator current) initial

public export
relEmptyStack : (eq : Equivalence state) -> (x : state) ->
  RelEffectStack state eq x x
relEmptyStack eq x = MkRelEffectStack (\v => v) idRespect (reflexive eq x)
  where
  0 idRespect : MapRespects eq (\v => v)
  idRespect related = related

public export
relPushStack : {current, initial : state} -> (e : RelEffStar state eq) ->
  RelEffectStack state eq current initial ->
  (resultState ** RelEffectStack state eq resultState initial)
relPushStack {current = before} e (MkRelEffectStack acc accRespect sound) =
  let result = runRelEff e before
   in (next result ** MkRelEffectStack (acc . inverse result)
         (pushedRespect result) (pushedSound result))
  where
  0 pushedRespect : (result : RelResult eq before) ->
    MapRespects eq (acc . inverse result)
  pushedRespect result related = accRespect (inverseRespects result related)

  0 pushedSound : (result : RelResult eq before) ->
    relation eq ((acc . inverse result) (next result)) initial
  pushedSound result = transitive eq
    (accRespect (inverseWitness result)) sound

||| Definition 34: a heterogeneous suite of Definition-24 operations sharing
||| one observational equivalence.
public export
record OperationSuite (value : Type) where
  constructor MkOperationSuite
  suiteEquivalence : Equivalence value
  OpCode : Type
  Argument : OpCode -> Type
  Outcome : OpCode -> Type
  suiteOperation : (code : OpCode) ->
    CoeffectOperation value (Argument code) (Outcome code)
  0 operationUsesSuiteEquivalence : (code : OpCode) ->
    valueEquivalence (suiteOperation code) = suiteEquivalence

public export
applyOperation : (suite : OperationSuite value) ->
  (code : OpCode suite) -> Argument suite code -> value ->
  Maybe (value, PartialMap value, Outcome suite code)
applyOperation suite code = runOperation (suiteOperation suite code)

public export
data TestStep : (code : Type) -> (argument : code -> Type) -> Type -> Type where
  ForwardStep : (op : code) -> argument op -> TestStep code argument value
  ||| Use one concrete yielded inverse on the current test state. This checks
  ||| that each inverse individually respects indistinguishability.
  FixedInverseStep : (op : code) -> argument op -> (origin : value) ->
                     TestStep code argument value
  ||| Yield inverses dynamically at the two compared states, then apply them to
  ||| one common probe. This makes pointwise comparison of yielded inverses
  ||| observable and closes the countermodel to the earlier test language.
  YieldedInverseStep : (op : code) -> argument op -> (probe : value) ->
                       TestStep code argument value

public export
data Observation : (code : Type) -> (outcome : code -> Type) -> Type where
  Observed : (op : code) -> outcome op -> Observation code outcome

public export
runTest : (suite : OperationSuite value) -> value ->
  List (TestStep (OpCode suite) (Argument suite) value) ->
  Maybe (List (Observation (OpCode suite) (Outcome suite)))
runTest suite start [] = Just []
runTest suite start (ForwardStep op arg :: rest) =
  case applyOperation suite op arg start of
    Nothing => Nothing
    Just (next, undo, result) =>
      map (Observed op result ::) (runTest suite next rest)
runTest suite start (FixedInverseStep op arg origin :: rest) =
  case applyOperation suite op arg origin of
    Nothing => Nothing
    Just (next, undo, result) => case undo start of
      Nothing => Nothing
      Just prior => runTest suite prior rest
runTest suite start (YieldedInverseStep op arg probe :: rest) =
  case applyOperation suite op arg start of
    Nothing => Nothing
    Just (next, undo, result) => case undo probe of
      Nothing => Nothing
      Just prior => runTest suite prior rest

||| Definition 34: no finite operation/inverse test distinguishes the values.
public export
Indistinguishable : {value : Type} -> (suite : OperationSuite value) -> value -> value -> Type
Indistinguishable {value} suite left right =
  (test : List (TestStep (OpCode suite) (Argument suite) value)) ->
  runTest suite left test = runTest suite right test

public export
data PartialIndistinguishable : (suite : OperationSuite value) ->
  Maybe value -> Maybe value -> Type where
  BothTestsUndefined : PartialIndistinguishable suite Nothing Nothing
  BothTestsDefined : Indistinguishable suite left right ->
    PartialIndistinguishable suite (Just left) (Just right)

public export
PartialMapPreservesIndistinguishability : {value : Type} ->
  (suite : OperationSuite value) -> PartialMap value -> Type
PartialMapPreservesIndistinguishability {value} suite map =
  {x, y : value} -> Indistinguishable suite x y ->
  PartialIndistinguishable suite (map x) (map y)

public export
PartialMapsIndistinguishablyRelated : {value : Type} ->
  (suite : OperationSuite value) -> PartialMap value -> PartialMap value -> Type
PartialMapsIndistinguishablyRelated {value} suite left right =
  (probe : value) -> PartialIndistinguishable suite (left probe) (right probe)

||| Exact result agreement required by operation respect: aligned definedness,
||| equal outcomes, indistinguishable successors, and relation-respecting
||| partial inverses.
public export
data IndistResultAgreement : {value : Type} -> (suite : OperationSuite value) ->
  {op : OpCode suite} ->
  Maybe (value, PartialMap value, Outcome suite op) ->
  Maybe (value, PartialMap value, Outcome suite op) -> Type where
  IndistResultsUndefined : IndistResultAgreement suite Nothing Nothing
  IndistResultsDefined : outLeft = outRight ->
    Indistinguishable suite nextLeft nextRight ->
    PartialMapsIndistinguishablyRelated suite undoLeft undoRight ->
    PartialMapPreservesIndistinguishability suite undoLeft ->
    PartialMapPreservesIndistinguishability suite undoRight ->
    IndistResultAgreement suite
      (Just (nextLeft, undoLeft, outLeft))
      (Just (nextRight, undoRight, outRight))

public export
data CandidateResultAgreement : (candidate : value -> value -> Type) ->
  Maybe (value, PartialMap value, outcome) ->
  Maybe (value, PartialMap value, outcome) -> Type where
  CandidateUndefined : CandidateResultAgreement candidate Nothing Nothing
  CandidateDefined : outLeft = outRight -> candidate nextLeft nextRight ->
    ((probe : value) ->
      PartialRelated value candidate (undoLeft probe) (undoRight probe)) ->
    ({x, y : value} -> candidate x y ->
      PartialRelated value candidate (undoLeft x) (undoLeft y)) ->
    ({x, y : value} -> candidate x y ->
      PartialRelated value candidate (undoRight x) (undoRight y)) ->
    CandidateResultAgreement candidate
      (Just (nextLeft, undoLeft, outLeft))
      (Just (nextRight, undoRight, outRight))

||| Lemma 35, stated with every Definition-24 respect obligation present.
||| TODO(proof): prefix closure over the heterogeneous test trace.
public export
OperationsRespectIndistinguishability : {value : Type} -> OperationSuite value -> Type
OperationsRespectIndistinguishability {value} suite =
  (op : OpCode suite) -> (arg : Argument suite op) ->
  {left, right : value} -> Indistinguishable suite left right ->
  IndistResultAgreement suite (applyOperation suite op arg left)
                                 (applyOperation suite op arg right)

public export
CoarsestRespectedEquivalence : {value : Type} -> OperationSuite value -> Type
CoarsestRespectedEquivalence {value} suite =
  (candidate : value -> value -> Type) ->
  ((op : OpCode suite) -> (arg : Argument suite op) ->
    {left, right : value} -> candidate left right ->
    CandidateResultAgreement candidate (applyOperation suite op arg left)
                                       (applyOperation suite op arg right)) ->
  {left, right : value} -> candidate left right -> Indistinguishable suite left right

public export
partialIdentity : PartialMap state
partialIdentity x = Just x

public export
partialCompose : PartialMap state -> PartialMap state -> PartialMap state
partialCompose after before x = case before x of
  Nothing => Nothing
  Just middle => after middle

public export
PartialMapsEquivalent : {state : Type} -> Equivalence state ->
  PartialMap state -> PartialMap state -> Type
PartialMapsEquivalent {state} eq left right = (x : state) ->
  PartialRelated state (relation eq) (left x) (right x)

public export
PartialCommute : {state : Type} -> Equivalence state ->
  PartialMap state -> PartialMap state -> Type
PartialCommute eq left right =
  PartialMapsEquivalent eq (partialCompose left right)
                           (partialCompose right left)

||| Definition 39's generated transformation monoid for a partial operation at
||| a fixed argument.
public export
data PartialGenerator : (value : Type) -> (suite : OperationSuite value) ->
  (op : OpCode suite) -> Argument suite op -> Type where
  PartialForward : PartialGenerator value suite op arg
  PartialYielded : (origin : value) -> PartialGenerator value suite op arg

public export
partialGeneratorMap : {value : Type} -> (suite : OperationSuite value) ->
  {op : OpCode suite} -> {arg : Argument suite op} ->
  PartialGenerator value suite op arg -> PartialMap value
partialGeneratorMap {value} suite {op} {arg} PartialForward x =
  case applyOperation suite op arg x of
    Nothing => Nothing
    Just (next, _, _) => Just next
partialGeneratorMap {value} suite {op} {arg} (PartialYielded origin) x =
  case applyOperation suite op arg origin of
    Nothing => Nothing
    Just (_, undo, _) => undo x

public export
data PartialTransformation : (value : Type) -> (suite : OperationSuite value) ->
  (op : OpCode suite) -> Argument suite op -> Type where
  PartialIdentityT : PartialTransformation value suite op arg
  PartialGeneratorT : PartialGenerator value suite op arg ->
                      PartialTransformation value suite op arg
  PartialComposeT : PartialTransformation value suite op arg ->
                    PartialTransformation value suite op arg ->
                    PartialTransformation value suite op arg

public export
runPartialTransformation : {value : Type} -> (suite : OperationSuite value) ->
  {op : OpCode suite} -> {arg : Argument suite op} ->
  PartialTransformation value suite op arg -> PartialMap value
runPartialTransformation suite PartialIdentityT = partialIdentity
runPartialTransformation suite (PartialGeneratorT generator) =
  partialGeneratorMap suite generator
runPartialTransformation suite (PartialComposeT after before) =
  partialCompose (runPartialTransformation suite after)
                 (runPartialTransformation suite before)

public export
data OperationYieldAgreement : (eq : Equivalence value) ->
  Maybe (value, PartialMap value, outcome) ->
  Maybe (value, PartialMap value, outcome) -> Type where
  YieldsBothUndefined : OperationYieldAgreement eq Nothing Nothing
  YieldsAgree : leftOutcome = rightOutcome ->
    PartialMapsEquivalent eq leftUndo rightUndo ->
    OperationYieldAgreement eq
      (Just (leftNext, leftUndo, leftOutcome))
      (Just (rightNext, rightUndo, rightOutcome))

public export
YieldStableUnder : (suite : OperationSuite value) ->
  (own : OpCode suite) -> Argument suite own ->
  PartialMap value -> value -> Type
YieldStableUnder suite own ownArg foreign origin =
  case foreign origin of
    Nothing => Unit
    Just moved => OperationYieldAgreement (suiteEquivalence suite)
      (applyOperation suite own ownArg origin)
      (applyOperation suite own ownArg moved)

||| Definition 39, now read up to the suite's observational equivalence and
||| quantified only over states reached by foreign generated transformations.
public export
record OperationsIndependent (suite : OperationSuite value)
                             (left, right : OpCode suite) where
  constructor MkOperationsIndependent
  0 transformationsCommute :
    (leftArg : Argument suite left) -> (rightArg : Argument suite right) ->
    (leftT : PartialTransformation value suite left leftArg) ->
    (rightT : PartialTransformation value suite right rightArg) ->
    PartialCommute (suiteEquivalence suite)
      (runPartialTransformation suite leftT)
      (runPartialTransformation suite rightT)
  0 leftYieldStable :
    (leftArg : Argument suite left) -> (rightArg : Argument suite right) ->
    (foreign : PartialTransformation value suite right rightArg) ->
    (origin : value) ->
    YieldStableUnder suite left leftArg
      (runPartialTransformation suite foreign) origin
  0 rightYieldStable :
    (leftArg : Argument suite left) -> (rightArg : Argument suite right) ->
    (foreign : PartialTransformation value suite left leftArg) ->
    (origin : value) ->
    YieldStableUnder suite right rightArg
      (runPartialTransformation suite foreign) origin

||| Theorem 40 is stated only for operations constructed locally on one key;
||| arbitrary whole-state operations cannot merely be tagged with a key.
public export
record KeyedOperationSuite (key : Type) (value : key -> Type) where
  constructor MkKeyedOperationSuite
  keyEquivalences : (k : key) -> Equivalence (value k)
  KeyOpCode : Type
  operationKey : KeyOpCode -> key
  KeyArgument : KeyOpCode -> Type
  KeyOutcome : KeyOpCode -> Type
  localOperation : (op : KeyOpCode) ->
    CoeffectOperation (value (operationKey op))
      (KeyArgument op) (KeyOutcome op)
  0 localUsesKeyEquivalence : (op : KeyOpCode) ->
    valueEquivalence (localOperation op) = keyEquivalences (operationKey op)

public export
keyedApply : {key : Type} -> {value : key -> Type} ->
  DecEq key => (suite : KeyedOperationSuite key value) ->
  (op : KeyOpCode suite) -> KeyArgument suite op ->
  (table : CoeffectContext key value) ->
  Maybe (LiftedOperationResult table (KeyOutcome suite op))
keyedApply suite op arg table =
  liftOperation (operationKey suite op) (localOperation suite op) arg table

public export
keyedPartialEff : {key : Type} -> {value : key -> Type} ->
  DecEq key => (suite : KeyedOperationSuite key value) ->
  (op : KeyOpCode suite) -> KeyArgument suite op ->
  CoeffectContext key value ->
  Maybe (CoeffectContext key value,
         CoeffectContext key value -> Maybe (CoeffectContext key value))
keyedPartialEff suite op arg table =
  map (\lifted => (liftedAfter lifted, liftedUndo lifted))
      (keyedApply suite op arg table)

||| A partial effect function and Definition-19 independence for such effects.
public export
PartialEffFn : Type -> Type
PartialEffFn state = state -> Maybe (state, PartialMap state)

public export
data PartialEffGenerator : (state : Type) -> PartialEffFn state -> Type where
  PartialEffForward : PartialEffGenerator state eff
  PartialEffYielded : (origin : state) -> PartialEffGenerator state eff

public export
partialEffGeneratorMap : {state : Type} -> {eff : PartialEffFn state} ->
  PartialEffGenerator state eff -> PartialMap state
partialEffGeneratorMap {state} {eff} PartialEffForward x =
  case eff x of Nothing => Nothing; Just (next, _) => Just next
partialEffGeneratorMap {state} {eff} (PartialEffYielded origin) x =
  case eff origin of Nothing => Nothing; Just (_, undo) => undo x

public export
data PartialEffTransformation : (state : Type) -> PartialEffFn state -> Type where
  PartialEffIdentityT : PartialEffTransformation state eff
  PartialEffGeneratorT : PartialEffGenerator state eff ->
                         PartialEffTransformation state eff
  PartialEffComposeT : PartialEffTransformation state eff ->
                       PartialEffTransformation state eff ->
                       PartialEffTransformation state eff

public export
runPartialEffTransformation : {state : Type} -> {eff : PartialEffFn state} ->
  PartialEffTransformation state eff -> PartialMap state
runPartialEffTransformation PartialEffIdentityT = partialIdentity
runPartialEffTransformation (PartialEffGeneratorT generator) =
  partialEffGeneratorMap generator
runPartialEffTransformation (PartialEffComposeT after before) =
  partialCompose (runPartialEffTransformation after)
                 (runPartialEffTransformation before)

public export
data PartialEffectYieldAgreement : (state : Type) -> Equivalence state ->
  Maybe (state, PartialMap state) -> Maybe (state, PartialMap state) -> Type where
  PartialEffectBothUndefined : PartialEffectYieldAgreement state eq Nothing Nothing
  PartialEffectYieldsAgree : PartialMapsEquivalent eq leftUndo rightUndo ->
    PartialEffectYieldAgreement state eq
      (Just (leftNext, leftUndo)) (Just (rightNext, rightUndo))

public export
PartialEffectYieldStableUnder : {state : Type} -> (eq : Equivalence state) ->
  PartialEffFn state -> PartialMap state -> state -> Type
PartialEffectYieldStableUnder {state} eq own foreign origin =
  case foreign origin of
    Nothing => Unit
    Just moved => PartialEffectYieldAgreement state eq (own origin) (own moved)

public export
record PartialEffectIndependent (eq : Equivalence state)
                                (left, right : PartialEffFn state) where
  constructor MkPartialEffectIndependent
  0 partialEffectsCommute :
    (leftT : PartialEffTransformation state left) ->
    (rightT : PartialEffTransformation state right) ->
    PartialCommute eq (runPartialEffTransformation leftT)
                      (runPartialEffTransformation rightT)
  0 partialLeftYieldStable : (foreign : PartialEffTransformation state right) ->
    (origin : state) -> PartialEffectYieldStableUnder eq left
      (runPartialEffTransformation foreign) origin
  0 partialRightYieldStable : (foreign : PartialEffTransformation state left) ->
    (origin : state) -> PartialEffectYieldStableUnder eq right
      (runPartialEffTransformation foreign) origin

public export
data LiftedOutcomeAgreement : (state : Type) -> (eq : Equivalence state) ->
  Maybe (state, PartialMap state, outcome) ->
  Maybe (state, PartialMap state, outcome) -> Type where
  LiftedOutcomesUndefined : LiftedOutcomeAgreement state eq Nothing Nothing
  LiftedOutcomesAgree : leftOutcome = rightOutcome ->
    PartialMapsEquivalent eq leftUndo rightUndo ->
    LiftedOutcomeAgreement state eq
      (Just (leftNext, leftUndo, leftOutcome))
      (Just (rightNext, rightUndo, rightOutcome))

public export
LiftedOutcomeStableUnder : {key : Type} -> {value : key -> Type} -> DecEq key =>
  (suite : KeyedOperationSuite key value) ->
  (own : KeyOpCode suite) -> KeyArgument suite own ->
  PartialMap (CoeffectContext key value) -> CoeffectContext key value -> Type
LiftedOutcomeStableUnder {key} {value} suite own ownArg foreign origin =
  case foreign origin of
    Nothing => Unit
    Just moved => LiftedOutcomeAgreement (CoeffectContext key value)
      (tableEquivalence (keyEquivalences suite))
      (map (\lifted => (liftedAfter lifted, liftedUndo lifted,
                         liftedOutcome lifted))
        (keyedApply suite own ownArg origin))
      (map (\lifted => (liftedAfter lifted, liftedUndo lifted,
                         liftedOutcome lifted))
        (keyedApply suite own ownArg moved))

||| Definition 39 specialized to genuine dependent-table lifts.
public export
record LiftedOperationsIndependent (keyEq : DecEq key)
                                   (suite : KeyedOperationSuite key value)
                                   (left, right : KeyOpCode suite) where
  constructor MkLiftedOperationsIndependent
  0 liftedIndependent : (leftArg : KeyArgument suite left) ->
    (rightArg : KeyArgument suite right) ->
    PartialEffectIndependent (tableEquivalence @{keyEq} (keyEquivalences suite))
      (keyedPartialEff @{keyEq} suite left leftArg)
      (keyedPartialEff @{keyEq} suite right rightArg)
  0 leftLiftedOutcomeStable : (leftArg : KeyArgument suite left) ->
    (rightArg : KeyArgument suite right) ->
    (foreign : PartialEffTransformation (CoeffectContext key value)
      (keyedPartialEff @{keyEq} suite right rightArg)) ->
    (origin : CoeffectContext key value) ->
    LiftedOutcomeStableUnder @{keyEq} suite left leftArg
      (runPartialEffTransformation foreign) origin
  0 rightLiftedOutcomeStable : (leftArg : KeyArgument suite left) ->
    (rightArg : KeyArgument suite right) ->
    (foreign : PartialEffTransformation (CoeffectContext key value)
      (keyedPartialEff @{keyEq} suite left leftArg)) ->
    (origin : CoeffectContext key value) ->
    LiftedOutcomeStableUnder @{keyEq} suite right rightArg
      (runPartialEffTransformation foreign) origin

||| Theorem 40, correctly confined to distinct dependent-table lifts.
||| TODO(proof): prove the partial-map commuting diagrams for distinct keys.
public export
distinctKeysIndependent : (key : Type) -> (value : key -> Type) -> Type
distinctKeysIndependent key value =
  (keyEq : DecEq key) -> (suite : KeyedOperationSuite key value) ->
  (left : KeyOpCode suite) -> (right : KeyOpCode suite) ->
  Not (operationKey suite left = operationKey suite right) ->
  LiftedOperationsIndependent keyEq suite left right

||| Definition 41: a computation assembled solely from keyed coeffect
||| operations, with continuations selected by outcomes.
public export
data Mediated : (suite : KeyedOperationSuite key value) -> Type where
  Done : Mediated suite
  Stage : (op : KeyOpCode suite) -> (arg : KeyArgument suite op) ->
          (KeyOutcome suite op -> Mediated suite) -> Mediated suite

public export
runMediated : {key : Type} -> {value : key -> Type} ->
  DecEq key => (suite : KeyedOperationSuite key value) ->
  Mediated suite -> PartialEffFn (CoeffectContext key value)
runMediated suite Done table = Just (table, \later => Just later)
runMediated suite (Stage op arg continue) table =
  case keyedApply suite op arg table of
    Nothing => Nothing
    Just lifted =>
      case runMediated suite (continue (liftedOutcome lifted))
        (liftedAfter lifted) of
        Nothing => Nothing
        Just (final, restUndo) =>
          Just (final, partialCompose (liftedUndo lifted) restUndo)

public export
data Occurs : {key : Type} -> {value : key -> Type} ->
  (suite : KeyedOperationSuite key value) ->
  (op : KeyOpCode suite) -> Mediated suite -> Type where
  OccursHere : Occurs suite op (Stage op arg continue)
  OccursLater : (outcome : KeyOutcome suite currentOp) ->
    Occurs suite op (continue outcome) ->
    Occurs suite op (Stage currentOp arg continue)

||| Definition 39's interface-wide key commutativity: every pair of operations
||| published at the key, including self-pairs, is independent.
public export
keyCommutative : {key : Type} -> {value : key -> Type} ->
  (keyEq : DecEq key) -> (suite : KeyedOperationSuite key value) -> key -> Type
keyCommutative keyEq suite k =
  (leftOp : KeyOpCode suite) -> (rightOp : KeyOpCode suite) ->
  operationKey suite leftOp = k -> operationKey suite rightOp = k ->
  LiftedOperationsIndependent keyEq suite leftOp rightOp

public export
record ProgramUsesKey (suite : KeyedOperationSuite key value)
                      (k : key) (program : Mediated suite) where
  constructor MkProgramUsesKey
  usedOperation : KeyOpCode suite
  operationOccurs : Occurs suite usedOperation program
  operationAtKey : operationKey suite usedOperation = k

||| The literal paper hypothesis: each key at which both programs have an
||| occurring operation is commutative for its whole published interface.
public export
sharedKeysCommutative : {key : Type} -> {value : key -> Type} ->
  (keyEq : DecEq key) -> (suite : KeyedOperationSuite key value) ->
  Mediated suite -> Mediated suite -> Type
sharedKeysCommutative keyEq suite left right =
  (k : key) -> ProgramUsesKey suite k left -> ProgramUsesKey suite k right ->
  keyCommutative keyEq suite k

||| Theorem 42, now with its exact interface-wide shared-key premise.
||| TODO(proof): structural induction on both mediated continuation trees.
public export
MediatedIndependenceTheorem : (key : Type) -> (value : key -> Type) -> Type
MediatedIndependenceTheorem key value =
  (keyEq : DecEq key) -> (suite : KeyedOperationSuite key value) ->
  (left : Mediated suite) -> (right : Mediated suite) ->
  sharedKeysCommutative keyEq suite left right ->
  PartialEffectIndependent (tableEquivalence @{keyEq} (keyEquivalences suite))
    (runMediated @{keyEq} suite left) (runMediated @{keyEq} suite right)
