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
||| equation while preserving every finite observation of its tower.
public export
ContextTower : Nat -> Type -> Type -> Type
ContextTower Z base coeffects = (base, coeffects)
ContextTower (S n) base coeffects = UnifiedLayer (ContextTower n base coeffects) coeffects

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
relPushStack {current} e (MkRelEffectStack acc accRespect sound) =
  let result = runRelEff e current
   in (next result ** MkRelEffectStack (acc . inverse result)
         (pushedRespect result) (pushedSound result))
  where
  0 pushedRespect : (result : RelResult eq current) ->
    MapRespects eq (acc . inverse result)
  pushedRespect result related = accRespect (inverseRespects result related)

  0 pushedSound : (result : RelResult eq current) ->
    relation eq ((acc . inverse result) (next result)) initial
  pushedSound result = transitive eq
    (accRespect (inverseWitness result)) sound

||| Definition 34: a heterogeneously typed operation suite.
public export
record OperationSuite (value : Type) where
  constructor MkOperationSuite
  OpCode : Type
  Argument : OpCode -> Type
  Outcome : OpCode -> Type
  applyOperation : (code : OpCode) -> Argument code -> value ->
    Maybe (value, value -> value, Outcome code)

public export
data TestStep : (code : Type) -> (argument : code -> Type) -> Type -> Type where
  ForwardStep : (op : code) -> argument op -> TestStep code argument value
  InverseStep : (op : code) -> argument op -> (origin : value) ->
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
runTest suite start (InverseStep op arg origin :: rest) =
  case applyOperation suite op arg origin of
    Nothing => Nothing
    Just (next, undo, result) => runTest suite (undo start) rest

||| Definition 34: no finite operation test distinguishes the values.
public export
Indistinguishable : {value : Type} -> (suite : OperationSuite value) -> value -> value -> Type
Indistinguishable {value} suite left right =
  (test : List (TestStep (OpCode suite) (Argument suite) value)) ->
  runTest suite left test = runTest suite right test

||| Result-agreement predicates used to state Lemma 35 without an inaccessible
||| dependent case expression in a top-level type synonym.
public export
IndistResultAgreement : {value : Type} -> (suite : OperationSuite value) ->
  {op : OpCode suite} -> Maybe (value, value -> value, Outcome suite op) ->
  Maybe (value, value -> value, Outcome suite op) -> Type
IndistResultAgreement suite Nothing Nothing = Unit
IndistResultAgreement suite (Just (nextL, undoL, outL))
                               (Just (nextR, undoR, outR)) =
  (outL = outR,
   Indistinguishable suite nextL nextR,
   (x : value) -> Indistinguishable suite (undoL x) (undoR x))
IndistResultAgreement suite _ _ = Void

public export
SuccessorAgreement : {value, outcome : Type} -> (candidate : value -> value -> Type) ->
  Maybe (value, value -> value, outcome) ->
  Maybe (value, value -> value, outcome) -> Type
SuccessorAgreement candidate Nothing Nothing = Unit
SuccessorAgreement candidate (Just (nextL, _, _)) (Just (nextR, _, _)) =
  candidate nextL nextR
SuccessorAgreement candidate _ _ = Void

||| Lemma 35 is stated as the exact universal property proved in the paper.
||| It is a type (not a postulate); no inhabitant is claimed in this model,
||| because the paper does not define equality for heterogeneous outcome traces.
||| TODO(proof): formalize prefix closure for heterogeneous traces.
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
    SuccessorAgreement candidate (applyOperation suite op arg left)
                                 (applyOperation suite op arg right)) ->
  {left, right : value} -> candidate left right -> Indistinguishable suite left right

||| Definition 39: operation independence, including outcomes, stated over a
||| homogeneous operation suite. Equality may be replaced by relation eq.
public export
record OperationsIndependent (suite : OperationSuite value)
                             (eq : Equivalence value)
                             (left, right : OpCode suite) where
  constructor MkOperationsIndependent
  0 liftedEffectsIndependent : (leftArg : Argument suite left) ->
    (rightArg : Argument suite right) ->
    Independent
      (\x => case applyOperation suite left leftArg x of
        Nothing => (x, id)
        Just (next, undo, _) => (next, undo))
      (\x => case applyOperation suite right rightArg x of
        Nothing => (x, id)
        Just (next, undo, _) => (next, undo))
  0 outcomesStableLeft : (leftArg : Argument suite left) ->
    (rightArg : Argument suite right) -> (origin, moved : value) ->
    case (applyOperation suite left leftArg origin,
          applyOperation suite left leftArg moved) of
      (Nothing, Nothing) => Unit
      (Just (_, _, out1), Just (_, _, out2)) => out1 = out2
      _ => Void
  0 outcomesStableRight : (leftArg : Argument suite left) ->
    (rightArg : Argument suite right) -> (origin, moved : value) ->
    case (applyOperation suite right rightArg origin,
          applyOperation suite right rightArg moved) of
      (Nothing, Nothing) => Unit
      (Just (_, _, out1), Just (_, _, out2)) => out1 = out2
      _ => Void

||| A keyed operation suite for Theorem 40.
public export
record KeyedOperationSuite (key, value : Type) where
  constructor MkKeyedOperationSuite
  keyedSuite : OperationSuite value
  operationKey : OpCode keyedSuite -> key

||| Theorem 40, stated at the exact operation-independence relation above.
||| TODO(proof): lift distinct-key table commutation through partial operations.
public export
distinctKeysIndependent : (key, value : Type) -> Type
distinctKeysIndependent key value =
  (keyed : KeyedOperationSuite key value) -> DecEq key =>
  (eq : Equivalence value) ->
  (left : OpCode (keyedSuite keyed)) ->
  (right : OpCode (keyedSuite keyed)) ->
  Not (operationKey keyed left = operationKey keyed right) ->
  OperationsIndependent (keyedSuite keyed) eq left right

||| Definition 41: a computation assembled solely from coeffect operations,
||| with later stages chosen from earlier outcomes.
public export
data Mediated : (suite : OperationSuite value) -> Type where
  Done : Mediated suite
  Stage : (op : OpCode suite) -> (arg : Argument suite op) ->
          (Outcome suite op -> Mediated suite) -> Mediated suite

||| Executable interpretation of Definition 41. Inverses compose in LIFO order.
public export
runMediated : (suite : OperationSuite value) -> Mediated suite -> EffFn value
runMediated suite Done x = (x, id)
runMediated suite (Stage op arg continue) x =
  case applyOperation suite op arg x of
    Nothing => (x, id)
    Just (next, undo, result) =>
      let (final, restUndo) = runMediated suite (continue result) next
       in (final, undo . restUndo)

||| Theorem 42, stated precisely for the executable mediated language. An
||| inhabitant is intentionally not fabricated; see NOTES for the missing
||| heterogeneous commutation development.
||| TODO(proof): induction on Mediated using generator commutation and outcomes.
public export
MediatedIndependenceTheorem : {value : Type} -> (suite : OperationSuite value) -> Type
MediatedIndependenceTheorem {value} suite =
  (left, right : Mediated suite) ->
  Independent (runMediated suite left) (runMediated suite right)
