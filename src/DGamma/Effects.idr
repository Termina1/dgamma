module DGamma.Effects

import DGamma.Core
import Data.List

%default total

||| Definition 1: a pair in the twisted composition monoid T_Gamma.
public export
record Twisted (state : Type) where
  constructor MkTwisted
  forward : state -> state
  backward : state -> state

||| Definition 1: (f1,g1) after (f2,g2), with inverses accumulated oppositely.
public export
twisted : Twisted state -> Twisted state -> Twisted state
twisted (MkTwisted f1 g1) (MkTwisted f2 g2) =
  MkTwisted (f1 . f2) (g2 . g1)

public export
twistedUnit : {state : Type} -> Twisted state
twistedUnit = MkTwisted id id

||| Associativity of twisted composition, stated pointwise because Idris does not
||| assume function extensionality.
public export
0 twistedAssociativeForward :
  (x, y, z : Twisted state) ->
  Pointwise (forward (twisted (twisted x y) z))
            (forward (twisted x (twisted y z)))
twistedAssociativeForward (MkTwisted f1 g1) (MkTwisted f2 g2) (MkTwisted f3 g3) x = Refl

public export
0 twistedAssociativeBackward :
  (x, y, z : Twisted state) ->
  Pointwise (backward (twisted (twisted x y) z))
            (backward (twisted x (twisted y z)))
twistedAssociativeBackward (MkTwisted f1 g1) (MkTwisted f2 g2) (MkTwisted f3 g3) x = Refl

public export
0 twistedLeftUnitForward : (p : Twisted state) ->
  Pointwise (forward (twisted (twistedUnit {state}) p)) (forward p)
twistedLeftUnitForward (MkTwisted f g) x = Refl

public export
0 twistedLeftUnitBackward : (p : Twisted state) ->
  Pointwise (backward (twisted (twistedUnit {state}) p)) (backward p)
twistedLeftUnitBackward (MkTwisted f g) x = Refl

public export
0 twistedRightUnitForward : (p : Twisted state) ->
  Pointwise (forward (twisted p (twistedUnit {state}))) (forward p)
twistedRightUnitForward (MkTwisted f g) x = Refl

public export
0 twistedRightUnitBackward : (p : Twisted state) ->
  Pointwise (backward (twisted p (twistedUnit {state}))) (backward p)
twistedRightUnitBackward (MkTwisted f g) x = Refl

||| Definition 2: effect context dGamma = Gamma x (Gamma -> Gamma).
public export
record EffectContext (state : Type) where
  constructor MkEffectContext
  current : state
  accumulator : state -> state

||| Definition 3: lift a forward/inverse pair and track the inverse.
public export
track : Twisted state -> EffectContext state -> EffectContext state
track (MkTwisted f g) (MkEffectContext x phi) =
  MkEffectContext (f x) (phi . g)

||| Theorem 4: track projects to the original forward map.
public export
0 trackProjection : (p : Twisted state) -> (ctx : EffectContext state) ->
  current (track p ctx) = forward p (current ctx)
trackProjection (MkTwisted f g) (MkEffectContext x phi) = Refl

||| Theorem 5(1), pointwise on both observable fields.
public export
0 trackUnitCurrent : (ctx : EffectContext state) ->
  current (track (twistedUnit {state}) ctx) = current ctx
trackUnitCurrent (MkEffectContext x phi) = Refl

public export
0 trackUnitAccumulator : (ctx : EffectContext state) ->
  Pointwise (accumulator (track (twistedUnit {state}) ctx)) (accumulator ctx)
trackUnitAccumulator (MkEffectContext x phi) probe = Refl

||| Theorem 5(2): track preserves twisted multiplication, pointwise.
public export
0 trackCompositionCurrent :
  (p, q : Twisted state) -> (ctx : EffectContext state) ->
  current (track (twisted p q) ctx) = current (track p (track q ctx))
trackCompositionCurrent (MkTwisted f1 g1) (MkTwisted f2 g2) (MkEffectContext x phi) = Refl

public export
0 trackCompositionAccumulator :
  (p, q : Twisted state) -> (ctx : EffectContext state) ->
  Pointwise (accumulator (track (twisted p q) ctx))
            (accumulator (track p (track q ctx)))
trackCompositionAccumulator (MkTwisted f1 g1) (MkTwisted f2 g2) (MkEffectContext x phi) probe = Refl

||| Definition 6: recover the state and reset the accumulator.
public export
recover : EffectContext state -> EffectContext state
recover (MkEffectContext x phi) = MkEffectContext (phi x) id

||| Theorem 7: a locally valid inverse preserves recovery exactly.
public export
0 recoverTracked : (p : Twisted state) -> (ctx : EffectContext state) ->
  backward p (forward p (current ctx)) = current ctx ->
  recover (track p ctx) = recover ctx
recoverTracked (MkTwisted f g) (MkEffectContext x phi) prf =
  rewrite prf in Refl

||| Definition 8: runtime part of an effect function.
public export
EffFn : Type -> Type
EffFn state = state -> (state, state -> state)

||| Definition 8: a witnessed effect function. The witness is erased.
public export
record EffStar (state : Type) where
  constructor MkEffStar
  runEff : EffFn state
  0 witnessed : (x : state) -> snd (runEff x) (fst (runEff x)) = x

||| Specialize a witness after exposing the pair returned at a state.
public export
0 witnessedAt : (e : EffStar state) -> (x, y : state) ->
  (undo : state -> state) -> runEff e x = (y, undo) -> undo y = x
witnessedAt e x y undo returned =
  replace {p = \pair => snd pair (fst pair) = x} returned (witnessed e x)

||| Apply a witnessed effect and expose a state-indexed undo token.
public export
applyStar : (e : EffStar state) -> (before : state) -> Applied before
applyStar e before with (runEff e before) proof returned
  applyStar e before | (after, undo) =
    MkApplied after (MkUndo undo (witnessedAt e before after undo returned))

||| Definition 9: effect composition; the left effect runs after the right.
public export
diamond : EffFn state -> EffFn state -> EffFn state
diamond f g x =
  let (y, undoG) = g x
      (z, undoF) = f y
   in (z, undoG . undoF)

public export
eta : {state : Type} -> EffFn state
eta x = (x, id)

||| Theorem 10(1): pointwise monoid laws for effect composition.
public export
0 diamondAssociativeState : (f, g, h : EffFn state) -> (x : state) ->
  fst (diamond (diamond f g) h x) = fst (diamond f (diamond g h) x)
diamondAssociativeState f g h x with (h x)
  diamondAssociativeState f g h x | (a, ha) with (g a)
    diamondAssociativeState f g h x | (a, ha) | (b, gb) with (f b)
      diamondAssociativeState f g h x | (a, ha) | (b, gb) | (c, fc) = Refl

public export
0 diamondAssociativeUndo : (f, g, h : EffFn state) -> (x, probe : state) ->
  snd (diamond (diamond f g) h x) probe =
  snd (diamond f (diamond g h) x) probe
diamondAssociativeUndo f g h x probe with (h x)
  diamondAssociativeUndo f g h x probe | (a, ha) with (g a)
    diamondAssociativeUndo f g h x probe | (a, ha) | (b, gb) with (f b)
      diamondAssociativeUndo f g h x probe | (a, ha) | (b, gb) | (c, fc) = Refl

public export
0 diamondLeftUnitState : (e : EffFn state) -> (x : state) ->
  fst (diamond (eta {state}) e x) = fst (e x)
diamondLeftUnitState e x with (e x)
  diamondLeftUnitState e x | (y, undo) = Refl

public export
0 diamondLeftUnitUndo : (e : EffFn state) -> (x, probe : state) ->
  snd (diamond (eta {state}) e x) probe = snd (e x) probe
diamondLeftUnitUndo e x probe with (e x)
  diamondLeftUnitUndo e x probe | (y, undo) = Refl

public export
0 diamondRightUnitState : (e : EffFn state) -> (x : state) ->
  fst (diamond e (eta {state}) x) = fst (e x)
diamondRightUnitState e x with (e x)
  diamondRightUnitState e x | (y, undo) = Refl

public export
0 diamondRightUnitUndo : (e : EffFn state) -> (x, probe : state) ->
  snd (diamond e (eta {state}) x) probe = snd (e x) probe
diamondRightUnitUndo e x probe with (e x)
  diamondRightUnitUndo e x probe | (y, undo) = Refl

||| Theorem 11(1): witnessing survives effect composition.
public export
diamondStar : EffStar state -> EffStar state -> EffStar state
diamondStar f g = MkEffStar (diamond (runEff f) (runEff g)) witnessComposite
  where
  0 witnessComposite : (x : state) ->
    snd (diamond (runEff f) (runEff g) x)
        (fst (diamond (runEff f) (runEff g) x)) = x
  witnessComposite x with (runEff g x) proof rightReturned
    witnessComposite x | (y, undoG) with (runEff f y) proof leftReturned
      witnessComposite x | (y, undoG) | (z, undoF) =
        trans (cong undoG (witnessedAt f y z undoF leftReturned))
              (witnessedAt g x y undoG rightReturned)

public export
etaStar : {state : Type} -> EffStar state
etaStar = MkEffStar (eta {state}) (\_ => Refl)

||| A twisted pair whose inverse is uniform at every state.
public export
UniformInverse : {state : Type} -> Twisted state -> Type
UniformInverse {state} p = (x : state) -> backward p (forward p x) = x

||| Theorem 11(2): a uniform inverse induces a witnessed effect function.
public export
fromTwistedStar : (p : Twisted state) -> (0 law : UniformInverse p) -> EffStar state
fromTwistedStar (MkTwisted f g) law = MkEffStar (\x => (f x, g)) law

||| Definition 12: lift an effect function one level up the effect-context tower.
public export
effect : EffFn state -> EffFn (EffectContext state)
effect e (MkEffectContext x phi) =
  let (y, undo) = e x
      f = fst . e
   in (MkEffectContext y (phi . undo), track (MkTwisted undo f))

||| Theorem 13, forward-state component, pointwise.
public export
0 effectPreservesDiamondCurrent :
  (f, g : EffFn state) -> (ctx : EffectContext state) ->
  current (fst (diamond (effect f) (effect g) ctx)) =
  current (fst (effect (diamond f g) ctx))
effectPreservesDiamondCurrent f g (MkEffectContext x phi) with (g x)
  effectPreservesDiamondCurrent f g (MkEffectContext x phi) | (y, gy) with (f y)
    effectPreservesDiamondCurrent f g (MkEffectContext x phi) | (y, gy) | (z, fz) = Refl

public export
0 effectPreservesDiamondAccumulator :
  (f, g : EffFn state) -> (ctx : EffectContext state) -> (probe : state) ->
  accumulator (fst (diamond (effect f) (effect g) ctx)) probe =
  accumulator (fst (effect (diamond f g) ctx)) probe
effectPreservesDiamondAccumulator f g (MkEffectContext x phi) probe with (g x)
  effectPreservesDiamondAccumulator f g (MkEffectContext x phi) probe | (y, gy) with (f y)
    effectPreservesDiamondAccumulator f g (MkEffectContext x phi) probe | (y, gy) | (z, fz) = Refl

public export
0 effectPreservesDiamondInverseCurrent :
  (f, g : EffFn state) -> (ctx, probe : EffectContext state) ->
  current (snd (diamond (effect f) (effect g) ctx) probe) =
  current (snd (effect (diamond f g) ctx) probe)
effectPreservesDiamondInverseCurrent f g (MkEffectContext x phi)
  (MkEffectContext probe psi) with (g x)
    effectPreservesDiamondInverseCurrent f g (MkEffectContext x phi)
      (MkEffectContext probe psi) | (y, gy) with (f y)
        effectPreservesDiamondInverseCurrent f g (MkEffectContext x phi)
          (MkEffectContext probe psi) | (y, gy) | (z, fz) = Refl

public export
0 effectPreservesDiamondInverseAccumulator :
  (f, g : EffFn state) -> (ctx, probe : EffectContext state) -> (x : state) ->
  accumulator (snd (diamond (effect f) (effect g) ctx) probe) x =
  accumulator (snd (effect (diamond f g) ctx) probe) x
effectPreservesDiamondInverseAccumulator f g (MkEffectContext original phi)
  (MkEffectContext probe psi) x with (g original)
    effectPreservesDiamondInverseAccumulator f g (MkEffectContext original phi)
      (MkEffectContext probe psi) x | (middle, undoG) with (f middle)
        effectPreservesDiamondInverseAccumulator f g (MkEffectContext original phi)
          (MkEffectContext probe psi) x | (middle, undoG) | (final, undoF) with (g x)
            effectPreservesDiamondInverseAccumulator f g (MkEffectContext original phi)
              (MkEffectContext probe psi) x | (middle, undoG) | (final, undoF) |
                (probeMiddle, probeUndoG) with (f probeMiddle)
                  effectPreservesDiamondInverseAccumulator f g (MkEffectContext original phi)
                    (MkEffectContext probe psi) x | (middle, undoG) | (final, undoF) |
                      (probeMiddle, probeUndoG) | (probeFinal, probeUndoF) = Refl

||| Theorem 14(1): the lifted forward map projects to the original one.
public export
0 effectForwardProjection : (e : EffFn state) -> (ctx : EffectContext state) ->
  current (fst (effect e ctx)) = fst (e (current ctx))
effectForwardProjection e (MkEffectContext x phi) with (e x)
  effectForwardProjection e (MkEffectContext x phi) | (_, _) = Refl

||| Theorem 14(2): the lifted inverse projects to the yielded inverse.
public export
0 effectInverseProjection :
  (e : EffFn state) -> (ctx, probe : EffectContext state) ->
  current (snd (effect e ctx) probe) = snd (e (current ctx)) (current probe)
effectInverseProjection e (MkEffectContext x phi) (MkEffectContext probe psi) with (e x)
  effectInverseProjection e (MkEffectContext x phi) (MkEffectContext probe psi) | (y, undo) = Refl

||| Theorem 15: the lifted inverse recovers the underlying state exactly.
public export
0 effectUndoCurrent : (e : EffStar state) -> (ctx : EffectContext state) ->
  let result = effect (runEff e) ctx
   in current (snd result (fst result)) = current ctx
effectUndoCurrent e (MkEffectContext x phi) with (runEff e x) proof returned
  effectUndoCurrent e (MkEffectContext x phi) | (y, undo) =
    witnessedAt e x y undo returned

||| Theorem 15's soundness-invariant conclusion.
public export
0 effectUndoRecovery : (e : EffStar state) -> (ctx : EffectContext state) ->
  recover (snd (effect (runEff e) ctx) (fst (effect (runEff e) ctx))) = recover ctx
effectUndoRecovery e (MkEffectContext x phi) with (runEff e x) proof returned
  effectUndoRecovery e (MkEffectContext x phi) | (y, undo) =
    let w = witnessedAt e x y undo returned
        inner = trans (cong (fst . runEff e) w) (cong fst returned)
        restored = trans (cong undo inner) w
     in cong (\v => MkEffectContext v id) (cong phi restored)

||| A finite LIFO stack of effects. Its accumulator is executable and its proof
||| records Theorem 16 for the sequence.
public export
record EffectStack (state : Type) (current : state) (initial : state) where
  constructor MkEffectStack
  stackAccumulator : state -> state
  0 stackSound : stackAccumulator current = initial

public export
emptyStack : (x : state) -> EffectStack state x x
emptyStack x = MkEffectStack id Refl

public export
pushStack : {state : Type} -> {current, initial : state} -> (e : EffStar state) ->
  EffectStack state current initial ->
  (next ** EffectStack state next initial)
pushStack e (MkEffectStack acc sound) with (runEff e current) proof returned
  pushStack e (MkEffectStack acc sound) | (next, undo) =
    (next ** MkEffectStack (acc . undo)
      (trans (cong acc (witnessedAt e current next undo returned)) sound))

||| Definition 17: generators and the generated transformation monoid M(e).
public export
data Generator : (state : Type) -> EffFn state -> Type where
  ForwardGenerator : Generator state e
  YieldedGenerator : (origin : state) -> Generator state e

public export
generatorMap : {state : Type} -> {e : EffFn state} -> Generator state e -> state -> state
generatorMap {e} ForwardGenerator = fst . e
generatorMap {e} (YieldedGenerator origin) = snd (e origin)

public export
data Transformation : (state : Type) -> EffFn state -> Type where
  IdentityT : Transformation state e
  GeneratorT : Generator state e -> Transformation state e
  ComposeT : Transformation state e -> Transformation state e -> Transformation state e

public export
runTransformation : {state : Type} -> {e : EffFn state} -> Transformation state e -> state -> state
runTransformation IdentityT = id
runTransformation (GeneratorT g) = generatorMap g
runTransformation (ComposeT f g) = runTransformation f . runTransformation g

||| Lemma 18(1): commutation of generated monoids follows from commutation of
||| their generators.
public export
GeneratorsCommute : {state : Type} -> (left, right : EffFn state) -> Type
GeneratorsCommute {state} left right =
  (f : Generator state left) -> (g : Generator state right) -> (x : state) ->
  generatorMap f (generatorMap g x) = generatorMap g (generatorMap f x)

public export
0 generatorsSettleCommutation : GeneratorsCommute left right ->
  (f : Transformation state left) -> (g : Transformation state right) ->
  (x : state) ->
  runTransformation f (runTransformation g x) =
  runTransformation g (runTransformation f x)
generatorsSettleCommutation generators IdentityT g x = Refl
generatorsSettleCommutation generators (GeneratorT f) IdentityT x = Refl
generatorsSettleCommutation generators (GeneratorT f) (GeneratorT g) x =
  generators f g x
generatorsSettleCommutation generators (GeneratorT f) (ComposeT g h) x =
  trans (generatorsSettleCommutation generators (GeneratorT f) g
           (runTransformation h x))
        (cong (runTransformation g)
          (generatorsSettleCommutation generators (GeneratorT f) h x))
generatorsSettleCommutation generators (ComposeT f h) g x =
  trans (cong (runTransformation f)
          (generatorsSettleCommutation generators h g x))
        (generatorsSettleCommutation generators f g (runTransformation h x))

||| The submonoid generated by two transformation monoids.
public export
data JointTransformation : (state : Type) -> EffFn state -> EffFn state -> Type where
  JointIdentity : JointTransformation state left right
  JointLeft : Transformation state left -> JointTransformation state left right
  JointRight : Transformation state right -> JointTransformation state left right
  JointCompose : JointTransformation state left right ->
                 JointTransformation state left right ->
                 JointTransformation state left right

public export
runJoint : {state : Type} -> {left, right : EffFn state} ->
  JointTransformation state left right -> state -> state
runJoint JointIdentity = id
runJoint (JointLeft t) = runTransformation t
runJoint (JointRight t) = runTransformation t
runJoint (JointCompose f g) = runJoint f . runJoint g

public export
0 diamondForwardPointwise : (left, right : EffFn state) -> (x : state) ->
  fst (diamond left right x) = fst (left (fst (right x)))
diamondForwardPointwise left right x with (right x) proof rightReturned
  diamondForwardPointwise left right x | (middle, undoRight) with (left middle) proof leftReturned
    diamondForwardPointwise left right x | (middle, undoRight) | (final, undoLeft) = Refl

public export
0 diamondInversePointwise : (left, right : EffFn state) ->
  (origin, probe : state) ->
  snd (diamond left right origin) probe =
  snd (right origin) (snd (left (fst (right origin))) probe)
diamondInversePointwise left right origin probe with (right origin) proof rightReturned
  diamondInversePointwise left right origin probe | (middle, undoRight) with (left middle) proof leftReturned
    diamondInversePointwise left right origin probe |
      (middle, undoRight) | (final, undoLeft) = Refl

||| Lemma 18(2), precisely stated as generated-submonoid inclusion.
public export
diamondDoesNotEnlarge : (state : Type) -> Type
diamondDoesNotEnlarge state =
  (left, right : EffFn state) ->
  (t : Transformation state (diamond left right)) ->
  (joint : JointTransformation state left right **
    Pointwise (runTransformation t) (runJoint joint))

public export
0 diamondDoesNotEnlargeProof : (state : Type) -> diamondDoesNotEnlarge state
diamondDoesNotEnlargeProof state left right IdentityT =
  (JointIdentity ** \x => Refl)
diamondDoesNotEnlargeProof state left right
  (GeneratorT ForwardGenerator) =
    (JointCompose
      (JointLeft (GeneratorT ForwardGenerator))
      (JointRight (GeneratorT ForwardGenerator)) **
      diamondForwardPointwise left right)
diamondDoesNotEnlargeProof state left right
  (GeneratorT (YieldedGenerator origin)) =
    (JointCompose
      (JointRight (GeneratorT (YieldedGenerator origin)))
      (JointLeft
        (GeneratorT (YieldedGenerator (fst (right origin))))) **
      diamondInversePointwise left right origin)
diamondDoesNotEnlargeProof state left right (ComposeT first second) =
  let (jointFirst ** firstEqual) =
        diamondDoesNotEnlargeProof state left right first
      (jointSecond ** secondEqual) =
        diamondDoesNotEnlargeProof state left right second
   in (JointCompose jointFirst jointSecond ** \x =>
        trans (cong (runTransformation first) (secondEqual x))
              (firstEqual (runJoint jointSecond x)))

||| Definition 19, without quotienting: all generated maps commute and yielded
||| inverses are stable under every foreign generated transformation.
public export
record Independent {state : Type} (left, right : EffFn state) where
  constructor MkIndependent
  0 transformationsCommute :
    (f : Transformation state left) -> (g : Transformation state right) -> (x : state) ->
    runTransformation f (runTransformation g x) =
    runTransformation g (runTransformation f x)
  0 leftInverseStable :
    (g : Transformation state right) -> (origin, probe : state) ->
    snd (left (runTransformation g origin)) probe = snd (left origin) probe
  0 rightInverseStable :
    (f : Transformation state left) -> (origin, probe : state) ->
    snd (right (runTransformation f origin)) probe = snd (right origin) probe

||| A directly useful two-effect instance of Theorem 20: undoing the first
||| effect while the second remains reaches the state obtained by omitting it.
public export
0 withdrawFirstOfTwo :
  (left, right : EffStar state) ->
  Independent (runEff left) (runEff right) ->
  (x : state) ->
  let (y, undoL) = runEff left x
      (z, undoR) = runEff right y
   in undoL z = fst (runEff right x)
withdrawFirstOfTwo left right ind x with (runEff left x) proof leftReturned
  withdrawFirstOfTwo left right ind x | (y, undoL) with (runEff right y) proof rightReturned
    withdrawFirstOfTwo left right ind x | (y, undoL) | (z, undoR) =
      let rawCommute = transformationsCommute ind
                         (GeneratorT (YieldedGenerator x))
                         (GeneratorT ForwardGenerator) y
          commute = replace
            {p = \pair => snd pair (fst (runEff right y)) =
                            fst (runEff right (snd pair y))}
            leftReturned rawCommute
          base = trans commute
                   (cong (fst . runEff right)
                     (witnessedAt left x y undoL leftReturned))
       in replace {p = \pair => undoL (fst pair) = fst (runEff right x)}
                  rightReturned base

||| Apply a finite family in list order.
public export
applyAll : List (EffStar state) -> state -> state
applyAll [] x = x
applyAll (e :: rest) x = applyAll rest (fst (runEff e x))

||| Collect exactly the inverses yielded at the states where applications run.
public export
collectUndos : List (EffStar state) -> state -> List (state -> state)
collectUndos [] x = []
collectUndos (e :: rest) x =
  snd (runEff e x) :: collectUndos rest (fst (runEff e x))

public export
runUndoList : List (state -> state) -> state -> state
runUndoList [] x = x
runUndoList (undo :: rest) x = runUndoList rest (undo x)

||| Pairwise independence of a finite effect family (Definition 19).
public export
data IndependentWith : EffStar state -> List (EffStar state) -> Type where
  IndependentWithNil : IndependentWith e []
  IndependentWithCons : Independent (runEff e) (runEff f) ->
                        IndependentWith e rest -> IndependentWith e (f :: rest)

public export
data PairwiseIndependent : List (EffStar state) -> Type where
  PairwiseNil : PairwiseIndependent []
  PairwiseCons : IndependentWith e rest -> PairwiseIndependent rest ->
                 PairwiseIndependent (e :: rest)

public export
pairwiseTail : PairwiseIndependent (e :: rest) -> PairwiseIndependent rest
pairwiseTail (PairwiseCons _ tail) = tail

public export
selectedIndependentLater : (earlier : List (EffStar state)) ->
  PairwiseIndependent (earlier ++ selected :: later) ->
  IndependentWith selected later
selectedIndependentLater [] (PairwiseCons selectedWith laterPairwise) = selectedWith
selectedIndependentLater (_ :: earlier) (PairwiseCons _ tailPairwise) =
  selectedIndependentLater earlier tailPairwise

||| Pairwise commutation of a concrete list of yielded inverse maps.
public export
Commute : {state : Type} -> (state -> state) -> (state -> state) -> Type
Commute {state} f g = (x : state) -> f (g x) = g (f x)

public export
data CommutesWith : (state -> state) -> List (state -> state) -> Type where
  CommutesWithNil : CommutesWith f []
  CommutesWithCons : Commute f g -> CommutesWith f rest ->
                     CommutesWith f (g :: rest)

public export
data PairwiseCommuting : List (state -> state) -> Type where
  CommutingNil : PairwiseCommuting []
  CommutingCons : CommutesWith f rest -> PairwiseCommuting rest ->
                  PairwiseCommuting (f :: rest)

public export
0 fixedYieldedUndoCommutes :
  (selected : EffStar state) -> (selectedOrigin : state) ->
  (others : List (EffStar state)) -> IndependentWith selected others ->
  (othersStart : state) ->
  CommutesWith (snd (runEff selected selectedOrigin))
               (collectUndos others othersStart)
fixedYieldedUndoCommutes selected selectedOrigin [] IndependentWithNil othersStart =
  CommutesWithNil
fixedYieldedUndoCommutes selected selectedOrigin (other :: rest)
  (IndependentWithCons independent selectedRest) othersStart =
    CommutesWithCons
      (transformationsCommute independent
        (GeneratorT (YieldedGenerator selectedOrigin))
        (GeneratorT (YieldedGenerator othersStart)))
      (fixedYieldedUndoCommutes selected selectedOrigin rest selectedRest
        (fst (runEff other othersStart)))

public export
0 collectedUndosCommute : (effects : List (EffStar state)) ->
  PairwiseIndependent effects -> (start : state) ->
  PairwiseCommuting (collectUndos effects start)
collectedUndosCommute [] PairwiseNil start = CommutingNil
collectedUndosCommute (e :: rest) (PairwiseCons withRest restPairwise) start =
  CommutingCons
    (fixedYieldedUndoCommutes e start rest withRest (fst (runEff e start)))
    (collectedUndosCommute rest restPairwise (fst (runEff e start)))

||| Pointwise equality for aligned lists of transformations.
public export
data TransformationListsEqual : List (state -> state) ->
                                List (state -> state) -> Type where
  TransformationsNil : TransformationListsEqual [] []
  TransformationsCons : Pointwise f g -> TransformationListsEqual fs gs ->
                        TransformationListsEqual (f :: fs) (g :: gs)

||| The inductive core of Theorem 20: move one selected contribution through
||| an arbitrary independent suffix, and preserve all suffix inverses.
public export
0 withdrawAcross : (selected : EffStar state) ->
  (later : List (EffStar state)) -> IndependentWith selected later ->
  (start : state) ->
  (snd (runEff selected start)
       (applyAll later (fst (runEff selected start))) = applyAll later start,
   TransformationListsEqual
     (collectUndos later (fst (runEff selected start)))
     (collectUndos later start))
withdrawAcross selected [] IndependentWithNil start =
  (witnessed selected start, TransformationsNil)
withdrawAcross selected (other :: rest)
  (IndependentWithCons independent selectedRest) start =
  let recursive = withdrawAcross selected rest selectedRest
                    (fst (runEff other start))
      commutation = transformationsCommute independent
        (GeneratorT ForwardGenerator) (GeneratorT ForwardGenerator) start
      restoredOriginal =
        trans (cong (snd (runEff selected start))
                (cong (applyAll rest) (sym commutation)))
          (trans
            (sym (leftInverseStable independent
              (GeneratorT ForwardGenerator) start
              (applyAll rest
                (fst (runEff selected (fst (runEff other start)))))))
            (fst recursive))
      alignedRest = replace
        {p = \s => TransformationListsEqual
          (collectUndos rest s)
          (collectUndos rest (fst (runEff other start)))}
        commutation (snd recursive)
   in (restoredOriginal,
       TransformationsCons
         (rightInverseStable independent
           (GeneratorT ForwardGenerator) start)
         alignedRest)

||| Apply/collect normalization after a prefix.
public export
0 applyAllAppend : (earlier, later : List (EffStar state)) -> (start : state) ->
  applyAll (earlier ++ later) start = applyAll later (applyAll earlier start)
applyAllAppend [] later start = Refl
applyAllAppend (e :: earlier) later start =
  applyAllAppend earlier later (fst (runEff e start))

public export
0 collectAfterPrefix : (earlier, later : List (EffStar state)) ->
  (start : state) ->
  drop (length earlier) (collectUndos (earlier ++ later) start) =
  collectUndos later (applyAll earlier start)
collectAfterPrefix [] later start = Refl
collectAfterPrefix (e :: earlier) later start =
  collectAfterPrefix earlier later (fst (runEff e start))

public export
0 collectAfterSelected : (earlier : List (EffStar state)) ->
  (selected : EffStar state) -> (later : List (EffStar state)) ->
  (start : state) ->
  drop (length earlier + 1)
       (collectUndos (earlier ++ selected :: later) start) =
  collectUndos later (fst (runEff selected (applyAll earlier start)))
collectAfterSelected [] selected later start = Refl
collectAfterSelected (e :: earlier) selected later start =
  collectAfterSelected earlier selected later (fst (runEff e start))

||| Theorem 20, including both conclusions, stated for a selected effect via a
||| prefix/suffix decomposition. The first equality withdraws the selected
||| contribution; the aligned-list relation says later effects yield the same
||| inverses after omission.
public export
outOfLIFOTheorem : (state : Type) -> Type
outOfLIFOTheorem state =
  (earlier : List (EffStar state)) -> (later : List (EffStar state)) ->
  (selected : EffStar state) ->
  (start : state) ->
  PairwiseIndependent (earlier ++ selected :: later) ->
  (snd (runEff selected (applyAll earlier start))
       (applyAll (earlier ++ selected :: later) start) =
       applyAll (earlier ++ later) start,
   TransformationListsEqual
     (drop (length earlier + 1)
       (collectUndos (earlier ++ selected :: later) start))
     (drop (length earlier)
       (collectUndos (earlier ++ later) start)))

public export
0 outOfLIFOProof : (state : Type) -> outOfLIFOTheorem state
outOfLIFOProof state earlier later selected start pairwise =
  let selectedWithLater = selectedIndependentLater earlier pairwise
      core = withdrawAcross selected later selectedWithLater
               (applyAll earlier start)
      recovered = fst core
      aligned = snd core
      recoveredAtTrace =
        replace
          {p = \completeState =>
            snd (runEff selected (applyAll earlier start)) completeState =
              applyAll later (applyAll earlier start)}
          (sym (applyAllAppend earlier (selected :: later) start))
          recovered
      recoveredAtBothTraces =
        replace
          {p = \omittedState =>
            snd (runEff selected (applyAll earlier start))
              (applyAll (earlier ++ selected :: later) start) = omittedState}
          (sym (applyAllAppend earlier later start))
          recoveredAtTrace
      alignedAtOriginal = replace
        {p = \original => TransformationListsEqual original
          (collectUndos later (applyAll earlier start))}
        (sym (collectAfterSelected earlier selected later start)) aligned
      alignedAtBoth = replace
        {p = \omitted => TransformationListsEqual
          (drop (length earlier + 1)
            (collectUndos (earlier ++ selected :: later) start)) omitted}
        (sym (collectAfterPrefix earlier later start)) alignedAtOriginal
   in (recoveredAtBothTraces, alignedAtBoth)

||| A standard adjacent-swap presentation of finite permutations.
public export
data AdjacentSwap : List a -> List a -> Type where
  SwapHere : AdjacentSwap (x :: y :: rest) (y :: x :: rest)
  SwapThere : AdjacentSwap xs ys -> AdjacentSwap (z :: xs) (z :: ys)

public export
data Permutation : List a -> List a -> Type where
  PermutationDone : Permutation xs xs
  PermutationStep : AdjacentSwap xs ys -> Permutation ys zs -> Permutation xs zs

public export
permutationCompose : Permutation xs ys -> Permutation ys zs -> Permutation xs zs
permutationCompose PermutationDone second = second
permutationCompose (PermutationStep step rest) second =
  PermutationStep step (permutationCompose rest second)

public export
liftPermutation : (head : a) -> Permutation xs ys ->
  Permutation (head :: xs) (head :: ys)
liftPermutation head PermutationDone = PermutationDone
liftPermutation head (PermutationStep step rest) =
  PermutationStep (SwapThere step) (liftPermutation head rest)

public export
0 commuteSym : Commute f g -> Commute g f
commuteSym commute x = sym (commute x)

public export
0 commutesWithSwap : CommutesWith f xs -> AdjacentSwap xs ys ->
  CommutesWith f ys
commutesWithSwap
  (CommutesWithCons first (CommutesWithCons second rest)) SwapHere =
    CommutesWithCons second (CommutesWithCons first rest)
commutesWithSwap (CommutesWithCons first rest) (SwapThere step) =
  CommutesWithCons first (commutesWithSwap rest step)

public export
0 swapPreservesCommuting : PairwiseCommuting xs -> AdjacentSwap xs ys ->
  PairwiseCommuting ys
swapPreservesCommuting
  {xs = left :: right :: rest} {ys = right :: left :: rest}
  (CommutingCons
    (CommutesWithCons first headWithRest)
    (CommutingCons secondWithRest restPairwise)) SwapHere =
      CommutingCons
        (CommutesWithCons (\probe => sym (first probe)) secondWithRest)
        (CommutingCons headWithRest restPairwise)
swapPreservesCommuting (CommutingCons headWith tailPairwise)
  (SwapThere step) =
    CommutingCons (commutesWithSwap headWith step)
                  (swapPreservesCommuting tailPairwise step)

public export
0 permutationPreservesCommuting : PairwiseCommuting xs -> Permutation xs ys ->
  PairwiseCommuting ys
permutationPreservesCommuting pairwise PermutationDone = pairwise
permutationPreservesCommuting pairwise (PermutationStep step rest) =
  permutationPreservesCommuting (swapPreservesCommuting pairwise step) rest

public export
0 swapRunEqual : PairwiseCommuting xs -> AdjacentSwap xs ys ->
  (start : state) -> runUndoList xs start = runUndoList ys start
swapRunEqual
  (CommutingCons (CommutesWithCons first _) _) SwapHere start =
    cong (runUndoList _) (sym (first start))
swapRunEqual (CommutingCons _ tailPairwise) (SwapThere step) start =
  swapRunEqual tailPairwise step _

public export
0 permutationRunEqual : PairwiseCommuting xs -> Permutation xs ys ->
  (start : state) -> runUndoList xs start = runUndoList ys start
permutationRunEqual pairwise PermutationDone start = Refl
permutationRunEqual pairwise (PermutationStep step rest) start =
  trans (swapRunEqual pairwise step start)
        (permutationRunEqual (swapPreservesCommuting pairwise step) rest start)

public export
moveHeadToEnd : (head : a) -> (rest : List a) ->
  Permutation (head :: rest) (rest ++ [head])
moveHeadToEnd head [] = PermutationDone
moveHeadToEnd head (next :: rest) =
  PermutationStep SwapHere (liftPermutation next (moveHeadToEnd head rest))

public export
reverseList : List a -> List a
reverseList [] = []
reverseList (x :: xs) = reverseList xs ++ [x]

public export
reversePermutation : (xs : List a) -> Permutation xs (reverseList xs)
reversePermutation [] = PermutationDone
reversePermutation (x :: xs) =
  permutationCompose (liftPermutation x (reversePermutation xs))
                     (moveHeadToEnd x (reverseList xs))

public export
0 runUndoAppend : (first, second : List (state -> state)) -> (start : state) ->
  runUndoList (first ++ second) start =
  runUndoList second (runUndoList first start)
runUndoAppend [] second start = Refl
runUndoAppend (f :: first) second start = runUndoAppend first second (f start)

||| LIFO recovery needs no independence (Theorem 16), here specialized to the
||| concrete inverse list collected from a trace.
public export
0 reverseCollectedRecovery : (effects : List (EffStar state)) -> (start : state) ->
  runUndoList (reverseList (collectUndos effects start))
              (applyAll effects start) = start
reverseCollectedRecovery [] start = Refl
reverseCollectedRecovery (e :: rest) start with (runEff e start) proof returned
  reverseCollectedRecovery (e :: rest) start | (next, undo) =
    trans
      (runUndoAppend
        (reverseList (collectUndos rest next)) [undo]
        (applyAll rest next))
      (trans (cong undo (reverseCollectedRecovery rest next))
             (witnessedAt e start next undo returned))

||| Corollary 21, precisely stated: every permutation of the inverses yielded by
||| a pairwise-independent application trace recovers its initial state.
public export
anyPermutationRecovery : (state : Type) -> Type
anyPermutationRecovery state =
  (effects : List (EffStar state)) -> (start : state) ->
  PairwiseIndependent effects -> (order : List (state -> state)) ->
  Permutation (collectUndos effects start) order ->
  runUndoList order (applyAll effects start) = start

public export
0 anyPermutationRecoveryProof : (state : Type) -> anyPermutationRecovery state
anyPermutationRecoveryProof state effects start independent order permutation =
  let commuting = collectedUndosCommute effects independent start
      orderToOriginal = sym
        (permutationRunEqual commuting permutation (applyAll effects start))
      originalToReverse = permutationRunEqual commuting
        (reversePermutation (collectUndos effects start))
        (applyAll effects start)
   in trans orderToOriginal
        (trans originalToReverse (reverseCollectedRecovery effects start))
