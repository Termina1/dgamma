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

||| Lemma 18(2), precisely stated as generated-submonoid inclusion.
public export
diamondDoesNotEnlarge : (state : Type) -> Type
diamondDoesNotEnlarge state =
  (left, right : EffFn state) ->
  (t : Transformation state (diamond left right)) ->
  (joint : JointTransformation state left right **
    Pointwise (runTransformation t) (runJoint joint))

||| TODO(proof): construct the embedding by induction on Transformation. The
||| statement is retained without a fabricated inhabitant; see NOTES.md.

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

||| Pointwise equality for aligned lists of transformations.
public export
data TransformationListsEqual : List (state -> state) ->
                                List (state -> state) -> Type where
  TransformationsNil : TransformationListsEqual [] []
  TransformationsCons : Pointwise f g -> TransformationListsEqual fs gs ->
                        TransformationListsEqual (f :: fs) (g :: gs)

||| Theorem 20, including both conclusions, stated for a selected effect via a
||| prefix/suffix decomposition. The first equality withdraws the selected
||| contribution; the aligned-list relation says later effects yield the same
||| inverses after omission.
||| TODO(proof): general induction over the prefix/suffix trace; the n=2 core
||| is proved by withdrawFirstOfTwo.
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

||| A standard adjacent-swap presentation of finite permutations.
public export
data Permutation : List a -> List a -> Type where
  PermutationRefl : Permutation xs xs
  PermutationCons : Permutation xs ys -> Permutation (x :: xs) (x :: ys)
  PermutationSwap : Permutation (x :: y :: rest) (y :: x :: rest)
  PermutationTrans : Permutation xs ys -> Permutation ys zs -> Permutation xs zs

||| Corollary 21, precisely stated: every permutation of the inverses yielded by
||| a pairwise-independent application trace recovers its initial state.
||| TODO(proof): induction on Permutation using Theorem 20.
public export
anyPermutationRecovery : (state : Type) -> Type
anyPermutationRecovery state =
  (effects : List (EffStar state)) -> (start : state) ->
  PairwiseIndependent effects -> (order : List (state -> state)) ->
  Permutation (collectUndos effects start) order ->
  runUndoList order (applyAll effects start) = start
