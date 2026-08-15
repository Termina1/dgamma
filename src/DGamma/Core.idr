module DGamma.Core

%default total

||| Pointwise equality, used instead of assuming function extensionality.
public export
Pointwise : {a, b : Type} -> (a -> b) -> (a -> b) -> Type
Pointwise {a} f g = (x : a) -> f x = g x

||| An executable equivalence relation together with its erased laws.
public export
record Equivalence (a : Type) where
  constructor MkEquivalence
  relation : a -> a -> Type
  0 reflexive : (x : a) -> relation x x
  0 symmetric : {x, y : a} -> relation x y -> relation y x
  0 transitive : {x, y, z : a} -> relation x y -> relation y z -> relation x z

public export
EqEquivalence : {a : Type} -> Equivalence a
EqEquivalence = MkEquivalence (\x, y => x = y)
  (\_ => Refl)
  (\prf => case prf of Refl => Refl)
  (\left, right => case left of Refl => right)

||| A state-indexed undo handle. The function is runtime data; its law is erased.
public export
record Undo {state : Type} (after : state) (before : state) where
  constructor MkUndo
  runUndo : state -> state
  0 undoValid : runUndo after = before

||| A loaded handle carrying a composite recovery function.
public export
record Loaded {state : Type} (current : state) (initial : state) where
  constructor MkLoaded
  recoverWith : state -> state
  0 loadedValid : recoverWith current = initial

||| Package the result of a state-indexed operation with its undo token.
public export
record Applied {state : Type} (before : state) where
  constructor MkApplied
  after : state
  undo : Undo after before
