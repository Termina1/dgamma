module DGamma.R6TwoIntermediateStatic

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Metatheory
import DGamma.CP5ConfluenceCrossTraceSpike
import Data.List.Elem
import Decidable.Equality

%default total

V : Nat -> Type
V _ = Unit

single : Nat -> CoeffectSpec Nat
single k = MkCoeffectSpec [k] (UniqueCons (\present => absurd present) UniqueNil)

lowerC : Component Nat V Unit String
lowerC = MkComponent emptySpec (single 0) []

middle1C : Component Nat V Unit String
middle1C = MkComponent (single 0) (single 1) []

middle2C : Component Nat V Unit String
middle2C = MkComponent (single 1) (single 2) []

alternateC : Component Nat V Unit String
alternateC = MkComponent emptySpec emptySpec []

upperC : Component Nat V Unit String
upperC = MkComponent (single 2) emptySpec []

lowerF : Fiber Nat Nat V Unit String
lowerF = MkFiber lowerC Root False emptyOwned (Active id EmptyView)

middle1F : Fiber Nat Nat V Unit String
middle1F = MkFiber middle1C Root True emptyOwned (Inactive Nothing)

middle2F : Fiber Nat Nat V Unit String
middle2F = MkFiber middle2C Root True emptyOwned (Inactive Nothing)

alternateF : Fiber Nat Nat V Unit String
alternateF = MkFiber alternateC Root False emptyOwned (Active id EmptyView)

upperF : Fiber Nat Nat V Unit String
upperF = MkFiber upperC Root False emptyOwned (Active id (ProviderView 3 EmptyView))

0 n0fresh : Not (Elem 0 (the (List Nat) [1,2,3,4]))
n0fresh Here impossible
n0fresh (There Here) impossible
n0fresh (There (There Here)) impossible
n0fresh (There (There (There Here))) impossible
n0fresh (There (There (There (There later)))) = absurd later

0 n1fresh : Not (Elem 1 (the (List Nat) [2,3,4]))
n1fresh Here impossible
n1fresh (There Here) impossible
n1fresh (There (There Here)) impossible
n1fresh (There (There (There later))) = absurd later

0 n2fresh : Not (Elem 2 (the (List Nat) [3,4]))
n2fresh Here impossible
n2fresh (There Here) impossible
n2fresh (There (There later)) = absurd later

0 n3fresh : Not (Elem 3 (the (List Nat) [4]))
n3fresh Here impossible
n3fresh (There later) = absurd later

leftRegistry : Registry Nat Nat V Unit String
leftRegistry = MkCoeffectContext
  [ Bind (the Nat 0) lowerF, Bind (the Nat 1) middle1F, Bind (the Nat 2) middle2F
  , Bind (the Nat 3) alternateF, Bind (the Nat 4) upperF ]
  (UniqueCons n0fresh (UniqueCons n1fresh (UniqueCons n2fresh
    (UniqueCons n3fresh (UniqueCons (\p => absurd p) UniqueNil)))))

0 n0freshRight : Not (Elem 0 (the (List Nat) [3,4]))
n0freshRight Here impossible
n0freshRight (There Here) impossible
n0freshRight (There (There later)) = absurd later

rightRegistry : Registry Nat Nat V Unit String
rightRegistry = MkCoeffectContext
  [Bind (the Nat 0) lowerF, Bind (the Nat 3) alternateF, Bind (the Nat 4) upperF]
  (UniqueCons n0freshRight
    (UniqueCons n3fresh (UniqueCons (\p => absurd p) UniqueNil)))

leftState : SystemState Nat Nat V Unit String
leftState = MkSystemState () leftRegistry

rightState : SystemState Nat Nat V Unit String
rightState = MkSystemState () rightRegistry

0 lowerToMiddle1 : SupportEdge (the (DecEq Nat) %search)
  DGamma.R6TwoIntermediateStatic.leftState 0 1
lowerToMiddle1 = SupportPrecedence
  (MkPrecedenceEdge 0 lowerF middle1F Refl Refl Here Here)

0 middle1ToMiddle2 : SupportEdge (the (DecEq Nat) %search)
  DGamma.R6TwoIntermediateStatic.leftState 1 2
middle1ToMiddle2 = SupportPrecedence
  (MkPrecedenceEdge 1 middle1F middle2F Refl Refl Here Here)

0 middle2ToUpper : SupportEdge (the (DecEq Nat) %search)
  DGamma.R6TwoIntermediateStatic.leftState 2 4
middle2ToUpper = SupportPrecedence
  (MkPrecedenceEdge 2 middle2F upperF Refl Refl Here Here)

0 twoUnsupportedIntermediatesPath : SupportPath (the (DecEq Nat) %search)
  DGamma.R6TwoIntermediateStatic.leftState 0 4
twoUnsupportedIntermediatesPath = SupportPathMore lowerToMiddle1
  (SupportPathMore middle1ToMiddle2 (SupportPathOne middle2ToUpper))

0 middle1Unsupported : isSupported @{the (DecEq Nat) %search}
  @{the (DecEq Nat) %search} 1 DGamma.R6TwoIntermediateStatic.leftState = False
middle1Unsupported = Refl

0 middle2Unsupported : isSupported @{the (DecEq Nat) %search}
  @{the (DecEq Nat) %search} 2 DGamma.R6TwoIntermediateStatic.leftState = False
middle2Unsupported = Refl

0 middle1AbsentRight : lookupFiber @{the (DecEq Nat) %search}
  {key = Nat} {value = V} {world = Unit} {error = String} 1
  (registry DGamma.R6TwoIntermediateStatic.rightState) = Nothing
middle1AbsentRight = Refl

0 middle2AbsentRight : lookupFiber @{the (DecEq Nat) %search}
  {key = Nat} {value = V} {world = Unit} {error = String} 2
  (registry DGamma.R6TwoIntermediateStatic.rightState) = Nothing
middle2AbsentRight = Refl

0 zeroNotThree : Not ((the Nat 0) = (the Nat 3))
zeroNotThree Refl impossible

0 zeroNotFour : Not ((the Nat 0) = (the Nat 4))
zeroNotFour Refl impossible

swapZeroThree : AdjacentActorOrderSwap Nat (the (List Nat) [0,3,4]) (the (List Nat) [3,0,4])
swapZeroThree = MkAdjacentActorOrderSwap [] (the Nat 0) (the Nat 3) [the Nat 4] Refl Refl zeroNotThree

swapZeroFour : AdjacentActorOrderSwap Nat (the (List Nat) [3,0,4]) (the (List Nat) [3,4,0])
swapZeroFour = MkAdjacentActorOrderSwap [the Nat 3] (the Nat 0) (the Nat 4) [] Refl Refl zeroNotFour

twoIntermediateActorTarget : CertifiedActorPermutation Nat (the (List Nat) [0,3,4]) (the (List Nat) [3,4,0])
twoIntermediateActorTarget = ActorPermutationStep swapZeroThree
  (ActorPermutationStep swapZeroFour ActorPermutationDone)
