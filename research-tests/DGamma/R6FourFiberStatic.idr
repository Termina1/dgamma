module DGamma.R6FourFiberStatic

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Metatheory
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP4DeletionChildlessInvariant
import Data.List.Elem
import Decidable.Equality

%default total

data N = Lower | Middle | Alternate | Upper

data K = KA | KB

implementation DecEq N where
  decEq Lower Lower = Yes Refl
  decEq Lower Middle = No (\Refl impossible)
  decEq Lower Alternate = No (\Refl impossible)
  decEq Lower Upper = No (\Refl impossible)
  decEq Middle Lower = No (\Refl impossible)
  decEq Middle Middle = Yes Refl
  decEq Middle Alternate = No (\Refl impossible)
  decEq Middle Upper = No (\Refl impossible)
  decEq Alternate Lower = No (\Refl impossible)
  decEq Alternate Middle = No (\Refl impossible)
  decEq Alternate Alternate = Yes Refl
  decEq Alternate Upper = No (\Refl impossible)
  decEq Upper Lower = No (\Refl impossible)
  decEq Upper Middle = No (\Refl impossible)
  decEq Upper Alternate = No (\Refl impossible)
  decEq Upper Upper = Yes Refl

implementation DecEq K where
  decEq KA KA = Yes Refl
  decEq KA KB = No (\Refl impossible)
  decEq KB KA = No (\Refl impossible)
  decEq KB KB = Yes Refl

V : K -> Type
V _ = Unit

specA : CoeffectSpec K
specA = MkCoeffectSpec [KA] (UniqueCons (\present => absurd present) UniqueNil)

specB : CoeffectSpec K
specB = MkCoeffectSpec [KB] (UniqueCons (\present => absurd present) UniqueNil)

lowerComponent : Component K V Unit String
lowerComponent = MkComponent emptySpec specA []

middleComponent : Component K V Unit String
middleComponent = MkComponent specA specB []

alternateComponent : Component K V Unit String
alternateComponent = MkComponent emptySpec specB []

upperComponent : Component K V Unit String
upperComponent = MkComponent specB emptySpec []

lowerFiber : Fiber N K V Unit String
lowerFiber = MkFiber lowerComponent Root False emptyOwned (Active id EmptyView)

middleFiber : Fiber N K V Unit String
middleFiber = MkFiber middleComponent Root True emptyOwned (Inactive Nothing)

alternateFiber : Fiber N K V Unit String
alternateFiber = MkFiber alternateComponent Root False emptyOwned (Active id EmptyView)

upperFiber : Fiber N K V Unit String
upperFiber = MkFiber upperComponent Root False emptyOwned
  (Active id (ProviderView Alternate EmptyView))

0 lowerFresh : Not (Elem Lower [Middle, Alternate, Upper])
lowerFresh Here impossible
lowerFresh (There Here) impossible
lowerFresh (There (There Here)) impossible
lowerFresh (There (There (There later))) = absurd later

0 middleFresh : Not (Elem Middle [Alternate, Upper])
middleFresh Here impossible
middleFresh (There Here) impossible
middleFresh (There (There later)) = absurd later

0 alternateFresh : Not (Elem Alternate [Upper])
alternateFresh Here impossible
alternateFresh (There later) = absurd later

leftRegistry : Registry N K V Unit String
leftRegistry = MkCoeffectContext
  [Bind Lower lowerFiber, Bind Middle middleFiber,
   Bind Alternate alternateFiber, Bind Upper upperFiber]
  (UniqueCons lowerFresh
    (UniqueCons middleFresh
      (UniqueCons alternateFresh (UniqueCons (\present => absurd present) UniqueNil))))

0 lowerFreshRight : Not (Elem Lower [Alternate, Upper])
lowerFreshRight Here impossible
lowerFreshRight (There Here) impossible
lowerFreshRight (There (There later)) = absurd later

rightRegistry : Registry N K V Unit String
rightRegistry = MkCoeffectContext
  [Bind Lower lowerFiber, Bind Alternate alternateFiber, Bind Upper upperFiber]
  (UniqueCons lowerFreshRight
    (UniqueCons alternateFresh (UniqueCons (\present => absurd present) UniqueNil)))

leftState : SystemState N K V Unit String
leftState = MkSystemState () leftRegistry

rightState : SystemState N K V Unit String
rightState = MkSystemState () rightRegistry

0 lowerSupportedLeft : isSupported @{the (DecEq N) %search} @{the (DecEq K) %search} Lower DGamma.R6FourFiberStatic.leftState = True
lowerSupportedLeft = Refl

0 upperSupportedLeft : isSupported @{the (DecEq N) %search} @{the (DecEq K) %search} Upper DGamma.R6FourFiberStatic.leftState = True
upperSupportedLeft = Refl

0 middleUnsupportedLeft : isSupported @{the (DecEq N) %search} @{the (DecEq K) %search} Middle DGamma.R6FourFiberStatic.leftState = False
middleUnsupportedLeft = Refl

0 lowerSupportedRight : isSupported @{the (DecEq N) %search} @{the (DecEq K) %search} Lower DGamma.R6FourFiberStatic.rightState = True
lowerSupportedRight = Refl

0 upperSupportedRight : isSupported @{the (DecEq N) %search} @{the (DecEq K) %search} Upper DGamma.R6FourFiberStatic.rightState = True
upperSupportedRight = Refl

0 middleAbsentRight : lookupFiber @{the (DecEq N) %search} {key = K} {value = V} {world = Unit} {error = String} Middle (registry DGamma.R6FourFiberStatic.rightState) = Nothing
middleAbsentRight = Refl

0 lowerToMiddle : SupportEdge (the (DecEq N) %search) DGamma.R6FourFiberStatic.leftState Lower Middle
lowerToMiddle = SupportPrecedence
  (MkPrecedenceEdge KA lowerFiber middleFiber Refl Refl Here Here)

0 middleToUpper : SupportEdge (the (DecEq N) %search) DGamma.R6FourFiberStatic.leftState Middle Upper
middleToUpper = SupportPrecedence
  (MkPrecedenceEdge KB middleFiber upperFiber Refl Refl Here Here)

0 supportedEndpointsPathThroughVestigial :
  SupportPath (the (DecEq N) %search) DGamma.R6FourFiberStatic.leftState Lower Upper
supportedEndpointsPathThroughVestigial =
  SupportPathMore lowerToMiddle (SupportPathOne middleToUpper)

0 lowerInGuardOrder : Elem Lower [Lower, Alternate, Upper]
lowerInGuardOrder = Here

0 upperInGuardOrder : Elem Upper [Lower, Alternate, Upper]
upperInGuardOrder = There (There Here)

0 noRightEdgeFromLower : {to : N} -> SupportEdge (the (DecEq N) %search) DGamma.R6FourFiberStatic.rightState Lower to -> Void
noRightEdgeFromLower {to = Lower}
  (SupportPrecedence (MkPrecedenceEdge KA _ _ Refl Refl provides consumes)) =
    case consumes of _ impossible
noRightEdgeFromLower {to = Lower}
  (SupportPrecedence (MkPrecedenceEdge KB _ _ Refl Refl provides consumes)) =
    case provides of _ impossible
noRightEdgeFromLower {to = Middle}
  (SupportPrecedence (MkPrecedenceEdge key _ _ found absent provides consumes)) =
    case absent of Refl impossible
noRightEdgeFromLower {to = Alternate}
  (SupportPrecedence (MkPrecedenceEdge KA _ _ Refl Refl provides consumes)) =
    case consumes of _ impossible
noRightEdgeFromLower {to = Alternate}
  (SupportPrecedence (MkPrecedenceEdge KB _ _ Refl Refl provides consumes)) =
    case provides of _ impossible
noRightEdgeFromLower {to = Upper}
  (SupportPrecedence (MkPrecedenceEdge KA _ _ Refl Refl provides consumes)) =
    case consumes of Here impossible
noRightEdgeFromLower {to = Upper}
  (SupportPrecedence (MkPrecedenceEdge KB _ _ Refl Refl provides consumes)) =
    case provides of Here impossible
noRightEdgeFromLower {to = Lower}
  (SupportParent (MkParentSupportEdge _ Refl parent)) =
    case parent of Refl impossible
noRightEdgeFromLower {to = Middle}
  (SupportParent (MkParentSupportEdge _ found parent)) =
    case found of Refl impossible
noRightEdgeFromLower {to = Alternate}
  (SupportParent (MkParentSupportEdge _ Refl parent)) =
    case parent of Refl impossible
noRightEdgeFromLower {to = Upper}
  (SupportParent (MkParentSupportEdge _ Refl parent)) =
    case parent of Refl impossible

0 noRightPathLowerUpper : SupportPath (the (DecEq N) %search) DGamma.R6FourFiberStatic.rightState Lower Upper -> Void
noRightPathLowerUpper (SupportPathOne edge) = noRightEdgeFromLower edge
noRightPathLowerUpper (SupportPathMore edge rest) = noRightEdgeFromLower edge

||| Exact shape of the revised forward-comparability field, specialized to the
||| concrete endpoint-member guards. It would map a real supported-endpoint path
||| whose intermediate is unsupported and absent on the right.
0 guardedTransportContradiction :
  ((lower, upper : N) ->
    Elem lower [Lower, Alternate, Upper] ->
    Elem upper [Lower, Alternate, Upper] ->
    SupportPath (the (DecEq N) %search) DGamma.R6FourFiberStatic.leftState lower upper ->
    SupportPath (the (DecEq N) %search) DGamma.R6FourFiberStatic.rightState lower upper) -> Void
guardedTransportContradiction transport =
  noRightPathLowerUpper
    (transport Lower Upper lowerInGuardOrder upperInGuardOrder
      supportedEndpointsPathThroughVestigial)

0 effectsPermitWithdrawal : EffectStateRelated (the (DecEq K) %search)
  (projectEffectState @{the (DecEq N) %search} DGamma.R6FourFiberStatic.leftState)
  (projectEffectState @{the (DecEq N) %search} DGamma.R6FourFiberStatic.rightState)
effectsPermitWithdrawal = MkEffectStateRelated Refl
  (\selected => case selected of
    Lower => Refl
    Middle => Refl
    Alternate => Refl
    Upper => Refl)

0 controlsOutsideMiddle : ControlEquivalentOutside (the (DecEq N) %search)
  [Middle] DGamma.R6FourFiberStatic.leftState DGamma.R6FourFiberStatic.rightState
controlsOutsideMiddle Lower notMiddle =
  SomeControlFibers (fiberControlReflexive lowerFiber)
controlsOutsideMiddle Middle notMiddle = void (notMiddle Here)
controlsOutsideMiddle Alternate notMiddle =
  SomeControlFibers (fiberControlReflexive alternateFiber)
controlsOutsideMiddle Upper notMiddle =
  SomeControlFibers (fiberControlReflexive upperFiber)

0 rawMiddleWithdrawn : RawNamesWithdrawn (the (DecEq N) %search) [Middle]
  DGamma.R6FourFiberStatic.leftState DGamma.R6FourFiberStatic.rightState
rawMiddleWithdrawn Lower Here impossible
rawMiddleWithdrawn Middle Here = VestigialNameWithdrawn middleFiber
  Refl Refl Refl Refl Refl
rawMiddleWithdrawn Alternate Here impossible
rawMiddleWithdrawn Upper Here impossible
rawMiddleWithdrawn selected (There later) = absurd later

0 middleNameHasGeneration : (child : N) -> Elem child [Middle] ->
  (birth : Nat ** Elem (MkRegistrationGeneration child birth)
    [MkRegistrationGeneration Middle 0])
middleNameHasGeneration Lower Here impossible
middleNameHasGeneration Middle Here = (0 ** Here)
middleNameHasGeneration Alternate Here impossible
middleNameHasGeneration Upper Here impossible
middleNameHasGeneration selected (There later) = absurd later

0 acceptedCanonicalEndpointAllowsIntermediate :
  CanonicalEndpointRelation N K Unit String V (the (DecEq N) %search)
    (the (DecEq K) %search) DGamma.R6FourFiberStatic.leftState DGamma.R6FourFiberStatic.rightState
acceptedCanonicalEndpointAllowsIntermediate = MkCanonicalEndpointRelation
  [Middle] [MkRegistrationGeneration Middle 0]
  effectsPermitWithdrawal controlsOutsideMiddle rawMiddleWithdrawn
  middleNameHasGeneration

||| Distinct parent constructors used by the R143 O15 countershape.
0 r143RootNotChild : {parent : N} -> Root = ChildOf parent -> Void
r143RootNotChild Refl impossible

||| Every successful right-endpoint lookup returns a root fiber. The lookup
||| equation owns the exact fiber reindexing used below.
0 r143RightFoundRoot :
  (selected : N) -> (fiber : Fiber N K V Unit String) ->
  lookupFiber @{the (DecEq N) %search} selected
    (registry DGamma.R6FourFiberStatic.rightState) = Just fiber ->
  fiberParent fiber = Root
r143RightFoundRoot Lower fiber found = case found of Refl => Refl
r143RightFoundRoot Middle fiber found = case found of Refl impossible
r143RightFoundRoot Alternate fiber found = case found of Refl => Refl
r143RightFoundRoot Upper fiber found = case found of Refl => Refl

||| The concrete reduced endpoint has no parent half of Equation 62.
0 r143NoRightParentEdge :
  {parent, child : N} ->
  ParentSupportEdge (the (DecEq N) %search) parent child
    DGamma.R6FourFiberStatic.rightState -> Void
r143NoRightParentEdge {child}
  (MkParentSupportEdge childFiber childFound childParent) =
    r143RootNotChild
      (trans (sym (r143RightFoundRoot child childFiber childFound)) childParent)

||| No exact provider lookup exists for the withdrawn middle actor.
0 r143MiddleLookupImpossible :
  {fiber : Fiber N K V Unit String} ->
  lookupFiber @{the (DecEq N) %search} Middle
    (registry DGamma.R6FourFiberStatic.rightState) = Just fiber -> Void
r143MiddleLookupImpossible found = case found of Refl impossible

||| The concrete upper actor has an empty provision specification.
0 r143UpperProvidesNothing :
  {fiber : Fiber N K V Unit String} ->
  lookupFiber @{the (DecEq N) %search} Upper
    (registry DGamma.R6FourFiberStatic.rightState) = Just fiber ->
  (wanted : K) ->
  Elem wanted (dependencies (componentProvisions (fiberComponent fiber))) ->
  Void
r143UpperProvidesNothing found wanted provides =
  case found of Refl => absurd provides

||| Every concrete reduced support edge starts at the alternate provider.
0 r143RightEdgeStartsAlternate :
  {lower, upper : N} ->
  SupportEdge (the (DecEq N) %search) DGamma.R6FourFiberStatic.rightState
    lower upper ->
  lower = Alternate
r143RightEdgeStartsAlternate {lower = Lower} edge =
  void (noRightEdgeFromLower edge)
r143RightEdgeStartsAlternate {lower = Middle} (SupportPrecedence edge) =
  void (r143MiddleLookupImpossible (providerFound edge))
r143RightEdgeStartsAlternate {lower = Middle} (SupportParent edge) =
  void (r143NoRightParentEdge edge)
r143RightEdgeStartsAlternate {lower = Alternate} edge = Refl
r143RightEdgeStartsAlternate {lower = Upper} (SupportPrecedence edge) =
  void (r143UpperProvidesNothing (providerFound edge) (edgeKey edge)
    (providerDeclares edge))
r143RightEdgeStartsAlternate {lower = Upper} (SupportParent edge) =
  void (r143NoRightParentEdge edge)

||| The lower fiber has no declared dependencies.
0 r143LowerDependsOnNothing :
  {fiber : Fiber N K V Unit String} ->
  lookupFiber @{the (DecEq N) %search} Lower
    (registry DGamma.R6FourFiberStatic.rightState) = Just fiber ->
  (wanted : K) ->
  Elem wanted (dependencies (componentDependencies (fiberComponent fiber))) ->
  Void
r143LowerDependsOnNothing found wanted depends =
  case found of Refl => absurd depends

||| The alternate provider also has no declared dependencies.
0 r143AlternateDependsOnNothing :
  {fiber : Fiber N K V Unit String} ->
  lookupFiber @{the (DecEq N) %search} Alternate
    (registry DGamma.R6FourFiberStatic.rightState) = Just fiber ->
  (wanted : K) ->
  Elem wanted (dependencies (componentDependencies (fiberComponent fiber))) ->
  Void
r143AlternateDependsOnNothing found wanted depends =
  case found of Refl => absurd depends

||| An edge from the alternate provider can end only at the upper consumer.
0 r143RightAlternateEdgeEndsUpper :
  {upper : N} ->
  SupportEdge (the (DecEq N) %search) DGamma.R6FourFiberStatic.rightState
    Alternate upper ->
  upper = Upper
r143RightAlternateEdgeEndsUpper {upper = Lower} (SupportPrecedence edge) =
  void (r143LowerDependsOnNothing (consumerFound edge) (edgeKey edge)
    (consumerDeclares edge))
r143RightAlternateEdgeEndsUpper {upper = Lower} (SupportParent edge) =
  void (r143NoRightParentEdge edge)
r143RightAlternateEdgeEndsUpper {upper = Middle} (SupportPrecedence edge) =
  void (r143MiddleLookupImpossible (consumerFound edge))
r143RightAlternateEdgeEndsUpper {upper = Middle} (SupportParent edge) =
  void (r143NoRightParentEdge edge)
r143RightAlternateEdgeEndsUpper {upper = Alternate} (SupportPrecedence edge) =
  void (r143AlternateDependsOnNothing (consumerFound edge) (edgeKey edge)
    (consumerDeclares edge))
r143RightAlternateEdgeEndsUpper {upper = Alternate} (SupportParent edge) =
  void (r143NoRightParentEdge edge)
r143RightAlternateEdgeEndsUpper {upper = Upper} edge = Refl

||| Reindex the edge once after its producer-owned source classification.
0 r143RightEdgeEndsUpperAfterStart :
  {lower, upper : N} ->
  (edge : SupportEdge (the (DecEq N) %search)
    DGamma.R6FourFiberStatic.rightState lower upper) ->
  lower = Alternate -> upper = Upper
r143RightEdgeEndsUpperAfterStart edge Refl =
  r143RightAlternateEdgeEndsUpper edge

0 r143UpperNotAlternate : Not (Upper = Alternate)
r143UpperNotAlternate Refl impossible

||| Since every right edge starts at `Alternate`, no nonempty support path can
||| start at `Upper`.
0 r143NoRightPathFromUpper :
  {target : N} ->
  SupportPath (the (DecEq N) %search) DGamma.R6FourFiberStatic.rightState
    Upper target -> Void
r143NoRightPathFromUpper (SupportPathOne edge) =
  r143UpperNotAlternate (r143RightEdgeStartsAlternate edge)
r143NoRightPathFromUpper (SupportPathMore edge rest) =
  r143UpperNotAlternate (r143RightEdgeStartsAlternate edge)

||| Consume the exact first-edge target before rejecting a longer path.
0 r143NoRightPathAfterUpper :
  {middle, target : N} ->
  middle = Upper ->
  SupportPath (the (DecEq N) %search) DGamma.R6FourFiberStatic.rightState
    middle target -> Void
r143NoRightPathAfterUpper Refl rest = r143NoRightPathFromUpper rest

||| Exact endpoint classifier for every nonempty reduced support path.
record R143RightPathShape (lower, upper : N) where
  constructor MkR143RightPathShape
  0 r143PathStartsAlternate : lower = Alternate
  0 r143PathEndsUpper : upper = Upper

0 r143RightPathShape :
  {lower, upper : N} ->
  (path : SupportPath (the (DecEq N) %search)
    DGamma.R6FourFiberStatic.rightState lower upper) ->
  R143RightPathShape lower upper
r143RightPathShape (SupportPathOne edge) =
  MkR143RightPathShape (r143RightEdgeStartsAlternate edge)
    (r143RightEdgeEndsUpperAfterStart edge
      (r143RightEdgeStartsAlternate edge))
r143RightPathShape (SupportPathMore edge rest) =
  void (r143NoRightPathAfterUpper
    (r143RightEdgeEndsUpperAfterStart edge
      (r143RightEdgeStartsAlternate edge)) rest)

0 r143AlternateFreshInRightOrder : Not (Elem Alternate [Upper, Lower])
r143AlternateFreshInRightOrder Here impossible
r143AlternateFreshInRightOrder (There Here) impossible
r143AlternateFreshInRightOrder (There (There later)) = absurd later

0 r143UpperFreshInRightOrder : Not (Elem Upper [Lower])
r143UpperFreshInRightOrder Here impossible
r143UpperFreshInRightOrder (There later) = absurd later

0 r143LowerFreshInRightOrder : Not (Elem Lower [])
r143LowerFreshInRightOrder present = absurd present

0 r143RightOrderUnique : UniqueKeys [Alternate, Upper, Lower]
r143RightOrderUnique = UniqueCons r143AlternateFreshInRightOrder
  (UniqueCons r143UpperFreshInRightOrder
    (UniqueCons r143LowerFreshInRightOrder UniqueNil))

0 r143MiddleNotInRightOrder : Not (Elem Middle [Alternate, Upper, Lower])
r143MiddleNotInRightOrder Here impossible
r143MiddleNotInRightOrder (There Here) impossible
r143MiddleNotInRightOrder (There (There Here)) impossible
r143MiddleNotInRightOrder (There (There (There later))) = absurd later

0 r143RightOrderSound :
  (selected : N) -> Elem selected [Alternate, Upper, Lower] ->
  isSupported @{the (DecEq N) %search} @{the (DecEq K) %search} selected
    DGamma.R6FourFiberStatic.rightState = True
r143RightOrderSound Lower member = lowerSupportedRight
r143RightOrderSound Middle member = void (r143MiddleNotInRightOrder member)
r143RightOrderSound Alternate member = Refl
r143RightOrderSound Upper member = upperSupportedRight

0 r143RightOrderComplete :
  (selected : N) ->
  isSupported @{the (DecEq N) %search} @{the (DecEq K) %search} selected
    DGamma.R6FourFiberStatic.rightState = True ->
  Elem selected [Alternate, Upper, Lower]
r143RightOrderComplete Lower supported = There (There Here)
r143RightOrderComplete Middle supported = case supported of Refl impossible
r143RightOrderComplete Alternate supported = Here
r143RightOrderComplete Upper supported = There Here

0 r143RightPathOrderedFromShape :
  {lower, upper : N} -> R143RightPathShape lower upper ->
  BeforeIn lower upper [Alternate, Upper, Lower]
r143RightPathOrderedFromShape shape =
  replace {p = \candidate => BeforeIn lower candidate [Alternate, Upper, Lower]}
    (sym (r143PathEndsUpper shape))
    (replace
      {p = \candidate => BeforeIn candidate Upper [Alternate, Upper, Lower]}
      (sym (r143PathStartsAlternate shape)) (BeforeHere Here))

0 noLowerBeforeUpperInRightOrder :
  BeforeIn Lower Upper [Alternate, Upper, Lower] -> Void
noLowerBeforeUpperInRightOrder
  (BeforeThere (BeforeThere (BeforeHere present))) = absurd present

0 inverseMappedRightOrderCannotLinearizeLeft :
  LinearizesSupport N K Unit String V (the (DecEq N) %search)
    (the (DecEq K) %search) DGamma.R6FourFiberStatic.leftState [Alternate, Upper, Lower] -> Void
inverseMappedRightOrderCannotLinearizeLeft linearization =
  noLowerBeforeUpperInRightOrder
    (supportPathsOrdered linearization Lower Upper
      supportedEndpointsPathThroughVestigial
      (There (There Here)) (There Here))


0 lowerNotAlternate : Not (Lower = Alternate)
lowerNotAlternate Refl impossible

0 lowerNotUpper : Not (Lower = Upper)
lowerNotUpper Refl impossible

firstActorSwap : AdjacentActorOrderSwap N
  [Lower, Alternate, Upper] [Alternate, Lower, Upper]
firstActorSwap = MkAdjacentActorOrderSwap [] Lower Alternate [Upper]
  Refl Refl lowerNotAlternate

secondActorSwap : AdjacentActorOrderSwap N
  [Alternate, Lower, Upper] [Alternate, Upper, Lower]
secondActorSwap = MkAdjacentActorOrderSwap [Alternate] Lower Upper []
  Refl Refl lowerNotUpper

replacementPureActorTarget : CertifiedActorPermutation N
  [Lower, Alternate, Upper] [Alternate, Upper, Lower]
replacementPureActorTarget = ActorPermutationStep firstActorSwap
  (ActorPermutationStep secondActorSwap ActorPermutationDone)

||| Revision-5 positive shape: the real original path and accepted withdrawal
||| coexist with a pure actor target, while the target is still refuted as a
||| left SupportPath linearization.
public export
record FourFiberRevision5Positive where
  constructor MkFourFiberRevision5Positive
  realOriginalPath : SupportPath (the (DecEq N) %search)
    DGamma.R6FourFiberStatic.leftState Lower Upper
  acceptedWithdrawnIntermediary : CanonicalEndpointRelation N K Unit String V
    (the (DecEq N) %search) (the (DecEq K) %search)
    DGamma.R6FourFiberStatic.leftState DGamma.R6FourFiberStatic.rightState
  falseLinearizationRefuted : LinearizesSupport N K Unit String V
    (the (DecEq N) %search) (the (DecEq K) %search)
    DGamma.R6FourFiberStatic.leftState [Alternate, Upper, Lower] -> Void
  replacementActorTarget : CertifiedActorPermutation N
    [Lower, Alternate, Upper] [Alternate, Upper, Lower]

0 fourFiberRevision5Positive : FourFiberRevision5Positive
fourFiberRevision5Positive = MkFourFiberRevision5Positive
  supportedEndpointsPathThroughVestigial
  acceptedCanonicalEndpointAllowsIntermediate
  inverseMappedRightOrderCannotLinearizeLeft
  replacementPureActorTarget

0 lowerFreshMoved : Not (Elem Lower [Alternate, Middle, Upper])
lowerFreshMoved Here impossible
lowerFreshMoved (There Here) impossible
lowerFreshMoved (There (There Here)) impossible
lowerFreshMoved (There (There (There later))) = absurd later

0 alternateFreshMoved : Not (Elem Alternate [Middle, Upper])
alternateFreshMoved Here impossible
alternateFreshMoved (There Here) impossible
alternateFreshMoved (There (There later)) = absurd later

0 middleFreshMoved : Not (Elem Middle [Upper])
middleFreshMoved Here impossible
middleFreshMoved (There later) = absurd later

movedMiddleRegistry : Registry N K V Unit String
movedMiddleRegistry = MkCoeffectContext
  [Bind Lower lowerFiber, Bind Alternate alternateFiber,
   Bind Middle middleFiber, Bind Upper upperFiber]
  (UniqueCons lowerFreshMoved
    (UniqueCons alternateFreshMoved
      (UniqueCons middleFreshMoved
        (UniqueCons (\present => absurd present) UniqueNil))))

movedMiddleState : SystemState N K V Unit String
movedMiddleState = MkSystemState () movedMiddleRegistry

0 movedLowerToMiddle : SupportEdge (the (DecEq N) %search)
  DGamma.R6FourFiberStatic.movedMiddleState Lower Middle
movedLowerToMiddle = SupportPrecedence
  (MkPrecedenceEdge KA lowerFiber middleFiber Refl Refl Here Here)

0 movedMiddleToUpper : SupportEdge (the (DecEq N) %search)
  DGamma.R6FourFiberStatic.movedMiddleState Middle Upper
movedMiddleToUpper = SupportPrecedence
  (MkPrecedenceEdge KB middleFiber upperFiber Refl Refl Here Here)

0 movedPositionStillHasPath : SupportPath (the (DecEq N) %search)
  DGamma.R6FourFiberStatic.movedMiddleState Lower Upper
movedPositionStillHasPath = SupportPathMore movedLowerToMiddle
  (SupportPathOne movedMiddleToUpper)

0 movedPositionStillUnsupported : isSupported @{the (DecEq N) %search}
  @{the (DecEq K) %search} Middle DGamma.R6FourFiberStatic.movedMiddleState = False
movedPositionStillUnsupported = Refl

movedPositionReplacementActorTarget : CertifiedActorPermutation N
  [Lower, Alternate, Upper] [Alternate, Upper, Lower]
movedPositionReplacementActorTarget = replacementPureActorTarget

upperLicensedByWithdrawnFiber : Fiber N K V Unit String
upperLicensedByWithdrawnFiber = MkFiber upperComponent (ChildOf Middle) False
  emptyOwned (Active id (ProviderView Alternate EmptyView))

leftLicensingRegistry : Registry N K V Unit String
leftLicensingRegistry = MkCoeffectContext
  [Bind Lower lowerFiber, Bind Middle middleFiber,
   Bind Alternate alternateFiber, Bind Upper upperLicensedByWithdrawnFiber]
  (UniqueCons lowerFresh
    (UniqueCons middleFresh
      (UniqueCons alternateFresh (UniqueCons (\present => absurd present) UniqueNil))))

rightLicensingRegistry : Registry N K V Unit String
rightLicensingRegistry = MkCoeffectContext
  [Bind Lower lowerFiber, Bind Alternate alternateFiber,
   Bind Upper upperLicensedByWithdrawnFiber]
  (UniqueCons lowerFreshRight
    (UniqueCons alternateFresh (UniqueCons (\present => absurd present) UniqueNil)))

leftLicensingState : SystemState N K V Unit String
leftLicensingState = MkSystemState () leftLicensingRegistry

rightLicensingState : SystemState N K V Unit String
rightLicensingState = MkSystemState () rightLicensingRegistry

0 licensingLowerToMiddle : SupportEdge (the (DecEq N) %search)
  DGamma.R6FourFiberStatic.leftLicensingState Lower Middle
licensingLowerToMiddle = SupportPrecedence
  (MkPrecedenceEdge KA lowerFiber middleFiber Refl Refl Here Here)

0 withdrawnMiddleLicensesUpper : SupportEdge (the (DecEq N) %search)
  DGamma.R6FourFiberStatic.leftLicensingState Middle Upper
withdrawnMiddleLicensesUpper = SupportParent
  (MkParentSupportEdge upperLicensedByWithdrawnFiber Refl Refl)

0 licensingParentPath : SupportPath (the (DecEq N) %search)
  DGamma.R6FourFiberStatic.leftLicensingState Lower Upper
licensingParentPath = SupportPathMore licensingLowerToMiddle
  (SupportPathOne withdrawnMiddleLicensesUpper)

0 licensingEffectsPermitWithdrawal : EffectStateRelated (the (DecEq K) %search)
  (projectEffectState @{the (DecEq N) %search} DGamma.R6FourFiberStatic.leftLicensingState)
  (projectEffectState @{the (DecEq N) %search} DGamma.R6FourFiberStatic.rightLicensingState)
licensingEffectsPermitWithdrawal = MkEffectStateRelated Refl
  (\selected => case selected of
    Lower => Refl
    Middle => Refl
    Alternate => Refl
    Upper => Refl)

0 licensingControlsOutsideMiddle : ControlEquivalentOutside (the (DecEq N) %search)
  [Middle] DGamma.R6FourFiberStatic.leftLicensingState DGamma.R6FourFiberStatic.rightLicensingState
licensingControlsOutsideMiddle Lower absent =
  SomeControlFibers (fiberControlReflexive lowerFiber)
licensingControlsOutsideMiddle Middle absent = void (absent Here)
licensingControlsOutsideMiddle Alternate absent =
  SomeControlFibers (fiberControlReflexive alternateFiber)
licensingControlsOutsideMiddle Upper absent =
  SomeControlFibers (fiberControlReflexive upperLicensedByWithdrawnFiber)

0 licensingRawMiddleWithdrawn : RawNamesWithdrawn (the (DecEq N) %search) [Middle]
  DGamma.R6FourFiberStatic.leftLicensingState DGamma.R6FourFiberStatic.rightLicensingState
licensingRawMiddleWithdrawn Lower Here impossible
licensingRawMiddleWithdrawn Middle Here = VestigialNameWithdrawn middleFiber
  Refl Refl Refl Refl Refl
licensingRawMiddleWithdrawn Alternate Here impossible
licensingRawMiddleWithdrawn Upper Here impossible
licensingRawMiddleWithdrawn selected (There later) = absurd later

0 acceptedLicensingParentWithdrawal : CanonicalEndpointRelation N K Unit String V
  (the (DecEq N) %search) (the (DecEq K) %search)
  DGamma.R6FourFiberStatic.leftLicensingState DGamma.R6FourFiberStatic.rightLicensingState
acceptedLicensingParentWithdrawal = MkCanonicalEndpointRelation
  [Middle] [MkRegistrationGeneration Middle 0]
  licensingEffectsPermitWithdrawal licensingControlsOutsideMiddle
  licensingRawMiddleWithdrawn middleNameHasGeneration

0 rightLicensingEndpointHasChild :
  hasChild @{the (DecEq N) %search} {key = K} {value = V} {world = Unit}
    {error = String} Middle (registry DGamma.R6FourFiberStatic.rightLicensingState) = True
rightLicensingEndpointHasChild = Refl

0 rightLicensingEndpointCannotBeWellFormed :
  registryWellFormed @{the (DecEq N) %search} @{the (DecEq K) %search}
    DGamma.R6FourFiberStatic.rightLicensingState = True -> Void
rightLicensingEndpointCannotBeWellFormed wellFormed =
  let childless = wellFormedAbsentHasNoChild (the (DecEq N) %search)
        (the (DecEq K) %search) Middle
        DGamma.R6FourFiberStatic.rightLicensingState wellFormed Refl
      contradiction = trans (sym childless) rightLicensingEndpointHasChild
  in case contradiction of Refl impossible

licensingParentReplacementActorTarget : CertifiedActorPermutation N
  [Lower, Alternate, Upper] [Alternate, Upper, Lower]
licensingParentReplacementActorTarget = replacementPureActorTarget
