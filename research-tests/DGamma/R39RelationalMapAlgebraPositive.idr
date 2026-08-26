module DGamma.R39RelationalMapAlgebraPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import DGamma.CP4RecoveryEffectRespect
import Decidable.Equality

%default total

public export
0 r39EffectRelatedSymmetric :
  EffectStateRelated keyEq left right -> EffectStateRelated keyEq right left
r39EffectRelatedSymmetric (MkEffectStateRelated ambient tables) =
  MkEffectStateRelated (sym ambient) (\actor => sym (tables actor))

public export
0 r39EffectRelatedTransitive :
  EffectStateRelated keyEq left middle ->
  EffectStateRelated keyEq middle right ->
  EffectStateRelated keyEq left right
r39EffectRelatedTransitive (MkEffectStateRelated firstAmbient firstTables)
  (MkEffectStateRelated secondAmbient secondTables) =
    MkEffectStateRelated (trans firstAmbient secondAmbient)
      (\actor => trans (firstTables actor) (secondTables actor))

public export
0 r39PartialRewrite :
  leftBefore = leftAfter -> rightBefore = rightAfter ->
  PartialRelated state rel leftBefore rightBefore ->
  PartialRelated state rel leftAfter rightAfter
r39PartialRewrite Refl Refl related = related

public export
0 r39EffectPartialSymmetric :
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    left right ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    right left
r39EffectPartialSymmetric PartialUndefined = PartialUndefined
r39EffectPartialSymmetric (PartialDefined related) =
  PartialDefined (r39EffectRelatedSymmetric related)

public export
0 r39EffectPartialTransitive :
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    first middle ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    middle last ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    first last
r39EffectPartialTransitive PartialUndefined PartialUndefined = PartialUndefined
r39EffectPartialTransitive (PartialDefined first) (PartialDefined second) =
  PartialDefined (r39EffectRelatedTransitive first second)

||| Every currently retained exact producer supplies the relational candidate
||| because each transition map already respects `EffectStateRelated`.
public export
0 r39ExactMapsGivePartialMapsRelated :
  (source, target : PartialEffectMap name key value world) ->
  EffectPartialMapRespects keyEq target ->
  ((state : EffectState name key value world) -> source state = target state) ->
  PartialMapsRelated (EffectStateEquivalence keyEq) source target
r39ExactMapsGivePartialMapsRelated source target targetRespects exact
  {x} {y} inputs =
    r39PartialRewrite (sym (exact x)) Refl (targetRespects x y inputs)

||| Strong relational map preservation is closed under the exact executable
||| `partialCompose` used by Definition 60 transformations.
public export
0 r39PartialMapsRelatedCompose :
  PartialMapsRelated (EffectStateEquivalence keyEq) sourceAfter targetAfter ->
  PartialMapsRelated (EffectStateEquivalence keyEq) sourceBefore targetBefore ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (partialCompose sourceAfter sourceBefore)
    (partialCompose targetAfter targetBefore)
r39PartialMapsRelatedCompose {sourceAfter} {targetAfter} {sourceBefore}
  {targetBefore} afterRelated beforeRelated {x} {y} inputs
  with (sourceBefore x) proof sourceRun
  r39PartialMapsRelatedCompose afterRelated beforeRelated inputs | Nothing
    with (targetBefore y) proof targetRun
    r39PartialMapsRelatedCompose afterRelated beforeRelated inputs |
      Nothing | Nothing = PartialUndefined
    r39PartialMapsRelatedCompose afterRelated beforeRelated inputs |
      Nothing | Just targetMiddle =
        case r39PartialRewrite sourceRun targetRun (beforeRelated inputs) of
          _ impossible
  r39PartialMapsRelatedCompose afterRelated beforeRelated inputs |
    Just sourceMiddle with (targetBefore y) proof targetRun
    r39PartialMapsRelatedCompose afterRelated beforeRelated inputs |
      Just sourceMiddle | Nothing =
        case r39PartialRewrite sourceRun targetRun (beforeRelated inputs) of
          _ impossible
    r39PartialMapsRelatedCompose afterRelated beforeRelated inputs |
      Just sourceMiddle | Just targetMiddle =
        let 0 middleRelated : EffectStateRelated keyEq sourceMiddle targetMiddle
            middleRelated = case r39PartialRewrite sourceRun targetRun
              (beforeRelated inputs) of PartialDefined related => related
        in afterRelated middleRelated

public export
0 r39PartialMapsRelatedTransitive :
  PartialMapsRelated (EffectStateEquivalence keyEq) first middle ->
  PartialMapsRelated (EffectStateEquivalence keyEq) middle last ->
  PartialMapsRelated (EffectStateEquivalence keyEq) first last
r39PartialMapsRelatedTransitive firstRelated secondRelated {x} {y} inputs =
  r39EffectPartialTransitive (firstRelated inputs)
    (secondRelated (effectStateReflexive keyEq y))

||| Consumer probe for `generatedMonoidsCommute`: a source commute square
||| transports through two relational map pairs without exact map equality.
public export
0 r39PartialCommuteFromRelatedMaps :
  (leftSource, leftTarget, rightSource, rightTarget :
    PartialEffectMap name key value world) ->
  PartialMapsRelated (EffectStateEquivalence keyEq) leftSource leftTarget ->
  PartialMapsRelated (EffectStateEquivalence keyEq) rightSource rightTarget ->
  PartialCommute (EffectStateEquivalence keyEq) leftSource rightSource ->
  PartialCommute (EffectStateEquivalence keyEq) leftTarget rightTarget
r39PartialCommuteFromRelatedMaps leftSource leftTarget rightSource rightTarget
  leftRelated rightRelated sourceCommute state =
    let 0 inputRelated = effectStateReflexive keyEq state
        0 sourceLeftRightToTarget =
          r39PartialMapsRelatedCompose leftRelated rightRelated inputRelated
        0 sourceRightLeftToTarget =
          r39PartialMapsRelatedCompose rightRelated leftRelated inputRelated
    in r39EffectPartialTransitive
      (r39EffectPartialSymmetric sourceLeftRightToTarget)
      (r39EffectPartialTransitive (sourceCommute state)
        sourceRightLeftToTarget)
