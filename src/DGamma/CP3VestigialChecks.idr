module DGamma.CP3VestigialChecks

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CalculusChecks
import DGamma.Section3Example
import DGamma.CP3StatementChecks
import Data.List.Elem
import Decidable.Equality

%default total

nameEq : DecEq Nat
nameEq = DGamma.CP3StatementChecks.episodeNameEq

keyEq : DecEq ToyKey
keyEq = DGamma.CP3StatementChecks.episodeKeyEq

child : Component ToyKey ToyValue ToyRuntime String
child = DGamma.CP3StatementChecks.episodeChild

parent : Component ToyKey ToyValue ToyRuntime String
parent = DGamma.CP3StatementChecks.episodeParent

||| The round-9 23-action left execution: unlike the older 24-action
||| activation-boundary regression, the closing episode's child is retired but
||| deliberately not O-Removed. It remains as a Lemma-57 vestigial endpoint.
public export
record VestigialLeft23 where
  constructor MkVestigialLeft23
  common23 : EpisodeCommonPrefix
  beginParent23 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LBegin 1)
    (namedAfter (episodeAdvance0b common23))
  insertDeleted23 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq
    (OInsert 2 (ChildOf 1) DGamma.CP3VestigialChecks.child) (namedAfter beginParent23)
  retireDeleted23 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (ORetire 2)
    (namedAfter insertDeleted23)
  retireProvider23 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (ORetire 0)
    (namedAfter retireDeleted23)
  leaveProvider23 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LLeave 0)
    (namedAfter retireProvider23)
  divertParent23 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LDivert 1)
    (namedAfter leaveProvider23)
  unloadParent23 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LUnload 1)
    (namedAfter divertParent23)
  unloadProvider23 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LUnload 0)
    (namedAfter unloadParent23)
  removeProvider23 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (ORemove 0)
    (namedAfter unloadProvider23)
  insertReplacement23 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq
    (OInsert 3 Root DGamma.CalculusChecks.providerComponent)
    (namedAfter removeProvider23)
  beginReplacement23 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LBegin 3)
    (namedAfter insertReplacement23)
  advanceReplacement23a : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LAdvance 3)
    (namedAfter beginReplacement23)
  advanceReplacement23b : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LAdvance 3)
    (namedAfter advanceReplacement23a)
  reopenParent23 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LBegin 1)
    (namedAfter advanceReplacement23b)
  insertSurvivor23 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq
    (OInsert 4 (ChildOf 1) DGamma.CP3VestigialChecks.child) (namedAfter reopenParent23)
  finishParent23 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LAdvance 1)
    (namedAfter insertSurvivor23)
  beginSurvivor23 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LBegin 4)
    (namedAfter finishParent23)
  finishSurvivor23 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LAdvance 4)
    (namedAfter beginSurvivor23)
  retireChildSource23 : EpisodeChildSource 2 (namedAfter insertDeleted23)
  retireProviderSource23 : EpisodeRootSource 0 (namedAfter retireDeleted23)
  removeProviderSource23 : EpisodeRootSource 0 (namedAfter unloadProvider23)

public export
buildVestigialLeft23 : EpisodeCommonPrefix -> Maybe VestigialLeft23
buildVestigialLeft23 common = do
  t5 <- checkedNamedFire nameEq keyEq (LBegin 1)
    (namedAfter (episodeAdvance0b common))
  t6 <- checkedNamedFire nameEq keyEq (OInsert 2 (ChildOf 1) DGamma.CP3VestigialChecks.child)
    (namedAfter t5)
  t7 <- checkedNamedFire nameEq keyEq (ORetire 2) (namedAfter t6)
  t8 <- checkedNamedFire nameEq keyEq (ORetire 0) (namedAfter t7)
  t9 <- checkedNamedFire nameEq keyEq (LLeave 0) (namedAfter t8)
  t10 <- checkedNamedFire nameEq keyEq (LDivert 1) (namedAfter t9)
  t11 <- checkedNamedFire nameEq keyEq (LUnload 1) (namedAfter t10)
  t12 <- checkedNamedFire nameEq keyEq (LUnload 0) (namedAfter t11)
  t13 <- checkedNamedFire nameEq keyEq (ORemove 0) (namedAfter t12)
  t14 <- checkedNamedFire nameEq keyEq
    (OInsert 3 Root DGamma.CalculusChecks.providerComponent) (namedAfter t13)
  t15 <- checkedNamedFire nameEq keyEq (LBegin 3) (namedAfter t14)
  t16 <- checkedNamedFire nameEq keyEq (LAdvance 3) (namedAfter t15)
  t17 <- checkedNamedFire nameEq keyEq (LAdvance 3) (namedAfter t16)
  t18 <- checkedNamedFire nameEq keyEq (LBegin 1) (namedAfter t17)
  t19 <- checkedNamedFire nameEq keyEq (OInsert 4 (ChildOf 1) DGamma.CP3VestigialChecks.child)
    (namedAfter t18)
  t20 <- checkedNamedFire nameEq keyEq (LAdvance 1) (namedAfter t19)
  t21 <- checkedNamedFire nameEq keyEq (LBegin 4) (namedAfter t20)
  t22 <- checkedNamedFire nameEq keyEq (LAdvance 4) (namedAfter t21)
  childSource <- findEpisodeChildSource 2 (namedAfter t6)
  retireSource <- findEpisodeRootSource 0 (namedAfter t7)
  removeSource <- findEpisodeRootSource 0 (namedAfter t12)
  Just (MkVestigialLeft23 common t5 t6 t7 t8 t9 t10 t11 t12 t13 t14
    t15 t16 t17 t18 t19 t20 t21 t22 childSource retireSource removeSource)

left23Tail23 : (left : VestigialLeft23) ->
  Transitions (namedAfter (finishSurvivor23 left))
    (namedAfter (finishSurvivor23 left))
left23Tail23 left = NoTransitions

left23Tail22 : (left : VestigialLeft23) ->
  Transitions (namedAfter (beginSurvivor23 left))
    (namedAfter (finishSurvivor23 left))
left23Tail22 left = MoreTransitions (namedTransition (finishSurvivor23 left))
  (left23Tail23 left)

left23Tail21 : (left : VestigialLeft23) ->
  Transitions (namedAfter (finishParent23 left))
    (namedAfter (finishSurvivor23 left))
left23Tail21 left = MoreTransitions (namedTransition (beginSurvivor23 left))
  (left23Tail22 left)

left23Tail20 : (left : VestigialLeft23) ->
  Transitions (namedAfter (insertSurvivor23 left))
    (namedAfter (finishSurvivor23 left))
left23Tail20 left = MoreTransitions (namedTransition (finishParent23 left))
  (left23Tail21 left)

left23Tail19 : (left : VestigialLeft23) ->
  Transitions (namedAfter (reopenParent23 left))
    (namedAfter (finishSurvivor23 left))
left23Tail19 left = MoreTransitions (namedTransition (insertSurvivor23 left))
  (left23Tail20 left)

left23Tail18 : (left : VestigialLeft23) ->
  Transitions (namedAfter (advanceReplacement23b left))
    (namedAfter (finishSurvivor23 left))
left23Tail18 left = MoreTransitions (namedTransition (reopenParent23 left))
  (left23Tail19 left)

left23Tail17 : (left : VestigialLeft23) ->
  Transitions (namedAfter (advanceReplacement23a left))
    (namedAfter (finishSurvivor23 left))
left23Tail17 left = MoreTransitions (namedTransition (advanceReplacement23b left))
  (left23Tail18 left)

left23Tail16 : (left : VestigialLeft23) ->
  Transitions (namedAfter (beginReplacement23 left))
    (namedAfter (finishSurvivor23 left))
left23Tail16 left = MoreTransitions (namedTransition (advanceReplacement23a left))
  (left23Tail17 left)

left23Tail15 : (left : VestigialLeft23) ->
  Transitions (namedAfter (insertReplacement23 left))
    (namedAfter (finishSurvivor23 left))
left23Tail15 left = MoreTransitions (namedTransition (beginReplacement23 left))
  (left23Tail16 left)

left23Tail14 : (left : VestigialLeft23) ->
  Transitions (namedAfter (removeProvider23 left))
    (namedAfter (finishSurvivor23 left))
left23Tail14 left = MoreTransitions (namedTransition (insertReplacement23 left))
  (left23Tail15 left)

left23Tail13 : (left : VestigialLeft23) ->
  Transitions (namedAfter (unloadProvider23 left))
    (namedAfter (finishSurvivor23 left))
left23Tail13 left = MoreTransitions (namedTransition (removeProvider23 left))
  (left23Tail14 left)

left23Tail12 : (left : VestigialLeft23) ->
  Transitions (namedAfter (unloadParent23 left))
    (namedAfter (finishSurvivor23 left))
left23Tail12 left = MoreTransitions (namedTransition (unloadProvider23 left))
  (left23Tail13 left)

left23Tail11 : (left : VestigialLeft23) ->
  Transitions (namedAfter (divertParent23 left))
    (namedAfter (finishSurvivor23 left))
left23Tail11 left = MoreTransitions (namedTransition (unloadParent23 left))
  (left23Tail12 left)

left23Tail10 : (left : VestigialLeft23) ->
  Transitions (namedAfter (leaveProvider23 left))
    (namedAfter (finishSurvivor23 left))
left23Tail10 left = MoreTransitions (namedTransition (divertParent23 left))
  (left23Tail11 left)

left23Tail9 : (left : VestigialLeft23) ->
  Transitions (namedAfter (retireProvider23 left))
    (namedAfter (finishSurvivor23 left))
left23Tail9 left = MoreTransitions (namedTransition (leaveProvider23 left))
  (left23Tail10 left)

left23Tail8 : (left : VestigialLeft23) ->
  Transitions (namedAfter (retireDeleted23 left))
    (namedAfter (finishSurvivor23 left))
left23Tail8 left = MoreTransitions (namedTransition (retireProvider23 left))
  (left23Tail9 left)

left23Tail7 : (left : VestigialLeft23) ->
  Transitions (namedAfter (insertDeleted23 left))
    (namedAfter (finishSurvivor23 left))
left23Tail7 left = MoreTransitions (namedTransition (retireDeleted23 left))
  (left23Tail8 left)

left23Tail6 : (left : VestigialLeft23) ->
  Transitions (namedAfter (beginParent23 left))
    (namedAfter (finishSurvivor23 left))
left23Tail6 left = MoreTransitions (namedTransition (insertDeleted23 left))
  (left23Tail7 left)

left23Tail5 : (left : VestigialLeft23) ->
  Transitions (namedAfter (episodeAdvance0b (common23 left)))
    (namedAfter (finishSurvivor23 left))
left23Tail5 left = MoreTransitions (namedTransition (beginParent23 left))
  (left23Tail6 left)

commonTrace : (common : EpisodeCommonPrefix) ->
  Transitions DGamma.CalculusChecks.initialSystem
    (namedAfter (episodeAdvance0b common))
commonTrace common = MoreTransitions (namedTransition (episodeInsert0 common))
  (MoreTransitions (namedTransition (episodeInsert1 common))
  (MoreTransitions (namedTransition (episodeBegin0 common))
  (MoreTransitions (namedTransition (episodeAdvance0a common))
  (MoreTransitions (namedTransition (episodeAdvance0b common)) NoTransitions))))

public export
vestigialLeft23Trace : (left : VestigialLeft23) ->
  Transitions DGamma.CalculusChecks.initialSystem
    (namedAfter (finishSurvivor23 left))
vestigialLeft23Trace left = appendTransitions (commonTrace (common23 left))
  (left23Tail5 left)

public export
vestigial23RuntimeCheck : Bool
vestigial23RuntimeCheck =
  case (buildEpisodeCommonPrefix, buildEpisodeCommonPrefix) of
    (Just leftCommon, Just rightCommon) =>
      case (buildVestigialLeft23 leftCommon, buildEpisodeRightTrace rightCommon) of
        (Just left, Just right) =>
          let leftFinal = namedAfter (finishSurvivor23 left)
              rightFinal = namedAfter (rightFinish4 right) in
            quiet @{nameEq} @{keyEq} leftFinal &&
            quiet @{nameEq} @{keyEq} rightFinal &&
            noFailedFibers leftFinal && noFailedFibers rightFinal &&
            isSupported @{nameEq} @{keyEq} 1 leftFinal &&
            isSupported @{nameEq} @{keyEq} 3 leftFinal &&
            isSupported @{nameEq} @{keyEq} 4 leftFinal &&
            not (isSupported @{nameEq} @{keyEq} 2 leftFinal) &&
            isSupported @{nameEq} @{keyEq} 1 rightFinal &&
            isSupported @{nameEq} @{keyEq} 3 rightFinal &&
            isSupported @{nameEq} @{keyEq} 4 rightFinal
        _ => False
    _ => False

swapNineFourteen : Nat -> Nat
swapNineFourteen 0 = 0
swapNineFourteen 1 = 1
swapNineFourteen 2 = 2
swapNineFourteen 3 = 3
swapNineFourteen 4 = 4
swapNineFourteen 5 = 5
swapNineFourteen 6 = 6
swapNineFourteen 7 = 7
swapNineFourteen 8 = 8
swapNineFourteen 9 = 14
swapNineFourteen 10 = 10
swapNineFourteen 11 = 11
swapNineFourteen 12 = 12
swapNineFourteen 13 = 13
swapNineFourteen 14 = 9
swapNineFourteen (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S later))))))))))))))) =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S later))))))))))))))

0 swapNineFourteenInvolutive : (n : Nat) ->
  swapNineFourteen (swapNineFourteen n) = n
swapNineFourteenInvolutive 0 = Refl
swapNineFourteenInvolutive 1 = Refl
swapNineFourteenInvolutive 2 = Refl
swapNineFourteenInvolutive 3 = Refl
swapNineFourteenInvolutive 4 = Refl
swapNineFourteenInvolutive 5 = Refl
swapNineFourteenInvolutive 6 = Refl
swapNineFourteenInvolutive 7 = Refl
swapNineFourteenInvolutive 8 = Refl
swapNineFourteenInvolutive 9 = Refl
swapNineFourteenInvolutive 10 = Refl
swapNineFourteenInvolutive 11 = Refl
swapNineFourteenInvolutive 12 = Refl
swapNineFourteenInvolutive 13 = Refl
swapNineFourteenInvolutive 14 = Refl
swapNineFourteenInvolutive (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S later))))))))))))))) = Refl

swapFourteenNineteen : Nat -> Nat
swapFourteenNineteen 0 = 0
swapFourteenNineteen 1 = 1
swapFourteenNineteen 2 = 2
swapFourteenNineteen 3 = 3
swapFourteenNineteen 4 = 4
swapFourteenNineteen 5 = 5
swapFourteenNineteen 6 = 6
swapFourteenNineteen 7 = 7
swapFourteenNineteen 8 = 8
swapFourteenNineteen 9 = 9
swapFourteenNineteen 10 = 10
swapFourteenNineteen 11 = 11
swapFourteenNineteen 12 = 12
swapFourteenNineteen 13 = 13
swapFourteenNineteen 14 = 19
swapFourteenNineteen 15 = 15
swapFourteenNineteen 16 = 16
swapFourteenNineteen 17 = 17
swapFourteenNineteen 18 = 18
swapFourteenNineteen 19 = 14
swapFourteenNineteen
  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S later)))))))))))))))))))) =
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S later))))))))))))))))))))

0 swapFourteenNineteenInvolutive : (n : Nat) ->
  swapFourteenNineteen (swapFourteenNineteen n) = n
swapFourteenNineteenInvolutive 0 = Refl
swapFourteenNineteenInvolutive 1 = Refl
swapFourteenNineteenInvolutive 2 = Refl
swapFourteenNineteenInvolutive 3 = Refl
swapFourteenNineteenInvolutive 4 = Refl
swapFourteenNineteenInvolutive 5 = Refl
swapFourteenNineteenInvolutive 6 = Refl
swapFourteenNineteenInvolutive 7 = Refl
swapFourteenNineteenInvolutive 8 = Refl
swapFourteenNineteenInvolutive 9 = Refl
swapFourteenNineteenInvolutive 10 = Refl
swapFourteenNineteenInvolutive 11 = Refl
swapFourteenNineteenInvolutive 12 = Refl
swapFourteenNineteenInvolutive 13 = Refl
swapFourteenNineteenInvolutive 14 = Refl
swapFourteenNineteenInvolutive 15 = Refl
swapFourteenNineteenInvolutive 16 = Refl
swapFourteenNineteenInvolutive 17 = Refl
swapFourteenNineteenInvolutive 18 = Refl
swapFourteenNineteenInvolutive 19 = Refl
swapFourteenNineteenInvolutive
  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S later)))))))))))))))))))) = Refl

vestigial23GenerationMap : RegistrationGeneration Nat -> RegistrationGeneration Nat
vestigial23GenerationMap (MkRegistrationGeneration 3 ordinal) =
  MkRegistrationGeneration 3 (swapNineFourteen ordinal)
vestigial23GenerationMap (MkRegistrationGeneration 4 ordinal) =
  MkRegistrationGeneration 4 (swapFourteenNineteen ordinal)
vestigial23GenerationMap generation = generation

0 vestigial23GenerationMapInvolutive : (generation : RegistrationGeneration Nat) ->
  vestigial23GenerationMap (vestigial23GenerationMap generation) = generation
vestigial23GenerationMapInvolutive (MkRegistrationGeneration 0 ordinal) = Refl
vestigial23GenerationMapInvolutive (MkRegistrationGeneration 1 ordinal) = Refl
vestigial23GenerationMapInvolutive (MkRegistrationGeneration 2 ordinal) = Refl
vestigial23GenerationMapInvolutive (MkRegistrationGeneration 3 ordinal) =
  cong (MkRegistrationGeneration 3) (swapNineFourteenInvolutive ordinal)
vestigial23GenerationMapInvolutive (MkRegistrationGeneration 4 ordinal) =
  cong (MkRegistrationGeneration 4) (swapFourteenNineteenInvolutive ordinal)
vestigial23GenerationMapInvolutive
  (MkRegistrationGeneration (S (S (S (S (S later))))) ordinal) = Refl

public export
vestigial23GenerationBijection : RegistrationGenerationBijection Nat
vestigial23GenerationBijection = MkRegistrationGenerationBijection
  vestigial23GenerationMap vestigial23GenerationMap
  vestigial23GenerationMapInvolutive vestigial23GenerationMapInvolutive

indexAdvance : Nat -> Action Nat ToyKey ToyValue ToyRuntime String ->
  RegistrationIndexState Nat -> RegistrationIndexState Nat
indexAdvance = advanceRegistrationIndex @{nameEq}

indexDelete : Nat -> Nat -> Nat -> Component ToyKey ToyValue ToyRuntime String ->
  RegistrationIndexState Nat -> RegistrationIndexState Nat
indexDelete = advanceDeletedRegistrationIndex @{nameEq}

indexSurvive : Nat -> Nat -> Nat -> Component ToyKey ToyValue ToyRuntime String ->
  RegistrationIndexState Nat -> RegistrationIndexState Nat
indexSurvive = advanceSurvivingRegistrationIndex @{nameEq}

commonIndex : RegistrationIndexState Nat
commonIndex =
  let i0 = indexAdvance 0
        (OInsert 0 Root DGamma.CalculusChecks.providerComponent)
        emptyRegistrationIndex
      i1 = indexAdvance 1 (OInsert 1 Root parent) i0
      i2 = indexAdvance 2 (LBegin 0) i1
      i3 = indexAdvance 3 (LAdvance 0) i2 in
    indexAdvance 4 (LAdvance 0) i3

left23DeletedIndex : RegistrationIndexState Nat
left23DeletedIndex = indexAdvance 5 (LBegin 1) commonIndex

left23SurvivingIndex : RegistrationIndexState Nat
left23SurvivingIndex =
  let i6 = indexDelete 6 2 1 child left23DeletedIndex
      i7 = indexAdvance 7 (ORetire 2) i6
      i8 = indexAdvance 8 (ORetire 0) i7
      i9 = indexAdvance 9 (LLeave 0) i8
      i10 = indexAdvance 10 (LDivert 1) i9
      i11 = indexAdvance 11 (LUnload 1) i10
      i12 = indexAdvance 12 (LUnload 0) i11
      i13 = indexAdvance 13 (ORemove 0) i12
      i14 = indexAdvance 14
        (OInsert 3 Root DGamma.CalculusChecks.providerComponent) i13
      i15 = indexAdvance 15 (LBegin 3) i14
      i16 = indexAdvance 16 (LAdvance 3) i15
      i17 = indexAdvance 17 (LAdvance 3) i16 in
    indexAdvance 18 (LBegin 1) i17

left23FinalIndex : RegistrationIndexState Nat
left23FinalIndex =
  let i19 = indexSurvive 19 4 1 child left23SurvivingIndex
      i20 = indexAdvance 20 (LAdvance 1) i19
      i21 = indexAdvance 21 (LBegin 4) i20 in
    indexAdvance 22 (LAdvance 4) i21

rightSurvivingIndex : RegistrationIndexState Nat
rightSurvivingIndex =
  let i5 = indexAdvance 5 (ORetire 0) commonIndex
      i6 = indexAdvance 6 (LLeave 0) i5
      i7 = indexAdvance 7 (LUnload 0) i6
      i8 = indexAdvance 8 (ORemove 0) i7
      i9 = indexAdvance 9
        (OInsert 3 Root DGamma.CalculusChecks.providerComponent) i8
      i10 = indexAdvance 10 (LBegin 3) i9
      i11 = indexAdvance 11 (LAdvance 3) i10
      i12 = indexAdvance 12 (LAdvance 3) i11 in
    indexAdvance 13 (LBegin 1) i12

rightFinalIndex : RegistrationIndexState Nat
rightFinalIndex =
  let i14 = indexSurvive 14 4 1 child rightSurvivingIndex
      i15 = indexAdvance 15 (LAdvance 1) i14
      i16 = indexAdvance 16 (LBegin 4) i15 in
    indexAdvance 17 (LAdvance 4) i16

0 deleted23Closes : (left : VestigialLeft23) ->
  ActionOccurs (LUnload 1) (left23Tail7 left)
deleted23Closes left =
  ActionOccursLater (namedTransition (retireDeleted23 left)) (left23Tail8 left)
  (ActionOccursLater (namedTransition (retireProvider23 left)) (left23Tail9 left)
  (ActionOccursLater (namedTransition (leaveProvider23 left)) (left23Tail10 left)
  (ActionOccursLater (namedTransition (divertParent23 left)) (left23Tail11 left)
  (ActionOccursHere (namedTransition (unloadParent23 left))
    (left23Tail12 left) (namedAction (unloadParent23 left))))))

0 deleted23Classification : (left : VestigialLeft23) ->
  DeletedClosingRegistration
    (registrationEventAt @{DGamma.CP3VestigialChecks.nameEq} 6
      DGamma.CP3VestigialChecks.left23DeletedIndex 2 1
      DGamma.CP3VestigialChecks.child)
    (left23Tail7 left)
deleted23Classification left = MkDeletedClosingRegistration
  (MkRegistrationActivation (MkRegistrationGeneration 1 1) 5) Refl
  (deleted23Closes left)

0 surviving23Open : (left : VestigialLeft23) ->
  NoParentUnload 1 (left23Tail20 left)
surviving23Open left =
  NoParentUnloadStep (namedTransition (finishParent23 left)) (left23Tail21 left)
    (\same => case trans (sym (namedAction (finishParent23 left))) same of
      Refl impossible)
  (NoParentUnloadStep (namedTransition (beginSurvivor23 left)) (left23Tail22 left)
    (\same => case trans (sym (namedAction (beginSurvivor23 left))) same of
      Refl impossible)
  (NoParentUnloadStep (namedTransition (finishSurvivor23 left)) (left23Tail23 left)
    (\same => case trans (sym (namedAction (finishSurvivor23 left))) same of
      Refl impossible) NoParentUnloadEnd))

0 rightOpen : (right : EpisodeRightTrace) ->
  NoParentUnload 1 (episodeRightTail15 right)
rightOpen right =
  NoParentUnloadStep (namedTransition (rightFinish1 right))
    (episodeRightTail16 right)
    (\same => case trans (sym (namedAction (rightFinish1 right))) same of
      Refl impossible)
  (NoParentUnloadStep (namedTransition (rightBegin4 right))
    (episodeRightTail17 right)
    (\same => case trans (sym (namedAction (rightBegin4 right))) same of
      Refl impossible)
  (NoParentUnloadStep (namedTransition (rightFinish4 right))
    (episodeRightTail18 right)
    (\same => case trans (sym (namedAction (rightFinish4 right))) same of
      Refl impossible) NoParentUnloadEnd))

0 surviving23Classification : (left : VestigialLeft23) ->
  SurvivingRegistration
    (registrationEventAt @{DGamma.CP3VestigialChecks.nameEq} 19
      DGamma.CP3VestigialChecks.left23SurvivingIndex 4 1
      DGamma.CP3VestigialChecks.child)
    (left23Tail20 left)
surviving23Classification left = MkSurvivingRegistration
  (MkRegistrationActivation (MkRegistrationGeneration 1 1) 18) Refl
  (surviving23Open left)

0 rightClassification : (right : EpisodeRightTrace) ->
  SurvivingRegistration
    (registrationEventAt @{DGamma.CP3VestigialChecks.nameEq} 14
      DGamma.CP3VestigialChecks.rightSurvivingIndex 4 1
      DGamma.CP3VestigialChecks.child)
    (episodeRightTail15 right)
rightClassification right = MkSurvivingRegistration
  (MkRegistrationActivation (MkRegistrationGeneration 1 1) 13) Refl
  (rightOpen right)

0 vestigial23TraceCorrespondence :
  (left : VestigialLeft23) -> (right : EpisodeRightTrace) ->
  RegistrationTraceCorrespondence DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.vestigial23GenerationBijection
    0 DGamma.CP3.emptyRegistrationIndex (vestigialLeft23Trace left)
      DGamma.CP3VestigialChecks.left23FinalIndex
    0 DGamma.CP3.emptyRegistrationIndex (episodeRightTrace right)
      DGamma.CP3VestigialChecks.rightFinalIndex [] []
vestigial23TraceCorrespondence left right =
  SkipLeftNonRegistration (OInsert 0 Root DGamma.CalculusChecks.providerComponent)
    (namedTransition (episodeInsert0 (common23 left)))
    (MoreTransitions (namedTransition (episodeInsert1 (common23 left)))
      (MoreTransitions (namedTransition (episodeBegin0 (common23 left)))
      (MoreTransitions (namedTransition (episodeAdvance0a (common23 left)))
      (MoreTransitions (namedTransition (episodeAdvance0b (common23 left)))
        (left23Tail5 left)))))
    (namedAction (episodeInsert0 (common23 left))) Refl
  (SkipLeftNonRegistration (OInsert 1 Root parent)
    (namedTransition (episodeInsert1 (common23 left)))
    (MoreTransitions (namedTransition (episodeBegin0 (common23 left)))
      (MoreTransitions (namedTransition (episodeAdvance0a (common23 left)))
      (MoreTransitions (namedTransition (episodeAdvance0b (common23 left)))
        (left23Tail5 left))))
    (namedAction (episodeInsert1 (common23 left))) Refl
  (SkipLeftNonRegistration (LBegin 0)
    (namedTransition (episodeBegin0 (common23 left)))
    (MoreTransitions (namedTransition (episodeAdvance0a (common23 left)))
      (MoreTransitions (namedTransition (episodeAdvance0b (common23 left)))
        (left23Tail5 left)))
    (namedAction (episodeBegin0 (common23 left))) Refl
  (SkipLeftNonRegistration (LAdvance 0)
    (namedTransition (episodeAdvance0a (common23 left)))
    (MoreTransitions (namedTransition (episodeAdvance0b (common23 left)))
      (left23Tail5 left))
    (namedAction (episodeAdvance0a (common23 left))) Refl
  (SkipLeftNonRegistration (LAdvance 0)
    (namedTransition (episodeAdvance0b (common23 left))) (left23Tail5 left)
    (namedAction (episodeAdvance0b (common23 left))) Refl
  (SkipLeftNonRegistration (LBegin 1) (namedTransition (beginParent23 left))
    (left23Tail6 left) (namedAction (beginParent23 left)) Refl
  (DiscardLeftDeletedRegistration (namedTransition (insertDeleted23 left))
    (left23Tail7 left) (namedAction (insertDeleted23 left))
    (deleted23Classification left)
  (SkipLeftNonRegistration (ORetire 2) (namedTransition (retireDeleted23 left))
    (left23Tail8 left) (namedAction (retireDeleted23 left)) Refl
  (SkipLeftNonRegistration (ORetire 0) (namedTransition (retireProvider23 left))
    (left23Tail9 left) (namedAction (retireProvider23 left)) Refl
  (SkipLeftNonRegistration (LLeave 0) (namedTransition (leaveProvider23 left))
    (left23Tail10 left) (namedAction (leaveProvider23 left)) Refl
  (SkipLeftNonRegistration (LDivert 1) (namedTransition (divertParent23 left))
    (left23Tail11 left) (namedAction (divertParent23 left)) Refl
  (SkipLeftNonRegistration (LUnload 1) (namedTransition (unloadParent23 left))
    (left23Tail12 left) (namedAction (unloadParent23 left)) Refl
  (SkipLeftNonRegistration (LUnload 0) (namedTransition (unloadProvider23 left))
    (left23Tail13 left) (namedAction (unloadProvider23 left)) Refl
  (SkipLeftNonRegistration (ORemove 0) (namedTransition (removeProvider23 left))
    (left23Tail14 left) (namedAction (removeProvider23 left)) Refl
  (SkipLeftNonRegistration
    (OInsert 3 Root DGamma.CalculusChecks.providerComponent)
    (namedTransition (insertReplacement23 left)) (left23Tail15 left)
    (namedAction (insertReplacement23 left)) Refl
  (SkipLeftNonRegistration (LBegin 3) (namedTransition (beginReplacement23 left))
    (left23Tail16 left) (namedAction (beginReplacement23 left)) Refl
  (SkipLeftNonRegistration (LAdvance 3)
    (namedTransition (advanceReplacement23a left)) (left23Tail17 left)
    (namedAction (advanceReplacement23a left)) Refl
  (SkipLeftNonRegistration (LAdvance 3)
    (namedTransition (advanceReplacement23b left)) (left23Tail18 left)
    (namedAction (advanceReplacement23b left)) Refl
  (SkipLeftNonRegistration (LBegin 1) (namedTransition (reopenParent23 left))
    (left23Tail19 left) (namedAction (reopenParent23 left)) Refl
  (QueueLeftGeneratedRegistration (namedTransition (insertSurvivor23 left))
    (left23Tail20 left) (namedAction (insertSurvivor23 left))
    (surviving23Classification left)
  (SkipLeftNonRegistration (LAdvance 1) (namedTransition (finishParent23 left))
    (left23Tail21 left) (namedAction (finishParent23 left)) Refl
  (SkipLeftNonRegistration (LBegin 4) (namedTransition (beginSurvivor23 left))
    (left23Tail22 left) (namedAction (beginSurvivor23 left)) Refl
  (SkipLeftNonRegistration (LAdvance 4) (namedTransition (finishSurvivor23 left))
    (left23Tail23 left) (namedAction (finishSurvivor23 left)) Refl
  (SkipRightNonRegistration
    (OInsert 0 Root DGamma.CalculusChecks.providerComponent)
    (namedTransition (episodeInsert0 (rightEpisodePrefix right)))
    (episodeRightTail1 right)
    (namedAction (episodeInsert0 (rightEpisodePrefix right))) Refl
  (SkipRightNonRegistration (OInsert 1 Root parent)
    (namedTransition (episodeInsert1 (rightEpisodePrefix right)))
    (episodeRightTail2 right)
    (namedAction (episodeInsert1 (rightEpisodePrefix right))) Refl
  (SkipRightNonRegistration (LBegin 0)
    (namedTransition (episodeBegin0 (rightEpisodePrefix right)))
    (episodeRightTail3 right)
    (namedAction (episodeBegin0 (rightEpisodePrefix right))) Refl
  (SkipRightNonRegistration (LAdvance 0)
    (namedTransition (episodeAdvance0a (rightEpisodePrefix right)))
    (episodeRightTail4 right)
    (namedAction (episodeAdvance0a (rightEpisodePrefix right))) Refl
  (SkipRightNonRegistration (LAdvance 0)
    (namedTransition (episodeAdvance0b (rightEpisodePrefix right)))
    (episodeRightTail5 right)
    (namedAction (episodeAdvance0b (rightEpisodePrefix right))) Refl
  (SkipRightNonRegistration (ORetire 0) (namedTransition (rightRetire0 right))
    (episodeRightTail6 right) (namedAction (rightRetire0 right)) Refl
  (SkipRightNonRegistration (LLeave 0) (namedTransition (rightLeave0 right))
    (episodeRightTail7 right) (namedAction (rightLeave0 right)) Refl
  (SkipRightNonRegistration (LUnload 0) (namedTransition (rightUnload0 right))
    (episodeRightTail8 right) (namedAction (rightUnload0 right)) Refl
  (SkipRightNonRegistration (ORemove 0) (namedTransition (rightRemove0 right))
    (episodeRightTail9 right) (namedAction (rightRemove0 right)) Refl
  (SkipRightNonRegistration
    (OInsert 3 Root DGamma.CalculusChecks.providerComponent)
    (namedTransition (rightInsert3 right)) (episodeRightTail10 right)
    (namedAction (rightInsert3 right)) Refl
  (SkipRightNonRegistration (LBegin 3) (namedTransition (rightBegin3 right))
    (episodeRightTail11 right) (namedAction (rightBegin3 right)) Refl
  (SkipRightNonRegistration (LAdvance 3)
    (namedTransition (rightAdvance3a right)) (episodeRightTail12 right)
    (namedAction (rightAdvance3a right)) Refl
  (SkipRightNonRegistration (LAdvance 3)
    (namedTransition (rightAdvance3b right)) (episodeRightTail13 right)
    (namedAction (rightAdvance3b right)) Refl
  (SkipRightNonRegistration (LBegin 1) (namedTransition (rightBegin1 right))
    (episodeRightTail14 right) (namedAction (rightBegin1 right)) Refl
  (MatchRightWithPendingLeft (namedTransition (rightSurvivingChild right))
    (episodeRightTail15 right) (namedAction (rightSurvivingChild right))
    (rightClassification right) []
    (registrationEventAt @{DGamma.CP3VestigialChecks.nameEq} 19
      DGamma.CP3VestigialChecks.left23SurvivingIndex 4 1
      DGamma.CP3VestigialChecks.child) []
    (MkRegistrationEventMatch Refl
      (MkRegistrationActivation (MkRegistrationGeneration 1 1) 18)
      (MkRegistrationActivation (MkRegistrationGeneration 1 1) 13)
      Refl Refl Refl Refl Refl)
  (SkipRightNonRegistration (LAdvance 1) (namedTransition (rightFinish1 right))
    (episodeRightTail16 right) (namedAction (rightFinish1 right)) Refl
  (SkipRightNonRegistration (LBegin 4) (namedTransition (rightBegin4 right))
    (episodeRightTail17 right) (namedAction (rightBegin4 right)) Refl
  (SkipRightNonRegistration (LAdvance 4) (namedTransition (rightFinish4 right))
    (episodeRightTail18 right) (namedAction (rightFinish4 right)) Refl
    RegistrationCorrespondenceEnd))))))))))))))))))))))))))))))))))))))))

0 vestigial23RegistrationCorrespondence :
  (left : VestigialLeft23) -> (right : EpisodeRightTrace) ->
  RegistrationCorrespondenceByGeneration
    DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.vestigial23GenerationBijection
    (vestigialLeft23Trace left) (episodeRightTrace right)
vestigial23RegistrationCorrespondence left right =
  MkRegistrationCorrespondenceByGeneration left23FinalIndex rightFinalIndex
    (vestigial23TraceCorrespondence left right)

left23Tail4 : (left : VestigialLeft23) ->
  Transitions (namedAfter (episodeAdvance0a (common23 left)))
    (namedAfter (finishSurvivor23 left))
left23Tail4 left = MoreTransitions
  (namedTransition (episodeAdvance0b (common23 left))) (left23Tail5 left)

left23Tail3 : (left : VestigialLeft23) ->
  Transitions (namedAfter (episodeBegin0 (common23 left)))
    (namedAfter (finishSurvivor23 left))
left23Tail3 left = MoreTransitions
  (namedTransition (episodeAdvance0a (common23 left))) (left23Tail4 left)

left23Tail2 : (left : VestigialLeft23) ->
  Transitions (namedAfter (episodeInsert1 (common23 left)))
    (namedAfter (finishSurvivor23 left))
left23Tail2 left = MoreTransitions
  (namedTransition (episodeBegin0 (common23 left))) (left23Tail3 left)

left23Tail1 : (left : VestigialLeft23) ->
  Transitions (namedAfter (episodeInsert0 (common23 left)))
    (namedAfter (finishSurvivor23 left))
left23Tail1 left = MoreTransitions
  (namedTransition (episodeInsert1 (common23 left))) (left23Tail2 left)

0 retireChild23Internal : (left : VestigialLeft23) ->
  RootOrchestrationStep DGamma.CP3VestigialChecks.nameEq (namedTransition (retireDeleted23 left)) -> Void
retireChild23Internal left = childRetireCannotBeRoot DGamma.CP3VestigialChecks.nameEq
  (namedTransition (retireDeleted23 left)) (namedAction (retireDeleted23 left))
  (episodeChildFiber (retireChildSource23 left))
  (episodeChildFound (retireChildSource23 left))
  (episodeChildParentRole (retireChildSource23 left))

0 retireProvider23Root : (left : VestigialLeft23) ->
  RootOrchestrationStep DGamma.CP3VestigialChecks.nameEq (namedTransition (retireProvider23 left))
retireProvider23Root left = RootRetireStep
  (episodeRootFiber (retireProviderSource23 left))
  (episodeRootFound (retireProviderSource23 left))
  (episodeRootParent (retireProviderSource23 left))
  (namedAction (retireProvider23 left))

0 removeProvider23Root : (left : VestigialLeft23) ->
  RootOrchestrationStep DGamma.CP3VestigialChecks.nameEq (namedTransition (removeProvider23 left))
removeProvider23Root left = RootRemoveStep
  (episodeRootFiber (removeProviderSource23 left))
  (episodeRootFound (removeProviderSource23 left))
  (episodeRootParent (removeProviderSource23 left))
  (namedAction (removeProvider23 left))

0 retireProviderRightRoot : (right : EpisodeRightTrace) ->
  RootOrchestrationStep DGamma.CP3VestigialChecks.nameEq (namedTransition (rightRetire0 right))
retireProviderRightRoot right = RootRetireStep
  (episodeRootFiber (rightRetire0Source right))
  (episodeRootFound (rightRetire0Source right))
  (episodeRootParent (rightRetire0Source right))
  (namedAction (rightRetire0 right))

0 removeProviderRightRoot : (right : EpisodeRightTrace) ->
  RootOrchestrationStep DGamma.CP3VestigialChecks.nameEq (namedTransition (rightRemove0 right))
removeProviderRightRoot right = RootRemoveStep
  (episodeRootFiber (rightRemove0Source right))
  (episodeRootFound (rightRemove0Source right))
  (episodeRootParent (rightRemove0Source right))
  (namedAction (rightRemove0 right))

0 vestigial23SameExternal :
  (left : VestigialLeft23) -> (right : EpisodeRightTrace) ->
  SameExternalOrchestration DGamma.CP3VestigialChecks.nameEq
    (vestigialLeft23Trace left)
    (episodeRightTrace right)
vestigial23SameExternal left right =
  MatchExternalInput (OInsert 0 Root DGamma.CalculusChecks.providerComponent)
    (namedTransition (episodeInsert0 (common23 left))) (left23Tail1 left)
    (RootInsertStep (namedAction (episodeInsert0 (common23 left))))
    (namedTransition (episodeInsert0 (rightEpisodePrefix right)))
    (episodeRightTail1 right)
    (RootInsertStep (namedAction (episodeInsert0 (rightEpisodePrefix right))))
    (namedAction (episodeInsert0 (common23 left)))
    (namedAction (episodeInsert0 (rightEpisodePrefix right)))
  (MatchExternalInput (OInsert 1 Root parent)
    (namedTransition (episodeInsert1 (common23 left))) (left23Tail2 left)
    (RootInsertStep (namedAction (episodeInsert1 (common23 left))))
    (namedTransition (episodeInsert1 (rightEpisodePrefix right)))
    (episodeRightTail2 right)
    (RootInsertStep (namedAction (episodeInsert1 (rightEpisodePrefix right))))
    (namedAction (episodeInsert1 (common23 left)))
    (namedAction (episodeInsert1 (rightEpisodePrefix right)))
  (SkipLeftInternal (namedTransition (episodeBegin0 (common23 left)))
    (left23Tail3 left) (namedLifecycleNotRoot (episodeBegin0 (common23 left)) Refl)
  (SkipLeftInternal (namedTransition (episodeAdvance0a (common23 left)))
    (left23Tail4 left)
    (namedLifecycleNotRoot (episodeAdvance0a (common23 left)) Refl)
  (SkipLeftInternal (namedTransition (episodeAdvance0b (common23 left)))
    (left23Tail5 left)
    (namedLifecycleNotRoot (episodeAdvance0b (common23 left)) Refl)
  (SkipLeftInternal (namedTransition (beginParent23 left)) (left23Tail6 left)
    (namedLifecycleNotRoot (beginParent23 left) Refl)
  (SkipLeftInternal (namedTransition (insertDeleted23 left)) (left23Tail7 left)
    (childInsertCannotBeRoot (namedTransition (insertDeleted23 left))
      (namedAction (insertDeleted23 left)))
  (SkipLeftInternal (namedTransition (retireDeleted23 left)) (left23Tail8 left)
    (retireChild23Internal left)
  (SkipRightInternal (namedTransition (episodeBegin0 (rightEpisodePrefix right)))
    (episodeRightTail3 right)
    (namedLifecycleNotRoot (episodeBegin0 (rightEpisodePrefix right)) Refl)
  (SkipRightInternal
    (namedTransition (episodeAdvance0a (rightEpisodePrefix right)))
    (episodeRightTail4 right)
    (namedLifecycleNotRoot (episodeAdvance0a (rightEpisodePrefix right)) Refl)
  (SkipRightInternal
    (namedTransition (episodeAdvance0b (rightEpisodePrefix right)))
    (episodeRightTail5 right)
    (namedLifecycleNotRoot (episodeAdvance0b (rightEpisodePrefix right)) Refl)
  (MatchExternalInput (ORetire 0)
    (namedTransition (retireProvider23 left)) (left23Tail9 left)
    (retireProvider23Root left)
    (namedTransition (rightRetire0 right)) (episodeRightTail6 right)
    (retireProviderRightRoot right)
    (namedAction (retireProvider23 left)) (namedAction (rightRetire0 right))
  (SkipLeftInternal (namedTransition (leaveProvider23 left)) (left23Tail10 left)
    (namedLifecycleNotRoot (leaveProvider23 left) Refl)
  (SkipLeftInternal (namedTransition (divertParent23 left)) (left23Tail11 left)
    (namedLifecycleNotRoot (divertParent23 left) Refl)
  (SkipLeftInternal (namedTransition (unloadParent23 left)) (left23Tail12 left)
    (namedLifecycleNotRoot (unloadParent23 left) Refl)
  (SkipLeftInternal (namedTransition (unloadProvider23 left)) (left23Tail13 left)
    (namedLifecycleNotRoot (unloadProvider23 left) Refl)
  (SkipRightInternal (namedTransition (rightLeave0 right))
    (episodeRightTail7 right) (namedLifecycleNotRoot (rightLeave0 right) Refl)
  (SkipRightInternal (namedTransition (rightUnload0 right))
    (episodeRightTail8 right) (namedLifecycleNotRoot (rightUnload0 right) Refl)
  (MatchExternalInput (ORemove 0)
    (namedTransition (removeProvider23 left)) (left23Tail14 left)
    (removeProvider23Root left)
    (namedTransition (rightRemove0 right)) (episodeRightTail9 right)
    (removeProviderRightRoot right)
    (namedAction (removeProvider23 left)) (namedAction (rightRemove0 right))
  (MatchExternalInput (OInsert 3 Root DGamma.CalculusChecks.providerComponent)
    (namedTransition (insertReplacement23 left)) (left23Tail15 left)
    (RootInsertStep (namedAction (insertReplacement23 left)))
    (namedTransition (rightInsert3 right)) (episodeRightTail10 right)
    (RootInsertStep (namedAction (rightInsert3 right)))
    (namedAction (insertReplacement23 left)) (namedAction (rightInsert3 right))
  (SkipLeftInternal (namedTransition (beginReplacement23 left))
    (left23Tail16 left) (namedLifecycleNotRoot (beginReplacement23 left) Refl)
  (SkipLeftInternal (namedTransition (advanceReplacement23a left))
    (left23Tail17 left) (namedLifecycleNotRoot (advanceReplacement23a left) Refl)
  (SkipLeftInternal (namedTransition (advanceReplacement23b left))
    (left23Tail18 left) (namedLifecycleNotRoot (advanceReplacement23b left) Refl)
  (SkipLeftInternal (namedTransition (reopenParent23 left)) (left23Tail19 left)
    (namedLifecycleNotRoot (reopenParent23 left) Refl)
  (SkipLeftInternal (namedTransition (insertSurvivor23 left)) (left23Tail20 left)
    (childInsertCannotBeRoot (namedTransition (insertSurvivor23 left))
      (namedAction (insertSurvivor23 left)))
  (SkipLeftInternal (namedTransition (finishParent23 left)) (left23Tail21 left)
    (namedLifecycleNotRoot (finishParent23 left) Refl)
  (SkipLeftInternal (namedTransition (beginSurvivor23 left)) (left23Tail22 left)
    (namedLifecycleNotRoot (beginSurvivor23 left) Refl)
  (SkipLeftInternal (namedTransition (finishSurvivor23 left)) (left23Tail23 left)
    (namedLifecycleNotRoot (finishSurvivor23 left) Refl)
  (SkipRightInternal (namedTransition (rightBegin3 right))
    (episodeRightTail11 right) (namedLifecycleNotRoot (rightBegin3 right) Refl)
  (SkipRightInternal (namedTransition (rightAdvance3a right))
    (episodeRightTail12 right) (namedLifecycleNotRoot (rightAdvance3a right) Refl)
  (SkipRightInternal (namedTransition (rightAdvance3b right))
    (episodeRightTail13 right) (namedLifecycleNotRoot (rightAdvance3b right) Refl)
  (SkipRightInternal (namedTransition (rightBegin1 right))
    (episodeRightTail14 right) (namedLifecycleNotRoot (rightBegin1 right) Refl)
  (SkipRightInternal (namedTransition (rightSurvivingChild right))
    (episodeRightTail15 right)
    (childInsertCannotBeRoot (namedTransition (rightSurvivingChild right))
      (namedAction (rightSurvivingChild right)))
  (SkipRightInternal (namedTransition (rightFinish1 right))
    (episodeRightTail16 right) (namedLifecycleNotRoot (rightFinish1 right) Refl)
  (SkipRightInternal (namedTransition (rightBegin4 right))
    (episodeRightTail17 right) (namedLifecycleNotRoot (rightBegin4 right) Refl)
  (SkipRightInternal (namedTransition (rightFinish4 right))
    (episodeRightTail18 right) (namedLifecycleNotRoot (rightFinish4 right) Refl)
    SameExternalOrchestrationEnd)))))))))))))))))))))))))))))))))))

0 vestigial23ExternalRoots :
  (left : VestigialLeft23) -> (right : EpisodeRightTrace) ->
  ExternalRootBirthCorrespondence
    DGamma.CP3VestigialChecks.vestigial23GenerationBijection 0
    (vestigialLeft23Trace left) 0 (episodeRightTrace right)
vestigial23ExternalRoots left right =
  MatchExternalRootBirth
    (namedTransition (episodeInsert0 (common23 left))) (left23Tail1 left)
    (namedTransition (episodeInsert0 (rightEpisodePrefix right)))
    (episodeRightTail1 right)
    (namedAction (episodeInsert0 (common23 left)))
    (namedAction (episodeInsert0 (rightEpisodePrefix right))) Refl
  (MatchExternalRootBirth
    (namedTransition (episodeInsert1 (common23 left))) (left23Tail2 left)
    (namedTransition (episodeInsert1 (rightEpisodePrefix right)))
    (episodeRightTail2 right)
    (namedAction (episodeInsert1 (common23 left)))
    (namedAction (episodeInsert1 (rightEpisodePrefix right))) Refl
  (SkipLeftNonExternalRootBirth (LBegin 0)
    (namedTransition (episodeBegin0 (common23 left))) (left23Tail3 left)
    (namedAction (episodeBegin0 (common23 left))) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 0)
    (namedTransition (episodeAdvance0a (common23 left))) (left23Tail4 left)
    (namedAction (episodeAdvance0a (common23 left))) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 0)
    (namedTransition (episodeAdvance0b (common23 left))) (left23Tail5 left)
    (namedAction (episodeAdvance0b (common23 left))) Refl
  (SkipLeftNonExternalRootBirth (LBegin 1)
    (namedTransition (beginParent23 left)) (left23Tail6 left)
    (namedAction (beginParent23 left)) Refl
  (SkipLeftNonExternalRootBirth (OInsert 2 (ChildOf 1) child)
    (namedTransition (insertDeleted23 left)) (left23Tail7 left)
    (namedAction (insertDeleted23 left)) Refl
  (SkipLeftNonExternalRootBirth (ORetire 2)
    (namedTransition (retireDeleted23 left)) (left23Tail8 left)
    (namedAction (retireDeleted23 left)) Refl
  (SkipLeftNonExternalRootBirth (ORetire 0)
    (namedTransition (retireProvider23 left)) (left23Tail9 left)
    (namedAction (retireProvider23 left)) Refl
  (SkipLeftNonExternalRootBirth (LLeave 0)
    (namedTransition (leaveProvider23 left)) (left23Tail10 left)
    (namedAction (leaveProvider23 left)) Refl
  (SkipLeftNonExternalRootBirth (LDivert 1)
    (namedTransition (divertParent23 left)) (left23Tail11 left)
    (namedAction (divertParent23 left)) Refl
  (SkipLeftNonExternalRootBirth (LUnload 1)
    (namedTransition (unloadParent23 left)) (left23Tail12 left)
    (namedAction (unloadParent23 left)) Refl
  (SkipLeftNonExternalRootBirth (LUnload 0)
    (namedTransition (unloadProvider23 left)) (left23Tail13 left)
    (namedAction (unloadProvider23 left)) Refl
  (SkipLeftNonExternalRootBirth (ORemove 0)
    (namedTransition (removeProvider23 left)) (left23Tail14 left)
    (namedAction (removeProvider23 left)) Refl
  (SkipRightNonExternalRootBirth (LBegin 0)
    (namedTransition (episodeBegin0 (rightEpisodePrefix right)))
    (episodeRightTail3 right)
    (namedAction (episodeBegin0 (rightEpisodePrefix right))) Refl
  (SkipRightNonExternalRootBirth (LAdvance 0)
    (namedTransition (episodeAdvance0a (rightEpisodePrefix right)))
    (episodeRightTail4 right)
    (namedAction (episodeAdvance0a (rightEpisodePrefix right))) Refl
  (SkipRightNonExternalRootBirth (LAdvance 0)
    (namedTransition (episodeAdvance0b (rightEpisodePrefix right)))
    (episodeRightTail5 right)
    (namedAction (episodeAdvance0b (rightEpisodePrefix right))) Refl
  (SkipRightNonExternalRootBirth (ORetire 0)
    (namedTransition (rightRetire0 right)) (episodeRightTail6 right)
    (namedAction (rightRetire0 right)) Refl
  (SkipRightNonExternalRootBirth (LLeave 0)
    (namedTransition (rightLeave0 right)) (episodeRightTail7 right)
    (namedAction (rightLeave0 right)) Refl
  (SkipRightNonExternalRootBirth (LUnload 0)
    (namedTransition (rightUnload0 right)) (episodeRightTail8 right)
    (namedAction (rightUnload0 right)) Refl
  (SkipRightNonExternalRootBirth (ORemove 0)
    (namedTransition (rightRemove0 right)) (episodeRightTail9 right)
    (namedAction (rightRemove0 right)) Refl
  (MatchExternalRootBirth (namedTransition (insertReplacement23 left))
    (left23Tail15 left) (namedTransition (rightInsert3 right))
    (episodeRightTail10 right) (namedAction (insertReplacement23 left))
    (namedAction (rightInsert3 right)) Refl
  (SkipLeftNonExternalRootBirth (LBegin 3)
    (namedTransition (beginReplacement23 left)) (left23Tail16 left)
    (namedAction (beginReplacement23 left)) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 3)
    (namedTransition (advanceReplacement23a left)) (left23Tail17 left)
    (namedAction (advanceReplacement23a left)) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 3)
    (namedTransition (advanceReplacement23b left)) (left23Tail18 left)
    (namedAction (advanceReplacement23b left)) Refl
  (SkipLeftNonExternalRootBirth (LBegin 1)
    (namedTransition (reopenParent23 left)) (left23Tail19 left)
    (namedAction (reopenParent23 left)) Refl
  (SkipLeftNonExternalRootBirth (OInsert 4 (ChildOf 1) child)
    (namedTransition (insertSurvivor23 left)) (left23Tail20 left)
    (namedAction (insertSurvivor23 left)) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 1)
    (namedTransition (finishParent23 left)) (left23Tail21 left)
    (namedAction (finishParent23 left)) Refl
  (SkipLeftNonExternalRootBirth (LBegin 4)
    (namedTransition (beginSurvivor23 left)) (left23Tail22 left)
    (namedAction (beginSurvivor23 left)) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 4)
    (namedTransition (finishSurvivor23 left)) (left23Tail23 left)
    (namedAction (finishSurvivor23 left)) Refl
  (SkipRightNonExternalRootBirth (LBegin 3)
    (namedTransition (rightBegin3 right)) (episodeRightTail11 right)
    (namedAction (rightBegin3 right)) Refl
  (SkipRightNonExternalRootBirth (LAdvance 3)
    (namedTransition (rightAdvance3a right)) (episodeRightTail12 right)
    (namedAction (rightAdvance3a right)) Refl
  (SkipRightNonExternalRootBirth (LAdvance 3)
    (namedTransition (rightAdvance3b right)) (episodeRightTail13 right)
    (namedAction (rightAdvance3b right)) Refl
  (SkipRightNonExternalRootBirth (LBegin 1)
    (namedTransition (rightBegin1 right)) (episodeRightTail14 right)
    (namedAction (rightBegin1 right)) Refl
  (SkipRightNonExternalRootBirth (OInsert 4 (ChildOf 1) child)
    (namedTransition (rightSurvivingChild right)) (episodeRightTail15 right)
    (namedAction (rightSurvivingChild right)) Refl
  (SkipRightNonExternalRootBirth (LAdvance 1)
    (namedTransition (rightFinish1 right)) (episodeRightTail16 right)
    (namedAction (rightFinish1 right)) Refl
  (SkipRightNonExternalRootBirth (LBegin 4)
    (namedTransition (rightBegin4 right)) (episodeRightTail17 right)
    (namedAction (rightBegin4 right)) Refl
  (SkipRightNonExternalRootBirth (LAdvance 4)
    (namedTransition (rightFinish4 right)) (episodeRightTail18 right)
    (namedAction (rightFinish4 right)) Refl
    ExternalRootBirthCorrespondenceEnd)))))))))))))))))))))))))))))))))))))

0 left23Current :
  (left : VestigialLeft23) -> (right : EpisodeRightTrace) ->
  VestigialEndpointGeneration Nat ToyKey ToyRuntime String ToyValue DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq
    (leftFinalGenerations (vestigial23RegistrationCorrespondence left right))
    (leftDeletedGenerations (vestigial23RegistrationCorrespondence left right))
    2 (namedAfter (finishSurvivor23 left)) ->
  (n : Nat) -> (generation : RegistrationGeneration Nat) ->
  lookupCurrentGeneration @{DGamma.CP3VestigialChecks.nameEq} n
    (leftFinalGenerations (vestigial23RegistrationCorrespondence left right)) =
      Just generation ->
  Either
    (VestigialEndpointGeneration Nat ToyKey ToyRuntime String ToyValue DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq
      (leftFinalGenerations (vestigial23RegistrationCorrespondence left right))
      (leftDeletedGenerations (vestigial23RegistrationCorrespondence left right))
      n (namedAfter (finishSurvivor23 left)))
    (rightGeneration : RegistrationGeneration Nat **
      (generationForward DGamma.CP3VestigialChecks.vestigial23GenerationBijection generation = rightGeneration,
       lookupCurrentGeneration @{DGamma.CP3VestigialChecks.nameEq} n
         (rightFinalGenerations
           (vestigial23RegistrationCorrespondence left right)) =
         Just rightGeneration))
left23Current left right vestigial 0 generation found =
  void (nothingIsNotJust found)
left23Current left right vestigial 1 generation found =
  case justInjective found of
    Refl => Right (MkRegistrationGeneration 1 1 ** (Refl, Refl))
left23Current left right vestigial 2 generation found = Left vestigial
left23Current left right vestigial 3 generation found =
  case justInjective found of
    Refl => Right (MkRegistrationGeneration 3 9 ** (Refl, Refl))
left23Current left right vestigial 4 generation found =
  case justInjective found of
    Refl => Right (MkRegistrationGeneration 4 14 ** (Refl, Refl))
left23Current left right vestigial (S (S (S (S (S later))))) generation found =
  void (nothingIsNotJust found)

0 right23Current :
  (left : VestigialLeft23) -> (right : EpisodeRightTrace) ->
  (n : Nat) -> (generation : RegistrationGeneration Nat) ->
  lookupCurrentGeneration @{DGamma.CP3VestigialChecks.nameEq} n
    (rightFinalGenerations (vestigial23RegistrationCorrespondence left right)) =
      Just generation ->
  Either
    (VestigialEndpointGeneration Nat ToyKey ToyRuntime String ToyValue DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq
      (rightFinalGenerations (vestigial23RegistrationCorrespondence left right))
      (rightDeletedGenerations (vestigial23RegistrationCorrespondence left right))
      n (namedAfter (rightFinish4 right)))
    (leftGeneration : RegistrationGeneration Nat **
      (generationBackward DGamma.CP3VestigialChecks.vestigial23GenerationBijection generation = leftGeneration,
       lookupCurrentGeneration @{DGamma.CP3VestigialChecks.nameEq} n
         (leftFinalGenerations
           (vestigial23RegistrationCorrespondence left right)) =
         Just leftGeneration))
right23Current left right 0 generation found = void (nothingIsNotJust found)
right23Current left right 1 generation found =
  case justInjective found of
    Refl => Right (MkRegistrationGeneration 1 1 ** (Refl, Refl))
right23Current left right 2 generation found = void (nothingIsNotJust found)
right23Current left right 3 generation found =
  case justInjective found of
    Refl => Right (MkRegistrationGeneration 3 14 ** (Refl, Refl))
right23Current left right 4 generation found =
  case justInjective found of
    Refl => Right (MkRegistrationGeneration 4 19 ** (Refl, Refl))
right23Current left right (S (S (S (S (S later))))) generation found =
  void (nothingIsNotJust found)

0 vestigial23EndpointRenaming :
  (left : VestigialLeft23) -> (right : EpisodeRightTrace) ->
  (vestigial : VestigialEndpointGeneration Nat ToyKey ToyRuntime String ToyValue
    DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq
    (leftFinalGenerations (vestigial23RegistrationCorrespondence left right))
    (leftDeletedGenerations (vestigial23RegistrationCorrespondence left right))
    2 (namedAfter (finishSurvivor23 left))) ->
  CurrentEndpointRenaming DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq DGamma.CP3VestigialChecks.vestigial23GenerationBijection
    (vestigialLeft23Trace left) (episodeRightTrace right)
    (vestigial23RegistrationCorrespondence left right)
vestigial23EndpointRenaming left right vestigial =
  MkCurrentEndpointRenaming identityNameBijection
    (\n, fiber, found, root => Refl)
    (\n, fiber, found, root => Refl)
    (left23Current left right vestigial)
    (right23Current left right)

0 vestigial23SameInputs :
  (left : VestigialLeft23) -> (right : EpisodeRightTrace) ->
  (vestigial : VestigialEndpointGeneration Nat ToyKey ToyRuntime String ToyValue
    DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq
    (leftFinalGenerations (vestigial23RegistrationCorrespondence left right))
    (leftDeletedGenerations (vestigial23RegistrationCorrespondence left right))
    2 (namedAfter (finishSurvivor23 left))) ->
  SameOrchestrationModuloGenerated DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq
    (vestigialLeft23Trace left) (episodeRightTrace right)
vestigial23SameInputs left right vestigial = MkSameOrchestrationModuloGenerated
  DGamma.CP3VestigialChecks.vestigial23GenerationBijection (vestigial23SameExternal left right)
  (vestigial23ExternalRoots left right)
  (vestigial23RegistrationCorrespondence left right)
  (vestigial23EndpointRenaming left right vestigial)

public export
record Vestigial23CorrespondenceWitness where
  constructor MkVestigial23CorrespondenceWitness
  vestigial23Left : VestigialLeft23
  vestigial23Right : EpisodeRightTrace
  0 vestigial23SameInputWitness : SameOrchestrationModuloGenerated DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq
    (vestigialLeft23Trace vestigial23Left)
    (episodeRightTrace vestigial23Right)

public export
vestigial23CorrespondenceWitness : Maybe Vestigial23CorrespondenceWitness
vestigial23CorrespondenceWitness = do
  leftCommon <- buildEpisodeCommonPrefix
  rightCommon <- buildEpisodeCommonPrefix
  left <- buildVestigialLeft23 leftCommon
  right <- buildEpisodeRightTrace rightCommon
  vestigial <- vestigialEndpointGeneration DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq
    (indexedLiveGenerations DGamma.CP3VestigialChecks.left23FinalIndex)
    (indexedDeletedGenerations DGamma.CP3VestigialChecks.left23FinalIndex)
    2 (namedAfter (finishSurvivor23 left)) (MkRegistrationGeneration 2 6)
    Refl Here
  Just (MkVestigial23CorrespondenceWitness left right
    (vestigial23SameInputs left right vestigial))

public export
vestigial23CorrespondenceCheck : Bool
vestigial23CorrespondenceCheck = case vestigial23CorrespondenceWitness of
  Nothing => False
  Just witness => True

||| The literal public Theorem-73 boundary for the 23/18 reviewer pair. Every
||| semantic premise is retained; the projection reaches the new outside-R
||| endpoint relation rather than an exact-domain shadow conclusion.
public export
0 vestigial23Theorem73PremiseChain :
  confluenceTheorem Nat ToyKey ToyValue ToyRuntime String ->
  (protocol : RegistrationProtocol ToyKey ToyValue ToyRuntime String) ->
  (0 witness : Vestigial23CorrespondenceWitness) ->
  AlignedTransitions Nat ToyKey ToyRuntime String ToyValue DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq
    (vestigialLeft23Trace (vestigial23Left witness)) ->
  AlignedTransitions Nat ToyKey ToyRuntime String ToyValue DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq
    (episodeRightTrace (vestigial23Right witness)) ->
  RegistrationDiscipline protocol DGamma.CP3VestigialChecks.nameEq
    (vestigialLeft23Trace (vestigial23Left witness)) ->
  RegistrationDiscipline protocol DGamma.CP3VestigialChecks.nameEq
    (episodeRightTrace (vestigial23Right witness)) ->
  registryWellFormed @{DGamma.CP3VestigialChecks.nameEq} @{DGamma.CP3VestigialChecks.keyEq}
    DGamma.CalculusChecks.initialSystem = True ->
  bindings (registry DGamma.CalculusChecks.initialSystem) = [] ->
  quiet @{DGamma.CP3VestigialChecks.nameEq} @{DGamma.CP3VestigialChecks.keyEq}
    (namedAfter (finishSurvivor23 (vestigial23Left witness))) = True ->
  quiet @{DGamma.CP3VestigialChecks.nameEq} @{DGamma.CP3VestigialChecks.keyEq}
    (namedAfter (rightFinish4 (vestigial23Right witness))) = True ->
  noFailedFibers
    (namedAfter (finishSurvivor23 (vestigial23Left witness))) = True ->
  noFailedFibers
    (namedAfter (rightFinish4 (vestigial23Right witness))) = True ->
  TraceComponentsTotal DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq
    (vestigialLeft23Trace (vestigial23Left witness)) ->
  TraceComponentsTotal DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq
    (episodeRightTrace (vestigial23Right witness)) ->
  TraceIndependent Nat ToyKey ToyRuntime String ToyValue DGamma.CP3VestigialChecks.keyEq
    (vestigialLeft23Trace (vestigial23Left witness)) ->
  TraceIndependent Nat ToyKey ToyRuntime String ToyValue DGamma.CP3VestigialChecks.keyEq
    (episodeRightTrace (vestigial23Right witness)) ->
  (registrations : RegistrationCorrespondenceByGeneration
      DGamma.CP3VestigialChecks.nameEq
      (generatedGenerationBijection (vestigial23SameInputWitness witness))
      (vestigialLeft23Trace (vestigial23Left witness))
      (episodeRightTrace (vestigial23Right witness)) **
    SystemEquivalentByRenamingModuloVestigial Nat ToyKey ToyRuntime String
      ToyValue DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq
      registrations (currentNameBijection (endpointRenaming
        (vestigial23SameInputWitness witness))))
vestigial23Theorem73PremiseChain claim protocol witness leftAligned rightAligned
  leftDiscipline rightDiscipline initialWellFormed initialEmpty leftQuiet
  rightQuiet leftSuccess rightSuccess leftTotal rightTotal leftIndependent
  rightIndependent =
    let result = claim DGamma.CP3VestigialChecks.nameEq
          DGamma.CP3VestigialChecks.keyEq protocol
          DGamma.CalculusChecks.initialSystem
          (namedAfter (finishSurvivor23 (vestigial23Left witness)))
          (namedAfter (rightFinish4 (vestigial23Right witness)))
          (vestigialLeft23Trace (vestigial23Left witness))
          (episodeRightTrace (vestigial23Right witness))
          leftAligned rightAligned leftDiscipline rightDiscipline
          initialWellFormed initialEmpty leftQuiet rightQuiet leftSuccess
          rightSuccess leftTotal rightTotal leftIndependent rightIndependent
          (vestigial23SameInputWitness witness) in
      (finalRegistrationCorrespondence result ** finalEndpointsEquivalent result)

||| The reviewer's stronger 27-action variant: child 2 is activated, retired
||| while Active, and only leaves/unloads after its registering parent closes.
||| It nevertheless ends in the same retired, clean, childless vestigial shape.
public export
record VestigialLeft27 where
  constructor MkVestigialLeft27
  common27 : EpisodeCommonPrefix
  beginParent27 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LBegin 1)
    (namedAfter (episodeAdvance0b common27))
  insertDeleted27 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq
    (OInsert 2 (ChildOf 1) DGamma.CP3VestigialChecks.child)
    (namedAfter beginParent27)
  beginDeleted27 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LBegin 2) (namedAfter insertDeleted27)
  finishDeleted27 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LAdvance 2) (namedAfter beginDeleted27)
  retireDeleted27 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (ORetire 2) (namedAfter finishDeleted27)
  retireProvider27 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (ORetire 0) (namedAfter retireDeleted27)
  leaveProvider27 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LLeave 0) (namedAfter retireProvider27)
  divertParent27 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LDivert 1) (namedAfter leaveProvider27)
  unloadParent27 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LUnload 1) (namedAfter divertParent27)
  leaveDeleted27 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LLeave 2) (namedAfter unloadParent27)
  unloadDeleted27 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LUnload 2) (namedAfter leaveDeleted27)
  unloadProvider27 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LUnload 0) (namedAfter unloadDeleted27)
  removeProvider27 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (ORemove 0) (namedAfter unloadProvider27)
  insertReplacement27 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq
    (OInsert 3 Root DGamma.CalculusChecks.providerComponent)
    (namedAfter removeProvider27)
  beginReplacement27 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LBegin 3) (namedAfter insertReplacement27)
  advanceReplacement27a : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LAdvance 3) (namedAfter beginReplacement27)
  advanceReplacement27b : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LAdvance 3)
    (namedAfter advanceReplacement27a)
  reopenParent27 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LBegin 1)
    (namedAfter advanceReplacement27b)
  insertSurvivor27 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq
    (OInsert 4 (ChildOf 1) DGamma.CP3VestigialChecks.child)
    (namedAfter reopenParent27)
  finishParent27 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LAdvance 1) (namedAfter insertSurvivor27)
  beginSurvivor27 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LBegin 4) (namedAfter finishParent27)
  finishSurvivor27 : CheckedNamedTransition DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (LAdvance 4) (namedAfter beginSurvivor27)
  retireChildSource27 : EpisodeChildSource 2 (namedAfter finishDeleted27)
  retireProviderSource27 : EpisodeRootSource 0 (namedAfter retireDeleted27)
  removeProviderSource27 : EpisodeRootSource 0 (namedAfter unloadProvider27)

public export
buildVestigialLeft27 : EpisodeCommonPrefix -> Maybe VestigialLeft27
buildVestigialLeft27 common = do
  t5 <- checkedNamedFire nameEq keyEq (LBegin 1)
    (namedAfter (episodeAdvance0b common))
  t6 <- checkedNamedFire nameEq keyEq (OInsert 2 (ChildOf 1) child) (namedAfter t5)
  t7 <- checkedNamedFire nameEq keyEq (LBegin 2) (namedAfter t6)
  t8 <- checkedNamedFire nameEq keyEq (LAdvance 2) (namedAfter t7)
  t9 <- checkedNamedFire nameEq keyEq (ORetire 2) (namedAfter t8)
  t10 <- checkedNamedFire nameEq keyEq (ORetire 0) (namedAfter t9)
  t11 <- checkedNamedFire nameEq keyEq (LLeave 0) (namedAfter t10)
  t12 <- checkedNamedFire nameEq keyEq (LDivert 1) (namedAfter t11)
  t13 <- checkedNamedFire nameEq keyEq (LUnload 1) (namedAfter t12)
  t14 <- checkedNamedFire nameEq keyEq (LLeave 2) (namedAfter t13)
  t15 <- checkedNamedFire nameEq keyEq (LUnload 2) (namedAfter t14)
  t16 <- checkedNamedFire nameEq keyEq (LUnload 0) (namedAfter t15)
  t17 <- checkedNamedFire nameEq keyEq (ORemove 0) (namedAfter t16)
  t18 <- checkedNamedFire nameEq keyEq
    (OInsert 3 Root DGamma.CalculusChecks.providerComponent) (namedAfter t17)
  t19 <- checkedNamedFire nameEq keyEq (LBegin 3) (namedAfter t18)
  t20 <- checkedNamedFire nameEq keyEq (LAdvance 3) (namedAfter t19)
  t21 <- checkedNamedFire nameEq keyEq (LAdvance 3) (namedAfter t20)
  t22 <- checkedNamedFire nameEq keyEq (LBegin 1) (namedAfter t21)
  t23 <- checkedNamedFire nameEq keyEq (OInsert 4 (ChildOf 1) child) (namedAfter t22)
  t24 <- checkedNamedFire nameEq keyEq (LAdvance 1) (namedAfter t23)
  t25 <- checkedNamedFire nameEq keyEq (LBegin 4) (namedAfter t24)
  t26 <- checkedNamedFire nameEq keyEq (LAdvance 4) (namedAfter t25)
  childSource <- findEpisodeChildSource 2 (namedAfter t8)
  retireSource <- findEpisodeRootSource 0 (namedAfter t9)
  removeSource <- findEpisodeRootSource 0 (namedAfter t16)
  Just (MkVestigialLeft27 common t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 childSource retireSource
    removeSource)

left27Tail27 : (left : VestigialLeft27) ->
  Transitions (namedAfter (finishSurvivor27 left)) (namedAfter (finishSurvivor27 left))
left27Tail27 left = NoTransitions

left27Tail26 : (left : VestigialLeft27) ->
  Transitions (namedAfter (beginSurvivor27 left)) (namedAfter (finishSurvivor27 left))
left27Tail26 left = MoreTransitions (namedTransition (finishSurvivor27 left))
  (left27Tail27 left)

left27Tail25 : (left : VestigialLeft27) ->
  Transitions (namedAfter (finishParent27 left)) (namedAfter (finishSurvivor27 left))
left27Tail25 left = MoreTransitions (namedTransition (beginSurvivor27 left))
  (left27Tail26 left)

left27Tail24 : (left : VestigialLeft27) ->
  Transitions (namedAfter (insertSurvivor27 left)) (namedAfter (finishSurvivor27 left))
left27Tail24 left = MoreTransitions (namedTransition (finishParent27 left))
  (left27Tail25 left)

left27Tail23 : (left : VestigialLeft27) ->
  Transitions (namedAfter (reopenParent27 left)) (namedAfter (finishSurvivor27 left))
left27Tail23 left = MoreTransitions (namedTransition (insertSurvivor27 left))
  (left27Tail24 left)

left27Tail22 : (left : VestigialLeft27) ->
  Transitions (namedAfter (advanceReplacement27b left)) (namedAfter (finishSurvivor27 left))
left27Tail22 left = MoreTransitions (namedTransition (reopenParent27 left))
  (left27Tail23 left)

left27Tail21 : (left : VestigialLeft27) ->
  Transitions (namedAfter (advanceReplacement27a left)) (namedAfter (finishSurvivor27 left))
left27Tail21 left = MoreTransitions (namedTransition (advanceReplacement27b left))
  (left27Tail22 left)

left27Tail20 : (left : VestigialLeft27) ->
  Transitions (namedAfter (beginReplacement27 left)) (namedAfter (finishSurvivor27 left))
left27Tail20 left = MoreTransitions (namedTransition (advanceReplacement27a left))
  (left27Tail21 left)

left27Tail19 : (left : VestigialLeft27) ->
  Transitions (namedAfter (insertReplacement27 left)) (namedAfter (finishSurvivor27 left))
left27Tail19 left = MoreTransitions (namedTransition (beginReplacement27 left))
  (left27Tail20 left)

left27Tail18 : (left : VestigialLeft27) ->
  Transitions (namedAfter (removeProvider27 left)) (namedAfter (finishSurvivor27 left))
left27Tail18 left = MoreTransitions (namedTransition (insertReplacement27 left))
  (left27Tail19 left)

left27Tail17 : (left : VestigialLeft27) ->
  Transitions (namedAfter (unloadProvider27 left)) (namedAfter (finishSurvivor27 left))
left27Tail17 left = MoreTransitions (namedTransition (removeProvider27 left))
  (left27Tail18 left)

left27Tail16 : (left : VestigialLeft27) ->
  Transitions (namedAfter (unloadDeleted27 left)) (namedAfter (finishSurvivor27 left))
left27Tail16 left = MoreTransitions (namedTransition (unloadProvider27 left))
  (left27Tail17 left)

left27Tail15 : (left : VestigialLeft27) ->
  Transitions (namedAfter (leaveDeleted27 left)) (namedAfter (finishSurvivor27 left))
left27Tail15 left = MoreTransitions (namedTransition (unloadDeleted27 left))
  (left27Tail16 left)

left27Tail14 : (left : VestigialLeft27) ->
  Transitions (namedAfter (unloadParent27 left)) (namedAfter (finishSurvivor27 left))
left27Tail14 left = MoreTransitions (namedTransition (leaveDeleted27 left))
  (left27Tail15 left)

left27Tail13 : (left : VestigialLeft27) ->
  Transitions (namedAfter (divertParent27 left)) (namedAfter (finishSurvivor27 left))
left27Tail13 left = MoreTransitions (namedTransition (unloadParent27 left))
  (left27Tail14 left)

left27Tail12 : (left : VestigialLeft27) ->
  Transitions (namedAfter (leaveProvider27 left)) (namedAfter (finishSurvivor27 left))
left27Tail12 left = MoreTransitions (namedTransition (divertParent27 left))
  (left27Tail13 left)

left27Tail11 : (left : VestigialLeft27) ->
  Transitions (namedAfter (retireProvider27 left)) (namedAfter (finishSurvivor27 left))
left27Tail11 left = MoreTransitions (namedTransition (leaveProvider27 left))
  (left27Tail12 left)

left27Tail10 : (left : VestigialLeft27) ->
  Transitions (namedAfter (retireDeleted27 left)) (namedAfter (finishSurvivor27 left))
left27Tail10 left = MoreTransitions (namedTransition (retireProvider27 left))
  (left27Tail11 left)

left27Tail9 : (left : VestigialLeft27) ->
  Transitions (namedAfter (finishDeleted27 left)) (namedAfter (finishSurvivor27 left))
left27Tail9 left = MoreTransitions (namedTransition (retireDeleted27 left))
  (left27Tail10 left)

left27Tail8 : (left : VestigialLeft27) ->
  Transitions (namedAfter (beginDeleted27 left)) (namedAfter (finishSurvivor27 left))
left27Tail8 left = MoreTransitions (namedTransition (finishDeleted27 left))
  (left27Tail9 left)

left27Tail7 : (left : VestigialLeft27) ->
  Transitions (namedAfter (insertDeleted27 left)) (namedAfter (finishSurvivor27 left))
left27Tail7 left = MoreTransitions (namedTransition (beginDeleted27 left))
  (left27Tail8 left)

left27Tail6 : (left : VestigialLeft27) ->
  Transitions (namedAfter (beginParent27 left)) (namedAfter (finishSurvivor27 left))
left27Tail6 left = MoreTransitions (namedTransition (insertDeleted27 left))
  (left27Tail7 left)

left27Tail5 : (left : VestigialLeft27) ->
  Transitions (namedAfter (episodeAdvance0b (common27 left))) (namedAfter (finishSurvivor27 left))
left27Tail5 left = MoreTransitions (namedTransition (beginParent27 left))
  (left27Tail6 left)

public export
vestigialLeft27Trace : (left : VestigialLeft27) ->
  Transitions DGamma.CalculusChecks.initialSystem (namedAfter (finishSurvivor27 left))
vestigialLeft27Trace left = appendTransitions (commonTrace (common27 left))
  (left27Tail5 left)

public export
vestigial27RuntimeCheck : Bool
vestigial27RuntimeCheck =
  case (buildEpisodeCommonPrefix, buildEpisodeCommonPrefix) of
    (Just leftCommon, Just rightCommon) =>
      case (buildVestigialLeft27 leftCommon, buildEpisodeRightTrace rightCommon) of
        (Just left, Just right) =>
          let leftFinal = namedAfter (finishSurvivor27 left)
              rightFinal = namedAfter (rightFinish4 right) in
            quiet @{nameEq} @{keyEq} leftFinal &&
            quiet @{nameEq} @{keyEq} rightFinal &&
            noFailedFibers leftFinal && noFailedFibers rightFinal &&
            isSupported @{nameEq} @{keyEq} 1 leftFinal &&
            isSupported @{nameEq} @{keyEq} 3 leftFinal &&
            isSupported @{nameEq} @{keyEq} 4 leftFinal &&
            not (isSupported @{nameEq} @{keyEq} 2 leftFinal) &&
            isSupported @{nameEq} @{keyEq} 1 rightFinal &&
            isSupported @{nameEq} @{keyEq} 3 rightFinal &&
            isSupported @{nameEq} @{keyEq} 4 rightFinal
        _ => False
    _ => False

swapNineEighteen : Nat -> Nat
swapNineEighteen 0 = 0
swapNineEighteen 1 = 1
swapNineEighteen 2 = 2
swapNineEighteen 3 = 3
swapNineEighteen 4 = 4
swapNineEighteen 5 = 5
swapNineEighteen 6 = 6
swapNineEighteen 7 = 7
swapNineEighteen 8 = 8
swapNineEighteen 9 = 18
swapNineEighteen 10 = 10
swapNineEighteen 11 = 11
swapNineEighteen 12 = 12
swapNineEighteen 13 = 13
swapNineEighteen 14 = 14
swapNineEighteen 15 = 15
swapNineEighteen 16 = 16
swapNineEighteen 17 = 17
swapNineEighteen 18 = 9
swapNineEighteen (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S later))))))))))))))))))) = (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S later)))))))))))))))))))

0 swapNineEighteenInvolutive : (n : Nat) ->
  swapNineEighteen (swapNineEighteen n) = n
swapNineEighteenInvolutive 0 = Refl
swapNineEighteenInvolutive 1 = Refl
swapNineEighteenInvolutive 2 = Refl
swapNineEighteenInvolutive 3 = Refl
swapNineEighteenInvolutive 4 = Refl
swapNineEighteenInvolutive 5 = Refl
swapNineEighteenInvolutive 6 = Refl
swapNineEighteenInvolutive 7 = Refl
swapNineEighteenInvolutive 8 = Refl
swapNineEighteenInvolutive 9 = Refl
swapNineEighteenInvolutive 10 = Refl
swapNineEighteenInvolutive 11 = Refl
swapNineEighteenInvolutive 12 = Refl
swapNineEighteenInvolutive 13 = Refl
swapNineEighteenInvolutive 14 = Refl
swapNineEighteenInvolutive 15 = Refl
swapNineEighteenInvolutive 16 = Refl
swapNineEighteenInvolutive 17 = Refl
swapNineEighteenInvolutive 18 = Refl
swapNineEighteenInvolutive (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S later))))))))))))))))))) = Refl

swapFourteenTwentyThree : Nat -> Nat
swapFourteenTwentyThree 0 = 0
swapFourteenTwentyThree 1 = 1
swapFourteenTwentyThree 2 = 2
swapFourteenTwentyThree 3 = 3
swapFourteenTwentyThree 4 = 4
swapFourteenTwentyThree 5 = 5
swapFourteenTwentyThree 6 = 6
swapFourteenTwentyThree 7 = 7
swapFourteenTwentyThree 8 = 8
swapFourteenTwentyThree 9 = 9
swapFourteenTwentyThree 10 = 10
swapFourteenTwentyThree 11 = 11
swapFourteenTwentyThree 12 = 12
swapFourteenTwentyThree 13 = 13
swapFourteenTwentyThree 14 = 23
swapFourteenTwentyThree 15 = 15
swapFourteenTwentyThree 16 = 16
swapFourteenTwentyThree 17 = 17
swapFourteenTwentyThree 18 = 18
swapFourteenTwentyThree 19 = 19
swapFourteenTwentyThree 20 = 20
swapFourteenTwentyThree 21 = 21
swapFourteenTwentyThree 22 = 22
swapFourteenTwentyThree 23 = 14
swapFourteenTwentyThree (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S later)))))))))))))))))))))))) = (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S later))))))))))))))))))))))))

0 swapFourteenTwentyThreeInvolutive : (n : Nat) ->
  swapFourteenTwentyThree (swapFourteenTwentyThree n) = n
swapFourteenTwentyThreeInvolutive 0 = Refl
swapFourteenTwentyThreeInvolutive 1 = Refl
swapFourteenTwentyThreeInvolutive 2 = Refl
swapFourteenTwentyThreeInvolutive 3 = Refl
swapFourteenTwentyThreeInvolutive 4 = Refl
swapFourteenTwentyThreeInvolutive 5 = Refl
swapFourteenTwentyThreeInvolutive 6 = Refl
swapFourteenTwentyThreeInvolutive 7 = Refl
swapFourteenTwentyThreeInvolutive 8 = Refl
swapFourteenTwentyThreeInvolutive 9 = Refl
swapFourteenTwentyThreeInvolutive 10 = Refl
swapFourteenTwentyThreeInvolutive 11 = Refl
swapFourteenTwentyThreeInvolutive 12 = Refl
swapFourteenTwentyThreeInvolutive 13 = Refl
swapFourteenTwentyThreeInvolutive 14 = Refl
swapFourteenTwentyThreeInvolutive 15 = Refl
swapFourteenTwentyThreeInvolutive 16 = Refl
swapFourteenTwentyThreeInvolutive 17 = Refl
swapFourteenTwentyThreeInvolutive 18 = Refl
swapFourteenTwentyThreeInvolutive 19 = Refl
swapFourteenTwentyThreeInvolutive 20 = Refl
swapFourteenTwentyThreeInvolutive 21 = Refl
swapFourteenTwentyThreeInvolutive 22 = Refl
swapFourteenTwentyThreeInvolutive 23 = Refl
swapFourteenTwentyThreeInvolutive (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S later)))))))))))))))))))))))) = Refl

vestigial27GenerationMap : RegistrationGeneration Nat -> RegistrationGeneration Nat
vestigial27GenerationMap (MkRegistrationGeneration 3 ordinal) =
  MkRegistrationGeneration 3 (swapNineEighteen ordinal)
vestigial27GenerationMap (MkRegistrationGeneration 4 ordinal) =
  MkRegistrationGeneration 4 (swapFourteenTwentyThree ordinal)
vestigial27GenerationMap generation = generation

0 vestigial27GenerationMapInvolutive : (generation : RegistrationGeneration Nat) ->
  vestigial27GenerationMap (vestigial27GenerationMap generation) = generation
vestigial27GenerationMapInvolutive (MkRegistrationGeneration 0 ordinal) = Refl
vestigial27GenerationMapInvolutive (MkRegistrationGeneration 1 ordinal) = Refl
vestigial27GenerationMapInvolutive (MkRegistrationGeneration 2 ordinal) = Refl
vestigial27GenerationMapInvolutive (MkRegistrationGeneration 3 ordinal) =
  cong (MkRegistrationGeneration 3) (swapNineEighteenInvolutive ordinal)
vestigial27GenerationMapInvolutive (MkRegistrationGeneration 4 ordinal) =
  cong (MkRegistrationGeneration 4) (swapFourteenTwentyThreeInvolutive ordinal)
vestigial27GenerationMapInvolutive
  (MkRegistrationGeneration (S (S (S (S (S later))))) ordinal) = Refl

public export
vestigial27GenerationBijection : RegistrationGenerationBijection Nat
vestigial27GenerationBijection = MkRegistrationGenerationBijection
  vestigial27GenerationMap vestigial27GenerationMap
  vestigial27GenerationMapInvolutive vestigial27GenerationMapInvolutive

left27DeletedIndex : RegistrationIndexState Nat
left27DeletedIndex = indexAdvance 5 (LBegin 1) commonIndex

left27SurvivingIndex : RegistrationIndexState Nat
left27SurvivingIndex =
  let i6 = indexDelete 6 2 1 child left27DeletedIndex
      i7 = indexAdvance 7 (LBegin 2) i6
      i8 = indexAdvance 8 (LAdvance 2) i7
      i9 = indexAdvance 9 (ORetire 2) i8
      i10 = indexAdvance 10 (ORetire 0) i9
      i11 = indexAdvance 11 (LLeave 0) i10
      i12 = indexAdvance 12 (LDivert 1) i11
      i13 = indexAdvance 13 (LUnload 1) i12
      i14 = indexAdvance 14 (LLeave 2) i13
      i15 = indexAdvance 15 (LUnload 2) i14
      i16 = indexAdvance 16 (LUnload 0) i15
      i17 = indexAdvance 17 (ORemove 0) i16
      i18 = indexAdvance 18
        (OInsert 3 Root DGamma.CalculusChecks.providerComponent) i17
      i19 = indexAdvance 19 (LBegin 3) i18
      i20 = indexAdvance 20 (LAdvance 3) i19
      i21 = indexAdvance 21 (LAdvance 3) i20 in
    indexAdvance 22 (LBegin 1) i21

left27FinalIndex : RegistrationIndexState Nat
left27FinalIndex =
  let i23 = indexSurvive 23 4 1 child left27SurvivingIndex
      i24 = indexAdvance 24 (LAdvance 1) i23
      i25 = indexAdvance 25 (LBegin 4) i24 in
    indexAdvance 26 (LAdvance 4) i25

0 deleted27Closes : (left : VestigialLeft27) ->
  ActionOccurs (LUnload 1) (left27Tail7 left)
deleted27Closes left =
  ActionOccursLater (namedTransition (beginDeleted27 left)) (left27Tail8 left)
  (ActionOccursLater (namedTransition (finishDeleted27 left)) (left27Tail9 left)
  (ActionOccursLater (namedTransition (retireDeleted27 left)) (left27Tail10 left)
  (ActionOccursLater (namedTransition (retireProvider27 left)) (left27Tail11 left)
  (ActionOccursLater (namedTransition (leaveProvider27 left)) (left27Tail12 left)
  (ActionOccursLater (namedTransition (divertParent27 left)) (left27Tail13 left)
  (ActionOccursHere (namedTransition (unloadParent27 left)) (left27Tail14 left)
    (namedAction (unloadParent27 left))))))))

0 deleted27Classification : (left : VestigialLeft27) ->
  DeletedClosingRegistration
    (registrationEventAt @{DGamma.CP3VestigialChecks.nameEq} 6
      DGamma.CP3VestigialChecks.left27DeletedIndex 2 1
      DGamma.CP3VestigialChecks.child)
    (left27Tail7 left)
deleted27Classification left = MkDeletedClosingRegistration
  (MkRegistrationActivation (MkRegistrationGeneration 1 1) 5) Refl
  (deleted27Closes left)

0 surviving27Open : (left : VestigialLeft27) ->
  NoParentUnload 1 (left27Tail24 left)
surviving27Open left =
  NoParentUnloadStep (namedTransition (finishParent27 left)) (left27Tail25 left)
    (\same => case trans (sym (namedAction (finishParent27 left))) same of Refl impossible)
  (NoParentUnloadStep (namedTransition (beginSurvivor27 left)) (left27Tail26 left)
    (\same => case trans (sym (namedAction (beginSurvivor27 left))) same of Refl impossible)
  (NoParentUnloadStep (namedTransition (finishSurvivor27 left)) (left27Tail27 left)
    (\same => case trans (sym (namedAction (finishSurvivor27 left))) same of Refl impossible)
    NoParentUnloadEnd))

0 surviving27Classification : (left : VestigialLeft27) ->
  SurvivingRegistration
    (registrationEventAt @{DGamma.CP3VestigialChecks.nameEq} 23
      DGamma.CP3VestigialChecks.left27SurvivingIndex 4 1
      DGamma.CP3VestigialChecks.child)
    (left27Tail24 left)
surviving27Classification left = MkSurvivingRegistration
  (MkRegistrationActivation (MkRegistrationGeneration 1 1) 22) Refl
  (surviving27Open left)

left27Tail4 : (left : VestigialLeft27) ->
  Transitions (namedAfter (episodeAdvance0a (common27 left)))
    (namedAfter (finishSurvivor27 left))
left27Tail4 left = MoreTransitions
  (namedTransition (episodeAdvance0b (common27 left))) (left27Tail5 left)

left27Tail3 : (left : VestigialLeft27) ->
  Transitions (namedAfter (episodeBegin0 (common27 left)))
    (namedAfter (finishSurvivor27 left))
left27Tail3 left = MoreTransitions
  (namedTransition (episodeAdvance0a (common27 left))) (left27Tail4 left)

left27Tail2 : (left : VestigialLeft27) ->
  Transitions (namedAfter (episodeInsert1 (common27 left)))
    (namedAfter (finishSurvivor27 left))
left27Tail2 left = MoreTransitions
  (namedTransition (episodeBegin0 (common27 left))) (left27Tail3 left)

left27Tail1 : (left : VestigialLeft27) ->
  Transitions (namedAfter (episodeInsert0 (common27 left)))
    (namedAfter (finishSurvivor27 left))
left27Tail1 left = MoreTransitions
  (namedTransition (episodeInsert1 (common27 left))) (left27Tail2 left)

0 vestigial27TraceCorrespondence :
  (left : VestigialLeft27) -> (right : EpisodeRightTrace) ->
  RegistrationTraceCorrespondence DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.vestigial27GenerationBijection
    0 DGamma.CP3.emptyRegistrationIndex (vestigialLeft27Trace left)
      DGamma.CP3VestigialChecks.left27FinalIndex
    0 DGamma.CP3.emptyRegistrationIndex (episodeRightTrace right)
      DGamma.CP3VestigialChecks.rightFinalIndex [] []
vestigial27TraceCorrespondence left right =
  SkipLeftNonRegistration (OInsert 0 Root DGamma.CalculusChecks.providerComponent) (namedTransition (episodeInsert0 (common27 left))) (left27Tail1 left) (namedAction (episodeInsert0 (common27 left))) Refl
  (SkipLeftNonRegistration (OInsert 1 Root parent) (namedTransition (episodeInsert1 (common27 left))) (left27Tail2 left) (namedAction (episodeInsert1 (common27 left))) Refl
  (SkipLeftNonRegistration (LBegin 0) (namedTransition (episodeBegin0 (common27 left))) (left27Tail3 left) (namedAction (episodeBegin0 (common27 left))) Refl
  (SkipLeftNonRegistration (LAdvance 0) (namedTransition (episodeAdvance0a (common27 left))) (left27Tail4 left) (namedAction (episodeAdvance0a (common27 left))) Refl
  (SkipLeftNonRegistration (LAdvance 0) (namedTransition (episodeAdvance0b (common27 left))) (left27Tail5 left) (namedAction (episodeAdvance0b (common27 left))) Refl
  (SkipLeftNonRegistration (LBegin 1) (namedTransition (beginParent27 left)) (left27Tail6 left) (namedAction (beginParent27 left)) Refl
  (DiscardLeftDeletedRegistration (namedTransition (insertDeleted27 left)) (left27Tail7 left) (namedAction (insertDeleted27 left)) (deleted27Classification left)
  (SkipLeftNonRegistration (LBegin 2) (namedTransition (beginDeleted27 left)) (left27Tail8 left) (namedAction (beginDeleted27 left)) Refl
  (SkipLeftNonRegistration (LAdvance 2) (namedTransition (finishDeleted27 left)) (left27Tail9 left) (namedAction (finishDeleted27 left)) Refl
  (SkipLeftNonRegistration (ORetire 2) (namedTransition (retireDeleted27 left)) (left27Tail10 left) (namedAction (retireDeleted27 left)) Refl
  (SkipLeftNonRegistration (ORetire 0) (namedTransition (retireProvider27 left)) (left27Tail11 left) (namedAction (retireProvider27 left)) Refl
  (SkipLeftNonRegistration (LLeave 0) (namedTransition (leaveProvider27 left)) (left27Tail12 left) (namedAction (leaveProvider27 left)) Refl
  (SkipLeftNonRegistration (LDivert 1) (namedTransition (divertParent27 left)) (left27Tail13 left) (namedAction (divertParent27 left)) Refl
  (SkipLeftNonRegistration (LUnload 1) (namedTransition (unloadParent27 left)) (left27Tail14 left) (namedAction (unloadParent27 left)) Refl
  (SkipLeftNonRegistration (LLeave 2) (namedTransition (leaveDeleted27 left)) (left27Tail15 left) (namedAction (leaveDeleted27 left)) Refl
  (SkipLeftNonRegistration (LUnload 2) (namedTransition (unloadDeleted27 left)) (left27Tail16 left) (namedAction (unloadDeleted27 left)) Refl
  (SkipLeftNonRegistration (LUnload 0) (namedTransition (unloadProvider27 left)) (left27Tail17 left) (namedAction (unloadProvider27 left)) Refl
  (SkipLeftNonRegistration (ORemove 0) (namedTransition (removeProvider27 left)) (left27Tail18 left) (namedAction (removeProvider27 left)) Refl
  (SkipLeftNonRegistration (OInsert 3 Root DGamma.CalculusChecks.providerComponent) (namedTransition (insertReplacement27 left)) (left27Tail19 left) (namedAction (insertReplacement27 left)) Refl
  (SkipLeftNonRegistration (LBegin 3) (namedTransition (beginReplacement27 left)) (left27Tail20 left) (namedAction (beginReplacement27 left)) Refl
  (SkipLeftNonRegistration (LAdvance 3) (namedTransition (advanceReplacement27a left)) (left27Tail21 left) (namedAction (advanceReplacement27a left)) Refl
  (SkipLeftNonRegistration (LAdvance 3) (namedTransition (advanceReplacement27b left)) (left27Tail22 left) (namedAction (advanceReplacement27b left)) Refl
  (SkipLeftNonRegistration (LBegin 1) (namedTransition (reopenParent27 left)) (left27Tail23 left) (namedAction (reopenParent27 left)) Refl
  (QueueLeftGeneratedRegistration (namedTransition (insertSurvivor27 left)) (left27Tail24 left) (namedAction (insertSurvivor27 left)) (surviving27Classification left)
  (SkipLeftNonRegistration (LAdvance 1) (namedTransition (finishParent27 left)) (left27Tail25 left) (namedAction (finishParent27 left)) Refl
  (SkipLeftNonRegistration (LBegin 4) (namedTransition (beginSurvivor27 left)) (left27Tail26 left) (namedAction (beginSurvivor27 left)) Refl
  (SkipLeftNonRegistration (LAdvance 4) (namedTransition (finishSurvivor27 left)) (left27Tail27 left) (namedAction (finishSurvivor27 left)) Refl
  (SkipRightNonRegistration (OInsert 0 Root DGamma.CalculusChecks.providerComponent) (namedTransition (episodeInsert0 (rightEpisodePrefix right))) (episodeRightTail1 right) (namedAction (episodeInsert0 (rightEpisodePrefix right))) Refl
  (SkipRightNonRegistration (OInsert 1 Root parent) (namedTransition (episodeInsert1 (rightEpisodePrefix right))) (episodeRightTail2 right) (namedAction (episodeInsert1 (rightEpisodePrefix right))) Refl
  (SkipRightNonRegistration (LBegin 0) (namedTransition (episodeBegin0 (rightEpisodePrefix right))) (episodeRightTail3 right) (namedAction (episodeBegin0 (rightEpisodePrefix right))) Refl
  (SkipRightNonRegistration (LAdvance 0) (namedTransition (episodeAdvance0a (rightEpisodePrefix right))) (episodeRightTail4 right) (namedAction (episodeAdvance0a (rightEpisodePrefix right))) Refl
  (SkipRightNonRegistration (LAdvance 0) (namedTransition (episodeAdvance0b (rightEpisodePrefix right))) (episodeRightTail5 right) (namedAction (episodeAdvance0b (rightEpisodePrefix right))) Refl
  (SkipRightNonRegistration (ORetire 0) (namedTransition (rightRetire0 right)) (episodeRightTail6 right) (namedAction (rightRetire0 right)) Refl
  (SkipRightNonRegistration (LLeave 0) (namedTransition (rightLeave0 right)) (episodeRightTail7 right) (namedAction (rightLeave0 right)) Refl
  (SkipRightNonRegistration (LUnload 0) (namedTransition (rightUnload0 right)) (episodeRightTail8 right) (namedAction (rightUnload0 right)) Refl
  (SkipRightNonRegistration (ORemove 0) (namedTransition (rightRemove0 right)) (episodeRightTail9 right) (namedAction (rightRemove0 right)) Refl
  (SkipRightNonRegistration (OInsert 3 Root DGamma.CalculusChecks.providerComponent) (namedTransition (rightInsert3 right)) (episodeRightTail10 right) (namedAction (rightInsert3 right)) Refl
  (SkipRightNonRegistration (LBegin 3) (namedTransition (rightBegin3 right)) (episodeRightTail11 right) (namedAction (rightBegin3 right)) Refl
  (SkipRightNonRegistration (LAdvance 3) (namedTransition (rightAdvance3a right)) (episodeRightTail12 right) (namedAction (rightAdvance3a right)) Refl
  (SkipRightNonRegistration (LAdvance 3) (namedTransition (rightAdvance3b right)) (episodeRightTail13 right) (namedAction (rightAdvance3b right)) Refl
  (SkipRightNonRegistration (LBegin 1) (namedTransition (rightBegin1 right)) (episodeRightTail14 right) (namedAction (rightBegin1 right)) Refl
  (MatchRightWithPendingLeft (namedTransition (rightSurvivingChild right)) (episodeRightTail15 right) (namedAction (rightSurvivingChild right)) (rightClassification right) [] (registrationEventAt @{DGamma.CP3VestigialChecks.nameEq} 23 DGamma.CP3VestigialChecks.left27SurvivingIndex 4 1 DGamma.CP3VestigialChecks.child) [] (MkRegistrationEventMatch Refl (MkRegistrationActivation (MkRegistrationGeneration 1 1) 22) (MkRegistrationActivation (MkRegistrationGeneration 1 1) 13) Refl Refl Refl Refl Refl)
  (SkipRightNonRegistration (LAdvance 1) (namedTransition (rightFinish1 right)) (episodeRightTail16 right) (namedAction (rightFinish1 right)) Refl
  (SkipRightNonRegistration (LBegin 4) (namedTransition (rightBegin4 right)) (episodeRightTail17 right) (namedAction (rightBegin4 right)) Refl
  (SkipRightNonRegistration (LAdvance 4) (namedTransition (rightFinish4 right)) (episodeRightTail18 right) (namedAction (rightFinish4 right)) Refl
    RegistrationCorrespondenceEnd))))))))))))))))))))))))))))))))))))))))))))

0 vestigial27RegistrationCorrespondence :
  (left : VestigialLeft27) -> (right : EpisodeRightTrace) ->
  RegistrationCorrespondenceByGeneration DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.vestigial27GenerationBijection
    (vestigialLeft27Trace left) (episodeRightTrace right)
vestigial27RegistrationCorrespondence left right =
  MkRegistrationCorrespondenceByGeneration left27FinalIndex rightFinalIndex
    (vestigial27TraceCorrespondence left right)

0 retireChild27Internal : (left : VestigialLeft27) ->
  RootOrchestrationStep DGamma.CP3VestigialChecks.nameEq
    (namedTransition (retireDeleted27 left)) -> Void
retireChild27Internal left = childRetireCannotBeRoot
  DGamma.CP3VestigialChecks.nameEq (namedTransition (retireDeleted27 left))
  (namedAction (retireDeleted27 left))
  (episodeChildFiber (retireChildSource27 left))
  (episodeChildFound (retireChildSource27 left))
  (episodeChildParentRole (retireChildSource27 left))

0 retireProvider27Root : (left : VestigialLeft27) ->
  RootOrchestrationStep DGamma.CP3VestigialChecks.nameEq
    (namedTransition (retireProvider27 left))
retireProvider27Root left = RootRetireStep
  (episodeRootFiber (retireProviderSource27 left))
  (episodeRootFound (retireProviderSource27 left))
  (episodeRootParent (retireProviderSource27 left))
  (namedAction (retireProvider27 left))

0 removeProvider27Root : (left : VestigialLeft27) ->
  RootOrchestrationStep DGamma.CP3VestigialChecks.nameEq
    (namedTransition (removeProvider27 left))
removeProvider27Root left = RootRemoveStep
  (episodeRootFiber (removeProviderSource27 left))
  (episodeRootFound (removeProviderSource27 left))
  (episodeRootParent (removeProviderSource27 left))
  (namedAction (removeProvider27 left))

0 vestigial27SameExternal :
  (left : VestigialLeft27) -> (right : EpisodeRightTrace) ->
  SameExternalOrchestration DGamma.CP3VestigialChecks.nameEq
    (vestigialLeft27Trace left) (episodeRightTrace right)
vestigial27SameExternal left right =
  MatchExternalInput (OInsert 0 Root DGamma.CalculusChecks.providerComponent) (namedTransition (episodeInsert0 (common27 left))) (left27Tail1 left) (RootInsertStep (namedAction (episodeInsert0 (common27 left)))) (namedTransition (episodeInsert0 (rightEpisodePrefix right))) (episodeRightTail1 right) (RootInsertStep (namedAction (episodeInsert0 (rightEpisodePrefix right)))) (namedAction (episodeInsert0 (common27 left))) (namedAction (episodeInsert0 (rightEpisodePrefix right)))
  (MatchExternalInput (OInsert 1 Root parent) (namedTransition (episodeInsert1 (common27 left))) (left27Tail2 left) (RootInsertStep (namedAction (episodeInsert1 (common27 left)))) (namedTransition (episodeInsert1 (rightEpisodePrefix right))) (episodeRightTail2 right) (RootInsertStep (namedAction (episodeInsert1 (rightEpisodePrefix right)))) (namedAction (episodeInsert1 (common27 left))) (namedAction (episodeInsert1 (rightEpisodePrefix right)))
  (SkipLeftInternal (namedTransition (episodeBegin0 (common27 left))) (left27Tail3 left) (namedLifecycleNotRoot (episodeBegin0 (common27 left)) Refl)
  (SkipLeftInternal (namedTransition (episodeAdvance0a (common27 left))) (left27Tail4 left) (namedLifecycleNotRoot (episodeAdvance0a (common27 left)) Refl)
  (SkipLeftInternal (namedTransition (episodeAdvance0b (common27 left))) (left27Tail5 left) (namedLifecycleNotRoot (episodeAdvance0b (common27 left)) Refl)
  (SkipLeftInternal (namedTransition (beginParent27 left)) (left27Tail6 left) (namedLifecycleNotRoot (beginParent27 left) Refl)
  (SkipLeftInternal (namedTransition (insertDeleted27 left)) (left27Tail7 left) (childInsertCannotBeRoot (namedTransition (insertDeleted27 left)) (namedAction (insertDeleted27 left)))
  (SkipLeftInternal (namedTransition (beginDeleted27 left)) (left27Tail8 left) (namedLifecycleNotRoot (beginDeleted27 left) Refl)
  (SkipLeftInternal (namedTransition (finishDeleted27 left)) (left27Tail9 left) (namedLifecycleNotRoot (finishDeleted27 left) Refl)
  (SkipLeftInternal (namedTransition (retireDeleted27 left)) (left27Tail10 left) (retireChild27Internal left)
  (SkipRightInternal (namedTransition (episodeBegin0 (rightEpisodePrefix right))) (episodeRightTail3 right) (namedLifecycleNotRoot (episodeBegin0 (rightEpisodePrefix right)) Refl)
  (SkipRightInternal (namedTransition (episodeAdvance0a (rightEpisodePrefix right))) (episodeRightTail4 right) (namedLifecycleNotRoot (episodeAdvance0a (rightEpisodePrefix right)) Refl)
  (SkipRightInternal (namedTransition (episodeAdvance0b (rightEpisodePrefix right))) (episodeRightTail5 right) (namedLifecycleNotRoot (episodeAdvance0b (rightEpisodePrefix right)) Refl)
  (MatchExternalInput (ORetire 0) (namedTransition (retireProvider27 left)) (left27Tail11 left) (retireProvider27Root left) (namedTransition (rightRetire0 right)) (episodeRightTail6 right) (retireProviderRightRoot right) (namedAction (retireProvider27 left)) (namedAction (rightRetire0 right))
  (SkipLeftInternal (namedTransition (leaveProvider27 left)) (left27Tail12 left) (namedLifecycleNotRoot (leaveProvider27 left) Refl)
  (SkipLeftInternal (namedTransition (divertParent27 left)) (left27Tail13 left) (namedLifecycleNotRoot (divertParent27 left) Refl)
  (SkipLeftInternal (namedTransition (unloadParent27 left)) (left27Tail14 left) (namedLifecycleNotRoot (unloadParent27 left) Refl)
  (SkipLeftInternal (namedTransition (leaveDeleted27 left)) (left27Tail15 left) (namedLifecycleNotRoot (leaveDeleted27 left) Refl)
  (SkipLeftInternal (namedTransition (unloadDeleted27 left)) (left27Tail16 left) (namedLifecycleNotRoot (unloadDeleted27 left) Refl)
  (SkipLeftInternal (namedTransition (unloadProvider27 left)) (left27Tail17 left) (namedLifecycleNotRoot (unloadProvider27 left) Refl)
  (SkipRightInternal (namedTransition (rightLeave0 right)) (episodeRightTail7 right) (namedLifecycleNotRoot (rightLeave0 right) Refl)
  (SkipRightInternal (namedTransition (rightUnload0 right)) (episodeRightTail8 right) (namedLifecycleNotRoot (rightUnload0 right) Refl)
  (MatchExternalInput (ORemove 0) (namedTransition (removeProvider27 left)) (left27Tail18 left) (removeProvider27Root left) (namedTransition (rightRemove0 right)) (episodeRightTail9 right) (removeProviderRightRoot right) (namedAction (removeProvider27 left)) (namedAction (rightRemove0 right))
  (MatchExternalInput (OInsert 3 Root DGamma.CalculusChecks.providerComponent) (namedTransition (insertReplacement27 left)) (left27Tail19 left) (RootInsertStep (namedAction (insertReplacement27 left))) (namedTransition (rightInsert3 right)) (episodeRightTail10 right) (RootInsertStep (namedAction (rightInsert3 right))) (namedAction (insertReplacement27 left)) (namedAction (rightInsert3 right))
  (SkipLeftInternal (namedTransition (beginReplacement27 left)) (left27Tail20 left) (namedLifecycleNotRoot (beginReplacement27 left) Refl)
  (SkipLeftInternal (namedTransition (advanceReplacement27a left)) (left27Tail21 left) (namedLifecycleNotRoot (advanceReplacement27a left) Refl)
  (SkipLeftInternal (namedTransition (advanceReplacement27b left)) (left27Tail22 left) (namedLifecycleNotRoot (advanceReplacement27b left) Refl)
  (SkipLeftInternal (namedTransition (reopenParent27 left)) (left27Tail23 left) (namedLifecycleNotRoot (reopenParent27 left) Refl)
  (SkipLeftInternal (namedTransition (insertSurvivor27 left)) (left27Tail24 left) (childInsertCannotBeRoot (namedTransition (insertSurvivor27 left)) (namedAction (insertSurvivor27 left)))
  (SkipLeftInternal (namedTransition (finishParent27 left)) (left27Tail25 left) (namedLifecycleNotRoot (finishParent27 left) Refl)
  (SkipLeftInternal (namedTransition (beginSurvivor27 left)) (left27Tail26 left) (namedLifecycleNotRoot (beginSurvivor27 left) Refl)
  (SkipLeftInternal (namedTransition (finishSurvivor27 left)) (left27Tail27 left) (namedLifecycleNotRoot (finishSurvivor27 left) Refl)
  (SkipRightInternal (namedTransition (rightBegin3 right)) (episodeRightTail11 right) (namedLifecycleNotRoot (rightBegin3 right) Refl)
  (SkipRightInternal (namedTransition (rightAdvance3a right)) (episodeRightTail12 right) (namedLifecycleNotRoot (rightAdvance3a right) Refl)
  (SkipRightInternal (namedTransition (rightAdvance3b right)) (episodeRightTail13 right) (namedLifecycleNotRoot (rightAdvance3b right) Refl)
  (SkipRightInternal (namedTransition (rightBegin1 right)) (episodeRightTail14 right) (namedLifecycleNotRoot (rightBegin1 right) Refl)
  (SkipRightInternal (namedTransition (rightSurvivingChild right)) (episodeRightTail15 right) (childInsertCannotBeRoot (namedTransition (rightSurvivingChild right)) (namedAction (rightSurvivingChild right)))
  (SkipRightInternal (namedTransition (rightFinish1 right)) (episodeRightTail16 right) (namedLifecycleNotRoot (rightFinish1 right) Refl)
  (SkipRightInternal (namedTransition (rightBegin4 right)) (episodeRightTail17 right) (namedLifecycleNotRoot (rightBegin4 right) Refl)
  (SkipRightInternal (namedTransition (rightFinish4 right)) (episodeRightTail18 right) (namedLifecycleNotRoot (rightFinish4 right) Refl)
    SameExternalOrchestrationEnd)))))))))))))))))))))))))))))))))))))))
0 vestigial27ExternalRoots :
  (left : VestigialLeft27) -> (right : EpisodeRightTrace) ->
  ExternalRootBirthCorrespondence
    DGamma.CP3VestigialChecks.vestigial27GenerationBijection 0
    (vestigialLeft27Trace left) 0 (episodeRightTrace right)
vestigial27ExternalRoots left right =
  MatchExternalRootBirth (namedTransition (episodeInsert0 (common27 left))) (left27Tail1 left) (namedTransition (episodeInsert0 (rightEpisodePrefix right))) (episodeRightTail1 right) (namedAction (episodeInsert0 (common27 left))) (namedAction (episodeInsert0 (rightEpisodePrefix right))) Refl
  (MatchExternalRootBirth (namedTransition (episodeInsert1 (common27 left))) (left27Tail2 left) (namedTransition (episodeInsert1 (rightEpisodePrefix right))) (episodeRightTail2 right) (namedAction (episodeInsert1 (common27 left))) (namedAction (episodeInsert1 (rightEpisodePrefix right))) Refl
  (SkipLeftNonExternalRootBirth (LBegin 0) (namedTransition (episodeBegin0 (common27 left))) (left27Tail3 left) (namedAction (episodeBegin0 (common27 left))) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 0) (namedTransition (episodeAdvance0a (common27 left))) (left27Tail4 left) (namedAction (episodeAdvance0a (common27 left))) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 0) (namedTransition (episodeAdvance0b (common27 left))) (left27Tail5 left) (namedAction (episodeAdvance0b (common27 left))) Refl
  (SkipLeftNonExternalRootBirth (LBegin 1) (namedTransition (beginParent27 left)) (left27Tail6 left) (namedAction (beginParent27 left)) Refl
  (SkipLeftNonExternalRootBirth (OInsert 2 (ChildOf 1) child) (namedTransition (insertDeleted27 left)) (left27Tail7 left) (namedAction (insertDeleted27 left)) Refl
  (SkipLeftNonExternalRootBirth (LBegin 2) (namedTransition (beginDeleted27 left)) (left27Tail8 left) (namedAction (beginDeleted27 left)) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 2) (namedTransition (finishDeleted27 left)) (left27Tail9 left) (namedAction (finishDeleted27 left)) Refl
  (SkipLeftNonExternalRootBirth (ORetire 2) (namedTransition (retireDeleted27 left)) (left27Tail10 left) (namedAction (retireDeleted27 left)) Refl
  (SkipLeftNonExternalRootBirth (ORetire 0) (namedTransition (retireProvider27 left)) (left27Tail11 left) (namedAction (retireProvider27 left)) Refl
  (SkipLeftNonExternalRootBirth (LLeave 0) (namedTransition (leaveProvider27 left)) (left27Tail12 left) (namedAction (leaveProvider27 left)) Refl
  (SkipLeftNonExternalRootBirth (LDivert 1) (namedTransition (divertParent27 left)) (left27Tail13 left) (namedAction (divertParent27 left)) Refl
  (SkipLeftNonExternalRootBirth (LUnload 1) (namedTransition (unloadParent27 left)) (left27Tail14 left) (namedAction (unloadParent27 left)) Refl
  (SkipLeftNonExternalRootBirth (LLeave 2) (namedTransition (leaveDeleted27 left)) (left27Tail15 left) (namedAction (leaveDeleted27 left)) Refl
  (SkipLeftNonExternalRootBirth (LUnload 2) (namedTransition (unloadDeleted27 left)) (left27Tail16 left) (namedAction (unloadDeleted27 left)) Refl
  (SkipLeftNonExternalRootBirth (LUnload 0) (namedTransition (unloadProvider27 left)) (left27Tail17 left) (namedAction (unloadProvider27 left)) Refl
  (SkipLeftNonExternalRootBirth (ORemove 0) (namedTransition (removeProvider27 left)) (left27Tail18 left) (namedAction (removeProvider27 left)) Refl
  (SkipRightNonExternalRootBirth (LBegin 0) (namedTransition (episodeBegin0 (rightEpisodePrefix right))) (episodeRightTail3 right) (namedAction (episodeBegin0 (rightEpisodePrefix right))) Refl
  (SkipRightNonExternalRootBirth (LAdvance 0) (namedTransition (episodeAdvance0a (rightEpisodePrefix right))) (episodeRightTail4 right) (namedAction (episodeAdvance0a (rightEpisodePrefix right))) Refl
  (SkipRightNonExternalRootBirth (LAdvance 0) (namedTransition (episodeAdvance0b (rightEpisodePrefix right))) (episodeRightTail5 right) (namedAction (episodeAdvance0b (rightEpisodePrefix right))) Refl
  (SkipRightNonExternalRootBirth (ORetire 0) (namedTransition (rightRetire0 right)) (episodeRightTail6 right) (namedAction (rightRetire0 right)) Refl
  (SkipRightNonExternalRootBirth (LLeave 0) (namedTransition (rightLeave0 right)) (episodeRightTail7 right) (namedAction (rightLeave0 right)) Refl
  (SkipRightNonExternalRootBirth (LUnload 0) (namedTransition (rightUnload0 right)) (episodeRightTail8 right) (namedAction (rightUnload0 right)) Refl
  (SkipRightNonExternalRootBirth (ORemove 0) (namedTransition (rightRemove0 right)) (episodeRightTail9 right) (namedAction (rightRemove0 right)) Refl
  (MatchExternalRootBirth (namedTransition (insertReplacement27 left)) (left27Tail19 left) (namedTransition (rightInsert3 right)) (episodeRightTail10 right) (namedAction (insertReplacement27 left)) (namedAction (rightInsert3 right)) Refl
  (SkipLeftNonExternalRootBirth (LBegin 3) (namedTransition (beginReplacement27 left)) (left27Tail20 left) (namedAction (beginReplacement27 left)) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 3) (namedTransition (advanceReplacement27a left)) (left27Tail21 left) (namedAction (advanceReplacement27a left)) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 3) (namedTransition (advanceReplacement27b left)) (left27Tail22 left) (namedAction (advanceReplacement27b left)) Refl
  (SkipLeftNonExternalRootBirth (LBegin 1) (namedTransition (reopenParent27 left)) (left27Tail23 left) (namedAction (reopenParent27 left)) Refl
  (SkipLeftNonExternalRootBirth (OInsert 4 (ChildOf 1) child) (namedTransition (insertSurvivor27 left)) (left27Tail24 left) (namedAction (insertSurvivor27 left)) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 1) (namedTransition (finishParent27 left)) (left27Tail25 left) (namedAction (finishParent27 left)) Refl
  (SkipLeftNonExternalRootBirth (LBegin 4) (namedTransition (beginSurvivor27 left)) (left27Tail26 left) (namedAction (beginSurvivor27 left)) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 4) (namedTransition (finishSurvivor27 left)) (left27Tail27 left) (namedAction (finishSurvivor27 left)) Refl
  (SkipRightNonExternalRootBirth (LBegin 3) (namedTransition (rightBegin3 right)) (episodeRightTail11 right) (namedAction (rightBegin3 right)) Refl
  (SkipRightNonExternalRootBirth (LAdvance 3) (namedTransition (rightAdvance3a right)) (episodeRightTail12 right) (namedAction (rightAdvance3a right)) Refl
  (SkipRightNonExternalRootBirth (LAdvance 3) (namedTransition (rightAdvance3b right)) (episodeRightTail13 right) (namedAction (rightAdvance3b right)) Refl
  (SkipRightNonExternalRootBirth (LBegin 1) (namedTransition (rightBegin1 right)) (episodeRightTail14 right) (namedAction (rightBegin1 right)) Refl
  (SkipRightNonExternalRootBirth (OInsert 4 (ChildOf 1) child) (namedTransition (rightSurvivingChild right)) (episodeRightTail15 right) (namedAction (rightSurvivingChild right)) Refl
  (SkipRightNonExternalRootBirth (LAdvance 1) (namedTransition (rightFinish1 right)) (episodeRightTail16 right) (namedAction (rightFinish1 right)) Refl
  (SkipRightNonExternalRootBirth (LBegin 4) (namedTransition (rightBegin4 right)) (episodeRightTail17 right) (namedAction (rightBegin4 right)) Refl
  (SkipRightNonExternalRootBirth (LAdvance 4) (namedTransition (rightFinish4 right)) (episodeRightTail18 right) (namedAction (rightFinish4 right)) Refl
    ExternalRootBirthCorrespondenceEnd)))))))))))))))))))))))))))))))))))))))))

0 left27Current :
  (left : VestigialLeft27) -> (right : EpisodeRightTrace) ->
  VestigialEndpointGeneration Nat ToyKey ToyRuntime String ToyValue
    DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq
    (leftFinalGenerations (vestigial27RegistrationCorrespondence left right))
    (leftDeletedGenerations (vestigial27RegistrationCorrespondence left right))
    2 (namedAfter (finishSurvivor27 left)) ->
  (n : Nat) -> (generation : RegistrationGeneration Nat) ->
  lookupCurrentGeneration @{DGamma.CP3VestigialChecks.nameEq} n
    (leftFinalGenerations (vestigial27RegistrationCorrespondence left right)) =
      Just generation ->
  Either
    (VestigialEndpointGeneration Nat ToyKey ToyRuntime String ToyValue
      DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq
      (leftFinalGenerations (vestigial27RegistrationCorrespondence left right))
      (leftDeletedGenerations (vestigial27RegistrationCorrespondence left right))
      n (namedAfter (finishSurvivor27 left)))
    (rightGeneration : RegistrationGeneration Nat **
      (generationForward DGamma.CP3VestigialChecks.vestigial27GenerationBijection generation = rightGeneration,
       lookupCurrentGeneration @{DGamma.CP3VestigialChecks.nameEq} n
         (rightFinalGenerations (vestigial27RegistrationCorrespondence left right)) =
         Just rightGeneration))
left27Current left right vestigial 0 generation found = void (nothingIsNotJust found)
left27Current left right vestigial 1 generation found =
  case justInjective found of
    Refl => Right (MkRegistrationGeneration 1 1 ** (Refl, Refl))
left27Current left right vestigial 2 generation found = Left vestigial
left27Current left right vestigial 3 generation found =
  case justInjective found of
    Refl => Right (MkRegistrationGeneration 3 9 ** (Refl, Refl))
left27Current left right vestigial 4 generation found =
  case justInjective found of
    Refl => Right (MkRegistrationGeneration 4 14 ** (Refl, Refl))
left27Current left right vestigial (S (S (S (S (S later))))) generation found =
  void (nothingIsNotJust found)

0 right27Current :
  (left : VestigialLeft27) -> (right : EpisodeRightTrace) ->
  (n : Nat) -> (generation : RegistrationGeneration Nat) ->
  lookupCurrentGeneration @{DGamma.CP3VestigialChecks.nameEq} n
    (rightFinalGenerations (vestigial27RegistrationCorrespondence left right)) =
      Just generation ->
  Either
    (VestigialEndpointGeneration Nat ToyKey ToyRuntime String ToyValue
      DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq
      (rightFinalGenerations (vestigial27RegistrationCorrespondence left right))
      (rightDeletedGenerations (vestigial27RegistrationCorrespondence left right))
      n (namedAfter (rightFinish4 right)))
    (leftGeneration : RegistrationGeneration Nat **
      (generationBackward DGamma.CP3VestigialChecks.vestigial27GenerationBijection generation = leftGeneration,
       lookupCurrentGeneration @{DGamma.CP3VestigialChecks.nameEq} n
         (leftFinalGenerations (vestigial27RegistrationCorrespondence left right)) =
         Just leftGeneration))
right27Current left right 0 generation found = void (nothingIsNotJust found)
right27Current left right 1 generation found =
  case justInjective found of
    Refl => Right (MkRegistrationGeneration 1 1 ** (Refl, Refl))
right27Current left right 2 generation found = void (nothingIsNotJust found)
right27Current left right 3 generation found =
  case justInjective found of
    Refl => Right (MkRegistrationGeneration 3 18 ** (Refl, Refl))
right27Current left right 4 generation found =
  case justInjective found of
    Refl => Right (MkRegistrationGeneration 4 23 ** (Refl, Refl))
right27Current left right (S (S (S (S (S later))))) generation found =
  void (nothingIsNotJust found)

0 vestigial27EndpointRenaming :
  (left : VestigialLeft27) -> (right : EpisodeRightTrace) ->
  (vestigial : VestigialEndpointGeneration Nat ToyKey ToyRuntime String ToyValue
    DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq
    (leftFinalGenerations (vestigial27RegistrationCorrespondence left right))
    (leftDeletedGenerations (vestigial27RegistrationCorrespondence left right))
    2 (namedAfter (finishSurvivor27 left))) ->
  CurrentEndpointRenaming DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq DGamma.CP3VestigialChecks.vestigial27GenerationBijection
    (vestigialLeft27Trace left) (episodeRightTrace right)
    (vestigial27RegistrationCorrespondence left right)
vestigial27EndpointRenaming left right vestigial =
  MkCurrentEndpointRenaming identityNameBijection
    (\n, fiber, found, root => Refl)
    (\n, fiber, found, root => Refl)
    (left27Current left right vestigial)
    (right27Current left right)

0 vestigial27SameInputs :
  (left : VestigialLeft27) -> (right : EpisodeRightTrace) ->
  (vestigial : VestigialEndpointGeneration Nat ToyKey ToyRuntime String ToyValue
    DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq
    (leftFinalGenerations (vestigial27RegistrationCorrespondence left right))
    (leftDeletedGenerations (vestigial27RegistrationCorrespondence left right))
    2 (namedAfter (finishSurvivor27 left))) ->
  SameOrchestrationModuloGenerated DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq (vestigialLeft27Trace left)
    (episodeRightTrace right)
vestigial27SameInputs left right vestigial = MkSameOrchestrationModuloGenerated
  DGamma.CP3VestigialChecks.vestigial27GenerationBijection (vestigial27SameExternal left right)
  (vestigial27ExternalRoots left right)
  (vestigial27RegistrationCorrespondence left right)
  (vestigial27EndpointRenaming left right vestigial)

public export
record Vestigial27CorrespondenceWitness where
  constructor MkVestigial27CorrespondenceWitness
  vestigial27Left : VestigialLeft27
  vestigial27Right : EpisodeRightTrace
  0 vestigial27SameInputWitness : SameOrchestrationModuloGenerated
    DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq
    (vestigialLeft27Trace vestigial27Left)
    (episodeRightTrace vestigial27Right)

public export
vestigial27CorrespondenceWitness : Maybe Vestigial27CorrespondenceWitness
vestigial27CorrespondenceWitness = do
  leftCommon <- buildEpisodeCommonPrefix
  rightCommon <- buildEpisodeCommonPrefix
  left <- buildVestigialLeft27 leftCommon
  right <- buildEpisodeRightTrace rightCommon
  vestigial <- vestigialEndpointGeneration DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq
    (indexedLiveGenerations DGamma.CP3VestigialChecks.left27FinalIndex)
    (indexedDeletedGenerations DGamma.CP3VestigialChecks.left27FinalIndex)
    2 (namedAfter (finishSurvivor27 left)) (MkRegistrationGeneration 2 6)
    Refl Here
  Just (MkVestigial27CorrespondenceWitness left right
    (vestigial27SameInputs left right vestigial))

public export
vestigial27CorrespondenceCheck : Bool
vestigial27CorrespondenceCheck = case vestigial27CorrespondenceWitness of
  Nothing => False
  Just witness => True


||| The literal public Theorem-73 boundary for the 27/18 reviewer pair. Every
||| semantic premise is retained; the projection reaches the new outside-R
||| endpoint relation rather than an exact-domain shadow conclusion.
public export
0 vestigial27Theorem73PremiseChain :
  confluenceTheorem Nat ToyKey ToyValue ToyRuntime String ->
  (protocol : RegistrationProtocol ToyKey ToyValue ToyRuntime String) ->
  (0 witness : Vestigial27CorrespondenceWitness) ->
  AlignedTransitions Nat ToyKey ToyRuntime String ToyValue DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq
    (vestigialLeft27Trace (vestigial27Left witness)) ->
  AlignedTransitions Nat ToyKey ToyRuntime String ToyValue DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq
    (episodeRightTrace (vestigial27Right witness)) ->
  RegistrationDiscipline protocol DGamma.CP3VestigialChecks.nameEq
    (vestigialLeft27Trace (vestigial27Left witness)) ->
  RegistrationDiscipline protocol DGamma.CP3VestigialChecks.nameEq
    (episodeRightTrace (vestigial27Right witness)) ->
  registryWellFormed @{DGamma.CP3VestigialChecks.nameEq} @{DGamma.CP3VestigialChecks.keyEq}
    DGamma.CalculusChecks.initialSystem = True ->
  bindings (registry DGamma.CalculusChecks.initialSystem) = [] ->
  quiet @{DGamma.CP3VestigialChecks.nameEq} @{DGamma.CP3VestigialChecks.keyEq}
    (namedAfter (finishSurvivor27 (vestigial27Left witness))) = True ->
  quiet @{DGamma.CP3VestigialChecks.nameEq} @{DGamma.CP3VestigialChecks.keyEq}
    (namedAfter (rightFinish4 (vestigial27Right witness))) = True ->
  noFailedFibers
    (namedAfter (finishSurvivor27 (vestigial27Left witness))) = True ->
  noFailedFibers
    (namedAfter (rightFinish4 (vestigial27Right witness))) = True ->
  TraceComponentsTotal DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq
    (vestigialLeft27Trace (vestigial27Left witness)) ->
  TraceComponentsTotal DGamma.CP3VestigialChecks.nameEq
    DGamma.CP3VestigialChecks.keyEq
    (episodeRightTrace (vestigial27Right witness)) ->
  TraceIndependent Nat ToyKey ToyRuntime String ToyValue DGamma.CP3VestigialChecks.keyEq
    (vestigialLeft27Trace (vestigial27Left witness)) ->
  TraceIndependent Nat ToyKey ToyRuntime String ToyValue DGamma.CP3VestigialChecks.keyEq
    (episodeRightTrace (vestigial27Right witness)) ->
  (registrations : RegistrationCorrespondenceByGeneration
      DGamma.CP3VestigialChecks.nameEq
      (generatedGenerationBijection (vestigial27SameInputWitness witness))
      (vestigialLeft27Trace (vestigial27Left witness))
      (episodeRightTrace (vestigial27Right witness)) **
    SystemEquivalentByRenamingModuloVestigial Nat ToyKey ToyRuntime String
      ToyValue DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq
      registrations (currentNameBijection (endpointRenaming
        (vestigial27SameInputWitness witness))))
vestigial27Theorem73PremiseChain claim protocol witness leftAligned rightAligned
  leftDiscipline rightDiscipline initialWellFormed initialEmpty leftQuiet
  rightQuiet leftSuccess rightSuccess leftTotal rightTotal leftIndependent
  rightIndependent =
    let result = claim DGamma.CP3VestigialChecks.nameEq
          DGamma.CP3VestigialChecks.keyEq protocol
          DGamma.CalculusChecks.initialSystem
          (namedAfter (finishSurvivor27 (vestigial27Left witness)))
          (namedAfter (rightFinish4 (vestigial27Right witness)))
          (vestigialLeft27Trace (vestigial27Left witness))
          (episodeRightTrace (vestigial27Right witness))
          leftAligned rightAligned leftDiscipline rightDiscipline
          initialWellFormed initialEmpty leftQuiet rightQuiet leftSuccess
          rightSuccess leftTotal rightTotal leftIndependent rightIndependent
          (vestigial27SameInputWitness witness) in
      (finalRegistrationCorrespondence result ** finalEndpointsEquivalent result)

||| A live/supported name cannot acquire vestigial evidence, irrespective of
||| any alleged discarded-generation metadata. This is the negative half of
||| the quotient: only genuinely inert Lemma-57 entries may be unmatched.
public export
0 supportedGenerationNotVestigial :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {current : GenerationEnvironment name} ->
  {discarded : List (RegistrationGeneration name)} ->
  {selected : name} -> {state : SystemState name key value world error} ->
  isSupported @{nameEq} @{keyEq} selected state = True ->
  VestigialEndpointGeneration name key world error value nameEq keyEq
    current discarded selected state -> Void
supportedGenerationNotVestigial supported vestigial =
  case trans (sym supported) (vestigialUnsupported vestigial) of
    Refl impossible

||| Concrete live-provider probe. The right endpoint's replacement provider is
||| both supported and the installed provider of ServiceA; even if a caller
||| fabricates discarded-generation membership, vestigial evidence is rejected
||| at the support field rather than accepted as a mere metadata flag.
public export
0 liveProvidingFiberVestigialRejected :
  (right : EpisodeRightTrace) ->
  isSupported @{DGamma.CP3VestigialChecks.nameEq}
    @{DGamma.CP3VestigialChecks.keyEq} 3
    (namedAfter (rightFinish4 right)) = True ->
  providerOf @{DGamma.CP3VestigialChecks.nameEq}
    @{DGamma.CP3VestigialChecks.keyEq} {value = ToyValue}
    {world = ToyRuntime} {error = String} ServiceA
    (registry (namedAfter (rightFinish4 right))) = Just 3 ->
  {current : GenerationEnvironment Nat} ->
  {discarded : List (RegistrationGeneration Nat)} ->
  VestigialEndpointGeneration Nat ToyKey ToyRuntime String ToyValue
    DGamma.CP3VestigialChecks.nameEq DGamma.CP3VestigialChecks.keyEq
    current discarded 3 (namedAfter (rightFinish4 right)) -> Void
liveProvidingFiberVestigialRejected right supported providing vestigial =
  supportedGenerationNotVestigial supported vestigial

public export
liveProvidingFiberRuntimeCheck : Bool
liveProvidingFiberRuntimeCheck = case buildEpisodeCommonPrefix of
  Nothing => False
  Just common => case buildEpisodeRightTrace common of
    Nothing => False
    Just right =>
      isSupported @{nameEq} @{keyEq} 3 (namedAfter (rightFinish4 right)) &&
      case providerOf @{nameEq} @{keyEq} ServiceA
        (registry (namedAfter (rightFinish4 right))) of
        Just 3 => True
        _ => False

public export
allCP3VestigialChecks : Bool
allCP3VestigialChecks = vestigial23RuntimeCheck &&
  vestigial23CorrespondenceCheck && vestigial27RuntimeCheck &&
  vestigial27CorrespondenceCheck && liveProvidingFiberRuntimeCheck
