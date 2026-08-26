module DGamma.R38UnloadExactMapFromRuntimeAccumulatorNegative

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Data.List.Elem
import Decidable.Equality

%default total

ProbeKey : Type
ProbeKey = Nat

ProbeValue : ProbeKey -> Type
ProbeValue _ = Unit

0 probeFreshLeft : Not (Elem (the Nat 0) [])
probeFreshLeft present = absurd present

0 probeFreshRight : Not (Elem (the Nat 0) [])
probeFreshRight Here impossible
probeFreshRight (There later) impossible

ProbeProvision : CoeffectSpec ProbeKey
ProbeProvision = MkCoeffectSpec [the Nat 0]
  (UniqueCons probeFreshLeft UniqueNil)

0 probeOwnedSound : (key : ProbeKey) ->
  Elem key [the Nat 0] -> Elem key [the Nat 0]
probeOwnedSound key present = present

ProbeLeftTable : OwnedTable ProbeKey ProbeValue ProbeProvision
ProbeLeftTable = MkOwnedTable
  (MkCoeffectContext [Bind (the Nat 0) ()]
    (UniqueCons probeFreshLeft UniqueNil))
  probeOwnedSound

ProbeRightTable : OwnedTable ProbeKey ProbeValue ProbeProvision
ProbeRightTable = MkOwnedTable
  (MkCoeffectContext [Bind (the Nat 0) ()]
    (UniqueCons probeFreshRight UniqueNil))
  probeOwnedSound

ProbeLeftAccumulator :
  LocalState ProbeKey ProbeValue Unit ProbeProvision ->
  LocalState ProbeKey ProbeValue Unit ProbeProvision
ProbeLeftAccumulator input = MkLocalState () ProbeLeftTable

ProbeRightAccumulator :
  LocalState ProbeKey ProbeValue Unit ProbeProvision ->
  LocalState ProbeKey ProbeValue Unit ProbeProvision
ProbeRightAccumulator input = MkLocalState () ProbeRightTable

0 probeAccumulatorsRuntimeRelated :
  AccumulatorRelated ProbeLeftAccumulator ProbeRightAccumulator
probeAccumulatorsRuntimeRelated input = MkLocalStateRuntimeRelated Refl Refl

||| Expected failure pin for O6 revision 38. The two accumulators agree on every
||| runtime field, but their output tables contain distinct erased uniqueness
||| functions. The frozen exact `headMapPreserved` field therefore cannot be
||| derived from `AccumulatorRelated`.
0 unloadExactMapFromRuntimeAccumulatorNegative :
  (nameEq : DecEq Nat) -> (keyEq : DecEq ProbeKey) -> (actor : Nat) ->
  (state : EffectState Nat ProbeKey ProbeValue Unit) ->
  accumulatorRuntimeEffectMap nameEq keyEq actor ProbeLeftAccumulator state =
    accumulatorRuntimeEffectMap nameEq keyEq actor ProbeRightAccumulator state
unloadExactMapFromRuntimeAccumulatorNegative nameEq keyEq actor state =
  let input : LocalState ProbeKey ProbeValue Unit ProbeProvision
      input = MkLocalState (effectAmbient state)
        (restrictOwnedPreservingOrder @{keyEq} ProbeProvision
          (effectTables state actor))
  in case probeAccumulatorsRuntimeRelated input of
    MkLocalStateRuntimeRelated Refl Refl => Refl
