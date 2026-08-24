module DGamma.R17WrongLookupControlNegative

import DGamma.Coeffects
import DGamma.CP3
import Decidable.Equality

%default total

0 falseNotInEmpty : Not (Elem False [])
falseNotInEmpty impossible

||| An actor present on the left and absent on the right cannot be certified by
||| the no-fiber constructor. `ControlEquivalent` rejects the wrong lookup pair
||| at the selected actor rather than accepting caller-chosen permutation data.
0 wrongLookupControlPairRejected :
  (nameEq : DecEq Bool) ->
  (ambient : world) ->
  (fiber : Fiber Bool key value world error) ->
  ControlEquivalent Bool key world error value nameEq
    (MkSystemState ambient
      (MkCoeffectContext [Bind False fiber]
        (UniqueCons falseNotInEmpty UniqueNil)))
    (MkSystemState ambient (MkCoeffectContext [] UniqueNil))
wrongLookupControlPairRejected nameEq ambient fiber =
  MkControlEquivalent (\selected => case selected of
    False => NoControlFibers
    True => NoControlFibers)
