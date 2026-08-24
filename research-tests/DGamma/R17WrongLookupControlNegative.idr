module DGamma.R17WrongLookupControlNegative

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import Decidable.Equality

%default total

||| An actor present on the left and absent on the right cannot be certified by
||| the no-fiber constructor. `ControlEquivalent` rejects the wrong lookup pair
||| at the selected actor rather than accepting caller-chosen permutation data.
0 wrongLookupControlPairRejected :
  (nameEq : DecEq Bool) ->
  (ambient : world) ->
  (fiber : Fiber Bool key value world error) ->
  (0 leftUnique : UniqueKeys [False]) ->
  ControlEquivalent Bool key world error value nameEq
    (MkSystemState ambient
      (MkCoeffectContext
        (the (List (Binding Bool (FiberAt Bool key value world error)))
          [Bind False fiber]) leftUnique))
    (MkSystemState ambient (MkCoeffectContext [] UniqueNil))
wrongLookupControlPairRejected nameEq ambient fiber leftUnique =
  MkControlEquivalent (\selected => case selected of
    False => NoControlFibers
    True => NoControlFibers)
