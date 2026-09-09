module DGamma.L2R9NativeSelection

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R7CatalogBirth
import DGamma.L2R8DistanceSearch
import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Runtime first-positive search on the ACTUAL native catalog/distance,
||| plus erased positive-total selection and authentic native-birth decoding.
||| None of these fields assumes key forcing, a move, or a phase. The producer
||| must fill both decoders from retained general theorems, not caller oracles.
public export
record NativeDistanceSelection
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {0 first, finalState : SystemState name key value world error}
  {0 trace : Transitions first finalState}
  (trail : AvailabilityTrace name key world error value trace) where
  constructor MkNativeDistanceSelection
  nativeSearch : DistanceSearch (\entry => rootDistance nameEq keyEq trail (catalogOrdinal entry)) (scanRootCatalog 0 trail)
  0 nativeSearchEquation : searchDistance (\entry => rootDistance nameEq keyEq trail (catalogOrdinal entry)) (scanRootCatalog 0 trail) = nativeSearch
  0 nativeSelected : (0 positive : LT 0 (totalDistance nameEq keyEq trail)) ->
    (entry : RootCatalogEntry name key world error value **
     before : List (RootCatalogEntry name key world error value) **
     after : List (RootCatalogEntry name key world error value) **
     (Elem entry (scanRootCatalog 0 trail), scanRootCatalog 0 trail = before ++ entry :: after,
      All (\earlier => rootDistance nameEq keyEq trail (catalogOrdinal earlier) = 0) before,
      LT 0 (rootDistance nameEq keyEq trail (catalogOrdinal entry))))
  0 nativeBirth : (entry : RootCatalogEntry name key world error value) ->
    (0 member : Elem entry (scanRootCatalog 0 trail)) ->
    CatalogBirthAt name key world error value entry 0 trace
