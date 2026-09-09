module DGamma.L2R4AnchorNative

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R4AnchorMeasure
import Data.Nat

%default total
%unbound_implicits off

||| Exact Action classifier for native event annotations. Every lifecycle
||| constructor counts; only root OInsert births charge a root cost; ORemove
||| marks its ending cut. Root assignments use occurrence ordinal AND name,
||| so reborn names need not share anchors. Assignment validity is separate.
public export
nativeAnchorEvent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (anchors : Nat -> name -> Maybe Nat) -> (ordinal : Nat) ->
  Action name key value world error -> AnchorEvent name
nativeAnchorEvent anchors ordinal (OInsert actor Root component) = AnchorBirth actor (anchors ordinal actor)
nativeAnchorEvent anchors ordinal (OInsert actor (ChildOf parent) component) = AnchorOther
nativeAnchorEvent anchors ordinal (ORetire actor) = AnchorOther
nativeAnchorEvent anchors ordinal (ORemove actor) = AnchorRelease (S ordinal)
nativeAnchorEvent anchors ordinal (LBegin actor) = AnchorLife actor
nativeAnchorEvent anchors ordinal (LAdvance actor) = AnchorLife actor
nativeAnchorEvent anchors ordinal (LDivert actor) = AnchorLife actor
nativeAnchorEvent anchors ordinal (LUnload actor) = AnchorLife actor
nativeAnchorEvent anchors ordinal (LLeave actor) = AnchorLife actor
