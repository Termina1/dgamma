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

||| Executable annotation of an ACTUAL checked DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace, preserving
||| every chronological action. States/trace indices remain authenticated by
||| DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep; no arbitrary word can replace a lifecycle or birth.
public export
annotateAnchors :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  (anchors : Nat -> name -> Maybe Nat) -> (ordinal : Nat) ->
  DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace -> List (AnchorEvent name)
annotateAnchors anchors ordinal (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd state) = []
annotateAnchors anchors ordinal (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep first (Fired nameEq keyEq action tag checked) rest later) =
  nativeAnchorEvent anchors ordinal action :: annotateAnchors anchors (S ordinal) later
