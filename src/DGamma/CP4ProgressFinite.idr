module DGamma.CP4ProgressFinite

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Control.WellFounded
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total


||| Append one final Definition-65 edge to a nonempty precedence path.
public export
0 precedencePathSnoc :
  PrecedencePath nameEq state first middle ->
  PrecedenceEdge nameEq middle finalName state ->
  PrecedencePath nameEq state first finalName
precedencePathSnoc (PrecedenceOne edge) finalEdge =
  PrecedenceMore edge (PrecedenceOne finalEdge)
precedencePathSnoc (PrecedenceMore edge rest) finalEdge =
  PrecedenceMore edge (precedencePathSnoc rest finalEdge)

||| The forward-successor relation used by the unloading descent: a consumer is
||| smaller than the provider it currently relies on, so accessibility follows
||| the provider-to-consumer direction of precedence.
public export
0 PrecedenceSuccessor :
  (nameEq : DecEq name) -> SystemState name key value world error ->
  name -> name -> Type
PrecedenceSuccessor nameEq state consumer provider =
  PrecedenceEdge nameEq provider consumer state

0 elemLengthZeroImpossible : (values : List a) -> length values = Z ->
  Elem wanted values -> Void
elemLengthZeroImpossible [] Refl present impossible
elemLengthZeroImpossible (_ :: _) Refl present impossible

0 accessibleFromAvailable :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (state : SystemState name key value world error) ->
  PrecedenceAcyclic nameEq state ->
  (fuel : Nat) -> (available, seen : List name) -> (current : name) ->
  length available = fuel -> Elem current available ->
  ((earlier : name) -> Elem earlier seen ->
    PrecedencePath nameEq state earlier current) ->
  ((candidate : name) -> Not (Elem candidate seen) ->
    (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} candidate (registry state) = Just fiber ->
    Elem candidate available) ->
  Accessible (PrecedenceSuccessor nameEq state) current
accessibleFromAvailable nameEq state acyclic Z available seen current lengthZero
  currentAvailable seenPath complete =
    void (elemLengthZeroImpossible available lengthZero currentAvailable)
accessibleFromAvailable nameEq state acyclic (S remaining) available seen current
  availableLength currentAvailable seenPath complete = Access $ \consumer, edge =>
    let 0 consumerNotCurrent : Not (consumer = current)
        consumerNotCurrent same =
          let 0 selfEdge : PrecedenceEdge nameEq current current state
              selfEdge = replace
                {p = \selected => PrecedenceEdge nameEq current selected state}
                same edge
          in acyclic current (PrecedenceOne selfEdge)
        0 consumerNotSeen : Not (Elem consumer seen)
        consumerNotSeen present = acyclic consumer
          (precedencePathSnoc (seenPath consumer present) edge)
        0 consumerAvailable : Elem consumer available
        consumerAvailable = complete consumer consumerNotSeen
          (consumerFiber edge) (consumerFound edge)
        0 consumerRemaining : Elem consumer (removeName current available)
        consumerRemaining = elemRemoveOtherName consumer current
          consumerNotCurrent available consumerAvailable
        0 removedLength : S (length (removeName current available)) =
          length available
        removedLength = removeNamePresentLength current available currentAvailable
        0 remainingLength : length (removeName current available) = remaining
        remainingLength = case trans removedLength availableLength of Refl => Refl
        0 nextSeenPath : (earlier : name) -> Elem earlier (current :: seen) ->
          PrecedencePath nameEq state earlier consumer
        nextSeenPath _ Here = PrecedenceOne edge
        nextSeenPath earlier (There earlierSeen) =
          precedencePathSnoc (seenPath earlier earlierSeen) edge
        0 nextComplete : (candidate : name) ->
          Not (Elem candidate (current :: seen)) ->
          (fiber : Fiber name key value world error) ->
          lookupFiber @{nameEq} candidate (registry state) = Just fiber ->
          Elem candidate (removeName current available)
        nextComplete candidate candidateFresh fiber found =
          let 0 candidateNotSeen : Not (Elem candidate seen)
              candidateNotSeen present = candidateFresh (There present)
              0 candidateNotCurrent : Not (candidate = current)
              candidateNotCurrent same = candidateFresh
                (replace {p = \selected => Elem selected (current :: seen)}
                  (sym same) Here)
          in elemRemoveOtherName candidate current candidateNotCurrent available
            (complete candidate candidateNotSeen fiber found)
    in accessibleFromAvailable nameEq state acyclic remaining
      (removeName current available) (current :: seen) consumer remainingLength
      consumerRemaining nextSeenPath nextComplete

||| Constructive finite-graph well-foundedness in the direction needed by
||| Theorem 66. This is the same finite acyclicity-to-descent pattern used by
||| Lemma 68, specialized to Definition 65 alone.
public export
0 precedenceSuccessorAccessible :
  (nameEq : DecEq name) -> (state : SystemState name key value world error) ->
  PrecedenceAcyclic nameEq state -> (current : name) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} current (registry state) = Just fiber ->
  Accessible (PrecedenceSuccessor nameEq state) current
precedenceSuccessorAccessible nameEq
  state@(MkSystemState ambient (MkCoeffectContext entries unique)) acyclic current
  fiber found =
    let 0 currentAvailable : Elem current (bindingKeys entries)
        currentAvailable = lookupJustElem current entries fiber found
        0 complete : (candidate : name) -> Not (Elem candidate []) ->
          (observed : Fiber name key value world error) ->
          lookupFiber @{nameEq} candidate
            (registry state) = Just observed ->
          Elem candidate (bindingKeys entries)
        complete candidate fresh observed present =
          lookupJustElem candidate entries observed present
        0 noSeenPath : (earlier : name) -> Elem earlier [] ->
          PrecedencePath nameEq state earlier current
        noSeenPath earlier present impossible
    in accessibleFromAvailable nameEq state acyclic (length (bindingKeys entries))
      (bindingKeys entries) [] current Refl currentAvailable noSeenPath complete
