module DGamma.CP4SupportSolution

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4Support
import Control.WellFounded
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

data PrependedBy : Nat -> List a -> List a -> Type where
  PrependedSame : PrependedBy Z values values
  PrependedOne : PrependedBy stepCount smaller larger ->
    PrependedBy (S stepCount) smaller (value :: larger)

prependedTrans :
  PrependedBy firstCount first middle ->
  PrependedBy secondCount middle final ->
  PrependedBy (secondCount + firstCount) first final
prependedTrans first PrependedSame = first
prependedTrans first (PrependedOne rest) = PrependedOne (prependedTrans first rest)

prependedLength : (count : Nat) -> (smaller, larger : List a) ->
  PrependedBy count smaller larger ->
  length larger = count + length smaller
prependedLength Z values values PrependedSame = Refl
prependedLength (S count) smaller (value :: larger) (PrependedOne rest) =
  cong S (prependedLength count smaller larger rest)

supportPassEntriesPrepended :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {auto nameEq : DecEq name} -> {auto keyEq : DecEq key} ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (scan : List (Binding name (FiberAt name key value world error))) ->
  (supported : List name) ->
  (count : Nat ** PrependedBy count supported
    (supportPassEntries {value = value} {world = world} {error = error} entries scan supported))
supportPassEntriesPrepended entries [] supported = (Z ** PrependedSame)
supportPassEntriesPrepended entries (Bind n fiber :: rest) supported
  with (listMember n supported) proof member
  supportPassEntriesPrepended entries (Bind n fiber :: rest) supported |
    True = supportPassEntriesPrepended entries rest supported
  supportPassEntriesPrepended entries (Bind n fiber :: rest) supported |
    False with (supportCandidate entries supported (Bind n fiber)) proof candidate
    supportPassEntriesPrepended entries (Bind n fiber :: rest) supported |
      False | True =
        let (count ** extension) = supportPassEntriesPrepended entries rest
              (n :: supported)
            first : PrependedBy (S Z) supported (n :: supported)
            first = PrependedOne PrependedSame
            combined = prependedTrans first extension
        in (count + S Z ** combined)
    supportPassEntriesPrepended entries (Bind n fiber :: rest) supported |
      False | False = supportPassEntriesPrepended entries rest supported

supportPassPrepended :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {auto nameEq : DecEq name} -> {auto keyEq : DecEq key} ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (supported : List name) ->
  (count : Nat ** PrependedBy count supported (supportPass {value = value} {world = world} {error = error} entries supported))
supportPassPrepended entries supported =
  supportPassEntriesPrepended entries entries supported

prependedZeroSame : (smaller, larger : List a) ->
  PrependedBy Z smaller larger -> smaller = larger
prependedZeroSame values values PrependedSame = Refl

prependedNonzeroLonger : (count : Nat) -> (smaller, larger : List a) ->
  PrependedBy (S count) smaller larger ->
  LT (length smaller) (length larger)
prependedNonzeroLonger count smaller larger extension =
  rewrite prependedLength (S count) smaller larger extension in
  LTESucc (replace {p = \right => LTE (length smaller) right}
    (plusCommutative (length smaller) count)
    (lteAddRight (length smaller)))

supportFuelFixed :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {auto nameEq : DecEq name} -> {auto keyEq : DecEq key} ->
  (fuel : Nat) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (supported : List name) ->
  supportPass {value = value} {world = world} {error = error} entries supported = supported ->
  supportFuel {value = value} {world = world} {error = error} fuel entries supported = supported
supportFuelFixed Z entries supported fixed = Refl
supportFuelFixed (S fuel) entries supported fixed =
  rewrite fixed in supportFuelFixed fuel entries supported fixed

supportFuelEndpointFixed :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {auto nameEq : DecEq name} -> {auto keyEq : DecEq key} ->
  (fuel : Nat) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (supported : List name) ->
  supportPass {value = value} {world = world} {error = error} entries supported = supported ->
  supportPass {value = value} {world = world} {error = error} entries (supportFuel {value = value} {world = world} {error = error} fuel entries supported) =
    supportFuel {value = value} {world = world} {error = error} fuel entries supported
supportFuelEndpointFixed {value} {world} {error} {nameEq} {keyEq}
  fuel entries supported fixed =
    let ended = supportFuelFixed @{nameEq} @{keyEq} fuel entries supported fixed
    in replace
      {p = \state => supportPass {value = value} {world = world} {error = error}
        entries state = state}
      (sym ended) fixed

totalCountLower : (fuel, restCount, passTail : Nat) -> LTE fuel restCount ->
  LTE (S fuel) (restCount + S passTail)
totalCountLower fuel restCount passTail lower =
  let first : LTE (S fuel) (S fuel + passTail)
      first = lteAddRight (S fuel)
      second : LTE (S fuel + passTail) (S restCount + passTail)
      second = plusLteMonotoneRight passTail (S fuel) (S restCount)
        (LTESucc lower)
  in replace {p = \right => LTE (S fuel) right}
    (plusSuccRightSucc restCount passTail) (transitive first second)

||| If the endpoint remains unstable after `fuel` passes, at least `fuel`
||| distinct prepend operations occurred.
unstableFuelAdds :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {auto nameEq : DecEq name} -> {auto keyEq : DecEq key} ->
  (fuel : Nat) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (supported : List name) ->
  Not (supportPass {value = value} {world = world} {error = error} entries (supportFuel {value = value} {world = world} {error = error} fuel entries supported) =
    supportFuel {value = value} {world = world} {error = error} fuel entries supported) ->
  (count : Nat **
    (PrependedBy count supported (supportFuel {value = value} {world = world} {error = error} fuel entries supported),
     LTE fuel count))
unstableFuelAdds Z entries supported unstable =
  (Z ** (PrependedSame, LTEZero))
unstableFuelAdds (S fuel) entries supported unstable =
  let (passCount ** passExtension) = supportPassPrepended @{nameEq} @{keyEq}
        {value = value} {world = world} {error = error} entries supported
  in case passCount of
    Z =>
      let passFixed : (supported = supportPass @{nameEq} @{keyEq}
            {value = value} {world = world} {error = error} entries supported)
          passFixed = prependedZeroSame supported
            (supportPass @{nameEq} @{keyEq} {value = value} {world = world}
              {error = error} entries supported) passExtension
          fixed : (supportPass @{nameEq} @{keyEq}
            {value = value} {world = world} {error = error} entries supported =
            supported)
          fixed = sym passFixed
          endpointFixed :
            (supportPass @{nameEq} @{keyEq}
              {value = value} {world = world} {error = error} entries
              (supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
                {error = error} fuel entries supported) =
             supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
               {error = error} fuel entries supported)
          endpointFixed = supportFuelEndpointFixed @{nameEq} @{keyEq} fuel entries
            supported fixed
          endpointOriginal = replace
            {p = \start =>
              supportPass @{nameEq} @{keyEq} {value = value} {world = world}
                {error = error} entries
                (supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
                  {error = error} fuel entries start) =
              supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
                {error = error} fuel entries start}
            (sym fixed) endpointFixed
      in void (unstable endpointOriginal)
    S passTail =>
      let (restCount ** (restExtension, restLower)) =
            unstableFuelAdds @{nameEq} @{keyEq} fuel entries
              (supportPass @{nameEq} @{keyEq} {value = value} {world = world}
                {error = error} entries supported) unstable
          combined = prependedTrans passExtension restExtension
      in (restCount + S passTail **
        (combined, totalCountLower fuel restCount passTail restLower))

listMemberFalseNotElem : DecEq a => (wanted : a) -> (values : List a) ->
  listMember wanted values = False -> Not (Elem wanted values)
listMemberFalseNotElem wanted [] absent present impossible
listMemberFalseNotElem wanted (current :: rest) absent present
  with (decEq wanted current)
  listMemberFalseNotElem current (current :: rest) absent present |
    Yes Refl = case absent of Refl impossible
  listMemberFalseNotElem current (current :: rest) absent Here |
    No distinct = void (distinct Refl)
  listMemberFalseNotElem wanted (current :: rest) absent (There later) |
    No distinct = listMemberFalseNotElem wanted rest absent later

0 NamesSubset : List name -> List name -> Type
NamesSubset smaller larger = (selected : name) -> Elem selected smaller ->
  Elem selected larger

0 bindingNamesSubsetTail :
  NamesSubset (bindingKeys rest) (bindingKeys (entry :: rest))
bindingNamesSubsetTail selected present = There present

supportPassEntriesSubset :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {auto nameEq : DecEq name} -> {auto keyEq : DecEq key} ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (scan : List (Binding name (FiberAt name key value world error))) ->
  (supported : List name) ->
  NamesSubset (bindingKeys scan) (bindingKeys entries) ->
  NamesSubset supported (bindingKeys entries) ->
  NamesSubset (supportPassEntries {value = value} {world = world} {error = error} entries scan supported) (bindingKeys entries)
supportPassEntriesSubset entries [] supported scanSubset supportedSubset =
  supportedSubset
supportPassEntriesSubset entries (Bind n fiber :: rest) supported
  scanSubset supportedSubset with (listMember n supported) proof member
  supportPassEntriesSubset entries (Bind n fiber :: rest) supported
    scanSubset supportedSubset | True =
      supportPassEntriesSubset entries rest supported
        (\selected, present => scanSubset selected (There present)) supportedSubset
  supportPassEntriesSubset entries (Bind n fiber :: rest) supported
    scanSubset supportedSubset | False with (supportCandidate entries supported (Bind n fiber)) proof candidate
    supportPassEntriesSubset entries (Bind n fiber :: rest) supported
      scanSubset supportedSubset | False | True =
        let branchResult = supportPassEntriesSubset entries rest (n :: supported)
              (\selected, present => scanSubset selected (There present))
              (\selected, present => case present of
                Here => scanSubset n Here
                There later => supportedSubset selected later)
        in branchResult
    supportPassEntriesSubset entries (Bind n fiber :: rest) supported
      scanSubset supportedSubset | False | False =
        supportPassEntriesSubset entries rest supported
          (\selected, present => scanSubset selected (There present)) supportedSubset

supportPassEntriesUnique :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {auto nameEq : DecEq name} -> {auto keyEq : DecEq key} ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (scan : List (Binding name (FiberAt name key value world error))) ->
  (supported : List name) ->
  UniqueKeys supported ->
  UniqueKeys (supportPassEntries {value = value} {world = world} {error = error} entries scan supported)
supportPassEntriesUnique entries [] supported unique = unique
supportPassEntriesUnique entries (Bind n fiber :: rest) supported unique
  with (listMember n supported) proof member
  supportPassEntriesUnique entries (Bind n fiber :: rest) supported unique |
    True = supportPassEntriesUnique entries rest supported unique
  supportPassEntriesUnique entries (Bind n fiber :: rest) supported unique |
    False with (supportCandidate entries supported (Bind n fiber)) proof candidate
    supportPassEntriesUnique entries (Bind n fiber :: rest) supported unique |
      False | True =
        let branchResult = supportPassEntriesUnique entries rest (n :: supported)
              (UniqueCons (listMemberFalseNotElem n supported member) unique)
        in branchResult
    supportPassEntriesUnique entries (Bind n fiber :: rest) supported unique |
      False | False = supportPassEntriesUnique entries rest supported unique

identityNamesSubset : (values : List name) -> NamesSubset values values
identityNamesSubset values selected present = present

supportPassSubset :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {auto nameEq : DecEq name} -> {auto keyEq : DecEq key} ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (supported : List name) ->
  NamesSubset supported (bindingKeys entries) ->
  NamesSubset (supportPass {value = value} {world = world} {error = error} entries supported) (bindingKeys entries)
supportPassSubset entries supported subset =
  supportPassEntriesSubset entries entries supported (identityNamesSubset (bindingKeys entries)) subset

supportPassUnique :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {auto nameEq : DecEq name} -> {auto keyEq : DecEq key} ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (supported : List name) -> UniqueKeys supported ->
  UniqueKeys (supportPass {value = value} {world = world} {error = error} entries supported)
supportPassUnique entries supported unique =
  supportPassEntriesUnique entries entries supported unique

supportFuelSubset :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {auto nameEq : DecEq name} -> {auto keyEq : DecEq key} ->
  (fuel : Nat) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (supported : List name) ->
  NamesSubset supported (bindingKeys entries) ->
  NamesSubset (supportFuel {value = value} {world = world} {error = error} fuel entries supported) (bindingKeys entries)
supportFuelSubset Z entries supported subset = subset
supportFuelSubset (S fuel) entries supported subset =
  supportFuelSubset fuel entries (supportPass {value = value} {world = world} {error = error} entries supported)
    (supportPassSubset entries supported subset)

supportFuelUnique :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {auto nameEq : DecEq name} -> {auto keyEq : DecEq key} ->
  (fuel : Nat) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (supported : List name) -> UniqueKeys supported ->
  UniqueKeys (supportFuel {value = value} {world = world} {error = error} fuel entries supported)
supportFuelUnique Z entries supported unique = unique
supportFuelUnique (S fuel) entries supported unique =
  supportFuelUnique fuel entries (supportPass {value = value} {world = world} {error = error} entries supported)
    (supportPassUnique entries supported unique)


removeFirst : DecEq a => a -> List a -> List a
removeFirst wanted [] = []
removeFirst wanted (current :: rest) with (decEq wanted current)
  removeFirst current (current :: rest) | Yes Refl = rest
  removeFirst wanted (current :: rest) | No different =
    current :: removeFirst wanted rest

removePresentLength : DecEq a => (wanted : a) -> (values : List a) ->
  Elem wanted values -> S (length (removeFirst wanted values)) = length values
removePresentLength wanted [] present impossible
removePresentLength wanted (current :: rest) present with (decEq wanted current)
  removePresentLength current (current :: rest) present | Yes Refl = Refl
  removePresentLength current (current :: rest) Here | No different =
    void (different Refl)
  removePresentLength wanted (current :: rest) (There later) | No different =
    cong S (removePresentLength wanted rest later)

elemOtherRemove : DecEq a => (wanted, removed : a) ->
  Not (wanted = removed) -> (values : List a) -> Elem wanted values ->
  Elem wanted (removeFirst removed values)
elemOtherRemove wanted removed different [] present impossible
elemOtherRemove wanted removed different (current :: rest) present
  with (decEq removed current)
  elemOtherRemove wanted current different (current :: rest) present |
    Yes Refl = case present of
      Here => void (different Refl)
      There later => later
  elemOtherRemove wanted removed different (current :: rest) present |
    No notRemoved = case present of
      Here => Here
      There later => There (elemOtherRemove wanted removed different rest later)

uniqueHeadDifferent :
  Not (Elem listHead listTail) -> Elem selected listTail ->
  Not (selected = listHead)
uniqueHeadDifferent headFresh selectedInTail Refl = headFresh selectedInTail

uniqueSubsetLength : DecEq a =>
  (smaller, larger : List a) -> UniqueKeys smaller ->
  NamesSubset smaller larger -> LTE (length smaller) (length larger)
uniqueSubsetLength [] larger UniqueNil subset = LTEZero
uniqueSubsetLength (head :: tail) larger (UniqueCons headFresh tailUnique)
  subset =
    let headPresent = subset head Here
        tailSubset : NamesSubset tail (removeFirst head larger)
        tailSubset selected selectedInTail =
          elemOtherRemove selected head
            (uniqueHeadDifferent headFresh selectedInTail) larger
            (subset selected (There selectedInTail))
        tailBound = uniqueSubsetLength tail (removeFirst head larger)
          tailUnique tailSubset
        removedLength = removePresentLength head larger headPresent
    in replace {p = \size => LTE (S (length tail)) size}
      removedLength (LTESucc tailBound)

natLTIrreflexiveSolution : (n : Nat) -> LT n n -> Void
natLTIrreflexiveSolution Z prf impossible
natLTIrreflexiveSolution (S k) (LTESucc prf) =
  natLTIrreflexiveSolution k prf

listDecEqWith : (elementEq : DecEq a) -> (left, right : List a) ->
  Dec (left = right)
listDecEqWith elementEq [] [] = Yes Refl
listDecEqWith elementEq [] (value :: rest) = No (\same => case same of {})
listDecEqWith elementEq (value :: rest) [] = No (\same => case same of {})
listDecEqWith elementEq (left :: lefts) (right :: rights)
  with (decEq @{elementEq} left right)
  listDecEqWith elementEq (left :: lefts) (left :: rights) | Yes Refl
    with (listDecEqWith elementEq lefts rights)
    listDecEqWith elementEq (left :: lefts) (left :: lefts) |
      Yes Refl | Yes Refl = Yes Refl
    listDecEqWith elementEq (left :: lefts) (left :: rights) |
      Yes Refl | No different = No (\same => different (snd (consInjective same)))
  listDecEqWith elementEq (left :: lefts) (right :: rights) | No different =
    No (\same => different (fst (consInjective same)))

bindingKeysLength : (entries : List (Binding key value)) ->
  length (bindingKeys entries) = length entries
bindingKeysLength [] = Refl
bindingKeysLength (entry :: rest) = cong S (bindingKeysLength rest)

||| The bounded closure performs enough passes on a finite unique registry: its
||| endpoint is a fixed point of one further support pass.
supportFuelLengthStable :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  supportPass @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} entries
    (supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
      {error = error} (length entries) entries []) =
  supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} (length entries) entries []
supportFuelLengthStable {value} {world} {error} nameEq keyEq entries
  with (listDecEqWith nameEq
    (supportPass @{nameEq} @{keyEq} {value = value} {world = world}
      {error = error} entries
      (supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
        {error = error} (length entries) entries []))
    (supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
      {error = error} (length entries) entries [])) proof decided
  supportFuelLengthStable {value} {world} {error} nameEq keyEq entries |
    Yes same = same
  supportFuelLengthStable {value} {world} {error} nameEq keyEq entries |
    No unstable =
      let (totalAdds ** (finalExtension, enoughAdds)) =
            unstableFuelAdds @{nameEq} @{keyEq} {value = value}
              {world = world} {error = error} (length entries) entries [] unstable
          computedFinalLength :
            (length (supportFuel @{nameEq} @{keyEq} {value = value}
              {world = world} {error = error} (length entries) entries []) =
             totalAdds)
          computedFinalLength = rewrite prependedLength totalAdds []
            (supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
              {error = error} (length entries) entries []) finalExtension in
                plusZeroRightNeutral totalAdds
          finalUnique = supportFuelUnique @{nameEq} @{keyEq} (length entries)
            entries [] UniqueNil
          finalSubset = supportFuelSubset @{nameEq} @{keyEq} (length entries)
            entries [] (\selected, present => case present of {})
          passResult = supportPassPrepended @{nameEq} @{keyEq}
            {value = value} {world = world} {error = error} entries (supportFuel @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (length entries) entries [])
      in case passResult of
        (passAdds ** passExtension) => case passAdds of
          Z =>
            let same = prependedZeroSame (supportFuel @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (length entries) entries []) (supportPass @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries (supportFuel @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (length entries) entries [])) passExtension
            in void (unstable (sym same))
          S passTail =>
            let grows = prependedNonzeroLonger passTail (supportFuel @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (length entries) entries []) (supportPass @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries (supportFuel @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (length entries) entries [])) passExtension
                nextUnique = supportPassUnique @{nameEq} @{keyEq} entries (supportFuel @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (length entries) entries [])
                  finalUnique
                nextSubset = supportPassSubset @{nameEq} @{keyEq} entries (supportFuel @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (length entries) entries [])
                  finalSubset
                nextBound = uniqueSubsetLength (supportPass @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries (supportFuel @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (length entries) entries [])) (bindingKeys entries)
                  nextUnique nextSubset
                nextBoundEntries : (LTE (length (supportPass @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries (supportFuel @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (length entries) entries []))) (length entries))
                nextBoundEntries = replace
                  {p = \size => LTE (length (supportPass @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries (supportFuel @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (length entries) entries []))) size}
                  (bindingKeysLength entries) nextBound
                entriesBelowFinal : (LTE (length entries) (length (supportFuel @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (length entries) entries [])))
                entriesBelowFinal = replace
                  {p = \size => LTE (length entries) size}
                  (sym computedFinalLength) enoughAdds
                cycle : (LT (length entries) (length entries))
                cycle = transitive (LTESucc entriesBelowFinal)
                  (transitive grows nextBoundEntries)
            in void (natLTIrreflexiveSolution (length entries) cycle)


listMemberTrueElem : DecEq a => (wanted : a) -> (values : List a) ->
  listMember wanted values = True -> Elem wanted values
listMemberTrueElem wanted [] present = case present of Refl impossible
listMemberTrueElem wanted (current :: rest) present with (decEq wanted current)
  listMemberTrueElem current (current :: rest) present | Yes Refl = Here
  listMemberTrueElem wanted (current :: rest) present | No different =
    There (listMemberTrueElem wanted rest present)

elemListMemberTrue : DecEq a => (wanted : a) -> (values : List a) ->
  Elem wanted values -> listMember wanted values = True
elemListMemberTrue wanted (wanted :: rest) Here with (decEq wanted wanted)
  elemListMemberTrue wanted (wanted :: rest) Here | Yes Refl = Refl
  elemListMemberTrue wanted (wanted :: rest) Here | No contra = void (contra Refl)
elemListMemberTrue wanted (current :: rest) (There later)
  with (decEq wanted current)
  elemListMemberTrue current (current :: rest) (There later) | Yes Refl = Refl
  elemListMemberTrue wanted (current :: rest) (There later) | No different =
    elemListMemberTrue wanted rest later

namesSubsetCons : NamesSubset supported (added :: supported)
namesSubsetCons selected present = There present

namesSubsetTrans : NamesSubset first middle -> NamesSubset middle final ->
  NamesSubset first final
namesSubsetTrans first second selected present = second selected (first selected present)

0 prependedNamesSubset :
  (count : Nat) -> (smaller, larger : List name) ->
  PrependedBy count smaller larger -> NamesSubset smaller larger
prependedNamesSubset Z values values PrependedSame =
  \selected, present => present
prependedNamesSubset (S count) smaller (value :: larger) (PrependedOne rest) =
  namesSubsetTrans (prependedNamesSubset count smaller larger rest) namesSubsetCons

orRightTrue : (left : Bool) -> left || True = True
orRightTrue False = Refl
orRightTrue True = Refl

providerCandidateMonotone :
  {name, key, world, error : Type} -> {value : key -> Type} -> DecEq name => DecEq key =>
  (wanted : key) -> (smaller, larger : List name) ->
  NamesSubset smaller larger ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  providerFromCandidate {value = value} {world = world} {error = error} wanted smaller entries = True ->
  providerFromCandidate {value = value} {world = world} {error = error} wanted larger entries = True
providerCandidateMonotone wanted smaller larger extends [] present =
  case present of Refl impossible
providerCandidateMonotone wanted smaller larger extends
  (Bind n fiber :: rest) present
  with (listMember n smaller) proof smallMember
  providerCandidateMonotone wanted smaller larger extends
    (Bind n fiber :: rest) present | True
    with (listMember wanted
      (dependencies (componentProvisions (fiberComponent fiber))))
    providerCandidateMonotone wanted smaller larger extends
      (Bind n fiber :: rest) present | True | True =
        let largeMember = elemListMemberTrue n larger
              (extends n (listMemberTrueElem n smaller smallMember))
        in rewrite largeMember in Refl
    providerCandidateMonotone wanted smaller larger extends
      (Bind n fiber :: rest) present | True | False =
        let largeMember = elemListMemberTrue n larger
              (extends n (listMemberTrueElem n smaller smallMember))
            tail = providerCandidateMonotone {value = value} {world = world}
              {error = error} wanted smaller larger extends rest present
        in rewrite largeMember in tail
  providerCandidateMonotone wanted smaller larger extends
    (Bind n fiber :: rest) present | False =
      let tail = providerCandidateMonotone {value = value} {world = world}
            {error = error} wanted smaller larger extends rest present
      in rewrite tail in orRightTrue
        (listMember n larger &&
          listMember wanted
            (dependencies (componentProvisions (fiberComponent fiber))))

parentCandidateMonotone : DecEq name =>
  (parent : Parent name) -> (smaller, larger : List name) ->
  NamesSubset smaller larger ->
  parentFromCandidate parent smaller = True ->
  parentFromCandidate parent larger = True
parentCandidateMonotone Root smaller larger extends present = Refl
parentCandidateMonotone (ChildOf parent) smaller larger extends present =
  elemListMemberTrue parent larger
    (extends parent (listMemberTrueElem parent smaller present))

andBothTrue : (left, right : Bool) -> left = True -> right = True ->
  left && right = True
andBothTrue left right leftTrue rightTrue =
  rewrite leftTrue in rewrite rightTrue in Refl

andLeftTrue : (left, right : Bool) -> left && right = True -> left = True
andLeftTrue False right valid = case valid of Refl impossible
andLeftTrue True right valid = Refl

andRightTrue : (left, right : Bool) -> left && right = True -> right = True
andRightTrue False right valid = case valid of Refl impossible
andRightTrue True right valid = valid

allProvidersMonotone :
  {name, key, world, error : Type} -> {value : key -> Type} -> DecEq name => DecEq key =>
  (wanted : List key) -> (smaller, larger : List name) ->
  NamesSubset smaller larger ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  allList (\k => providerFromCandidate {value = value} {world = world} {error = error} k smaller entries) wanted = True ->
  allList (\k => providerFromCandidate {value = value} {world = world} {error = error} k larger entries) wanted = True
allProvidersMonotone [] smaller larger extends entries present = Refl
allProvidersMonotone (k :: ks) smaller larger extends entries present =
  let headTrue = andLeftTrue
        (providerFromCandidate {value = value} {world = world} {error = error}
          k smaller entries)
        (allList (\wanted => providerFromCandidate {value = value}
          {world = world} {error = error} wanted smaller entries) ks) present
      tailTrue = andRightTrue
        (providerFromCandidate {value = value} {world = world} {error = error}
          k smaller entries)
        (allList (\wanted => providerFromCandidate {value = value}
          {world = world} {error = error} wanted smaller entries) ks) present
      nextHead = providerCandidateMonotone {value = value} {world = world}
        {error = error} k smaller larger extends entries headTrue
      nextTail = allProvidersMonotone {value = value} {world = world}
        {error = error} ks smaller larger extends entries tailTrue
  in andBothTrue _ _ nextHead nextTail

supportCandidateMonotone :
  {name, key, world, error : Type} -> {value : key -> Type} -> DecEq name => DecEq key =>
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (smaller, larger : List name) ->
  NamesSubset smaller larger ->
  (entry : Binding name (FiberAt name key value world error)) ->
  supportCandidate {value = value} {world = world} {error = error} entries smaller entry = True ->
  supportCandidate {value = value} {world = world} {error = error} entries larger entry = True
supportCandidateMonotone entries smaller larger extends (Bind n fiber) present =
  let aliveTrue = andLeftTrue (not (retired fiber))
        (parentFromCandidate (fiberParent fiber) smaller &&
          allList (\k => providerFromCandidate {value = value} {world = world}
            {error = error} k smaller entries)
            (dependencies (componentDependencies (fiberComponent fiber)))) present
      restTrue = andRightTrue (not (retired fiber))
        (parentFromCandidate (fiberParent fiber) smaller &&
          allList (\k => providerFromCandidate {value = value} {world = world}
            {error = error} k smaller entries)
            (dependencies (componentDependencies (fiberComponent fiber)))) present
      parentTrue = andLeftTrue (parentFromCandidate (fiberParent fiber) smaller)
        (allList (\k => providerFromCandidate {value = value} {world = world}
          {error = error} k smaller entries)
          (dependencies (componentDependencies (fiberComponent fiber)))) restTrue
      providersTrue = andRightTrue
        (parentFromCandidate (fiberParent fiber) smaller)
        (allList (\k => providerFromCandidate {value = value} {world = world}
          {error = error} k smaller entries)
          (dependencies (componentDependencies (fiberComponent fiber)))) restTrue
      nextParent = parentCandidateMonotone (fiberParent fiber) smaller larger
        extends parentTrue
      nextProviders = allProvidersMonotone {value = value} {world = world}
        {error = error}
        (dependencies (componentDependencies (fiberComponent fiber)))
        smaller larger extends entries providersTrue
      core = andBothTrue (not (retired fiber))
        (parentFromCandidate (fiberParent fiber) larger &&
          allList (\k => providerFromCandidate {value = value} {world = world}
            {error = error} k larger entries)
            (dependencies (componentDependencies (fiberComponent fiber))))
        aliveTrue (andBothTrue _ _ nextParent nextProviders)
  in core

bindingKeyFromEntryElem :
  (n : name) -> (fiber : Fiber name key value world error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  Elem (Bind n fiber) entries -> Elem n (bindingKeys entries)
bindingKeyFromEntryElem n fiber (Bind n fiber :: rest) Here = Here
bindingKeyFromEntryElem n fiber (entry :: rest) (There later) =
  There (bindingKeyFromEntryElem n fiber rest later)

entryLookupFromElem :
  {name, key, world, error : Type} -> {value : key -> Type} -> DecEq name =>
  (entries : List (Binding name (FiberAt name key value world error))) ->
  UniqueKeys (bindingKeys entries) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  Elem (Bind n fiber) entries -> lookupEntries n entries = Just fiber
entryLookupFromElem [] UniqueNil n fiber present impossible
entryLookupFromElem (Bind n fiber :: rest)
  (UniqueCons headFresh tailUnique) n fiber Here
  with (decEq n n)
  entryLookupFromElem (Bind n fiber :: rest)
    (UniqueCons headFresh tailUnique) n fiber Here | Yes Refl = Refl
  entryLookupFromElem (Bind n fiber :: rest)
    (UniqueCons headFresh tailUnique) n fiber Here | No contra =
      void (contra Refl)
entryLookupFromElem (Bind current observed :: rest)
  (UniqueCons headFresh tailUnique) n fiber (There later)
  with (decEq n current)
  entryLookupFromElem (Bind n observed :: rest)
    (UniqueCons headFresh tailUnique) n fiber (There later) | Yes Refl =
      void (headFresh (bindingKeyFromEntryElem n fiber rest later))
  entryLookupFromElem (Bind current observed :: rest)
    (UniqueCons headFresh tailUnique) n fiber (There later) | No different =
      entryLookupFromElem rest tailUnique n fiber later


0 EntriesSubset : List a -> List a -> Type
EntriesSubset smaller larger = (entry : a) -> Elem entry smaller -> Elem entry larger

entriesSubsetTail : EntriesSubset rest (entry :: rest)
entriesSubsetTail selected present = There present

entriesSubsetIdentity : EntriesSubset entries entries
entriesSubsetIdentity selected present = present

0 SupportListSound :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  List (Binding name (FiberAt name key value world error)) ->
  List name -> Type
SupportListSound nameEq keyEq entries supported =
  (selected : name) -> listMember @{nameEq} selected supported = True ->
  (fiber : Fiber name key value world error **
    (lookupEntries @{nameEq} selected entries = Just fiber,
     supportCandidate @{nameEq} @{keyEq} entries supported (Bind selected fiber) =
       True))

emptySupportListSound :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  SupportListSound {value = value} {world = world} {error = error} nameEq keyEq entries []
emptySupportListSound {value = value} {world = world} {error = error} nameEq keyEq entries selected present =
  case present of Refl impossible

supportListSoundCons :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  UniqueKeys (bindingKeys entries) ->
  (n : name) -> (fiber : Fiber name key value world error) ->
  Elem (Bind n fiber) entries ->
  (supported : List name) ->
  supportCandidate @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries supported (Bind n fiber) = True ->
  SupportListSound {value = value} {world = world} {error = error} nameEq keyEq entries supported ->
  SupportListSound {value = value} {world = world} {error = error} nameEq keyEq entries (n :: supported)
supportListSoundCons nameEq keyEq entries unique n fiber entryIn supported
  candidate sound selected present with (decEq @{nameEq} selected n)
  supportListSoundCons nameEq keyEq entries unique n fiber entryIn supported
    candidate sound n present | Yes Refl =
      let found = entryLookupFromElem entries unique n fiber entryIn
          nextCandidate = supportCandidateMonotone entries supported
            (n :: supported) namesSubsetCons (Bind n fiber) candidate
      in (fiber ** (found, nextCandidate))
  supportListSoundCons nameEq keyEq entries unique n fiber entryIn supported
    candidate sound selected present | No different =
      let oldPresent : (listMember @{nameEq} selected supported = True)
          oldPresent = present
      in case sound selected oldPresent of
        (oldFiber ** (found, oldCandidate)) =>
          let nextCandidate = supportCandidateMonotone entries supported
                (n :: supported) namesSubsetCons (Bind selected oldFiber)
                oldCandidate
          in (oldFiber ** (found, nextCandidate))

supportPassEntriesSound :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  UniqueKeys (bindingKeys entries) ->
  (scan : List (Binding name (FiberAt name key value world error))) ->
  EntriesSubset scan entries ->
  (supported : List name) ->
  SupportListSound {value = value} {world = world} {error = error} nameEq keyEq entries supported ->
  SupportListSound {value = value} {world = world} {error = error} nameEq keyEq entries
    (supportPassEntries @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries scan supported)
supportPassEntriesSound nameEq keyEq entries unique [] scanSubset supported sound =
  sound
supportPassEntriesSound nameEq keyEq entries unique
  (Bind n fiber :: rest) scanSubset supported sound
  with (listMember @{nameEq} n supported) proof member
  supportPassEntriesSound nameEq keyEq entries unique
    (Bind n fiber :: rest) scanSubset supported sound | True =
      supportPassEntriesSound nameEq keyEq entries unique rest
        (\selected, present => scanSubset selected (There present)) supported sound
  supportPassEntriesSound nameEq keyEq entries unique
    (Bind n fiber :: rest) scanSubset supported sound | False
    with (supportCandidate @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries supported (Bind n fiber)) proof candidate
    supportPassEntriesSound nameEq keyEq entries unique
      (Bind n fiber :: rest) scanSubset supported sound | False | True =
        supportPassEntriesSound nameEq keyEq entries unique rest
          (\selected, present => scanSubset selected (There present))
          (n :: supported)
          (supportListSoundCons nameEq keyEq entries unique n fiber
            (scanSubset (Bind n fiber) Here) supported candidate sound)
    supportPassEntriesSound nameEq keyEq entries unique
      (Bind n fiber :: rest) scanSubset supported sound | False | False =
        supportPassEntriesSound nameEq keyEq entries unique rest
          (\selected, present => scanSubset selected (There present)) supported sound

supportPassSound :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  UniqueKeys (bindingKeys entries) ->
  (supported : List name) -> SupportListSound {value = value} {world = world} {error = error} nameEq keyEq entries supported ->
  SupportListSound {value = value} {world = world} {error = error} nameEq keyEq entries
    (supportPass @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries supported)
supportPassSound nameEq keyEq entries unique supported sound =
  supportPassEntriesSound nameEq keyEq entries unique entries
    entriesSubsetIdentity supported sound

supportFuelSound :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (fuel : Nat) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  UniqueKeys (bindingKeys entries) ->
  (supported : List name) -> SupportListSound {value = value} {world = world} {error = error} nameEq keyEq entries supported ->
  SupportListSound {value = value} {world = world} {error = error} nameEq keyEq entries
    (supportFuel @{nameEq} @{keyEq} {value = value} {world = world} {error = error} fuel entries supported)
supportFuelSound nameEq keyEq Z entries unique supported sound = sound
supportFuelSound nameEq keyEq (S fuel) entries unique supported sound =
  supportFuelSound nameEq keyEq fuel entries unique
    (supportPass @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries supported)
    (supportPassSound nameEq keyEq entries unique supported sound)

maybeJustInjective : Just left = Just right -> left = right
maybeJustInjective Refl = Refl

0 lookupEntryElem :
  {name, key, world, error : Type} -> {value : key -> Type} -> DecEq name =>
  (selected : name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (fiber : Fiber name key value world error) ->
  lookupEntries selected entries = Just fiber -> Elem (Bind selected fiber) entries
lookupEntryElem selected [] fiber found = case found of Refl impossible
lookupEntryElem selected (Bind current observed :: rest) fiber found
  with (decEq selected current)
  lookupEntryElem current (Bind current observed :: rest) fiber found | Yes Refl =
    case maybeJustInjective found of Refl => Here
  lookupEntryElem selected (Bind current observed :: rest) fiber found | No different =
    There (lookupEntryElem selected rest fiber found)

0 providerPredicateCandidate :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (supported : List name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  providerFromPredicate @{nameEq} @{keyEq} {value = value} {world = world} {error = error} wanted
    (\selected => listMember @{nameEq} selected supported) entries =
  providerFromCandidate @{nameEq} @{keyEq} {value = value} {world = world} {error = error} wanted supported entries
providerPredicateCandidate nameEq keyEq wanted supported [] = Refl
providerPredicateCandidate nameEq keyEq wanted supported (Bind n fiber :: rest) =
  cong ((listMember @{nameEq} n supported &&
    listMember @{keyEq} wanted
      (dependencies (componentProvisions (fiberComponent fiber)))) ||)
    (providerPredicateCandidate {value = value} {world = world} {error = error}
      nameEq keyEq wanted supported rest)

0 allListPointwise :
  (left, right : a -> Bool) -> (values : List a) ->
  ((selected : a) -> Elem selected values -> left selected = right selected) ->
  allList left values = allList right values
allListPointwise left right [] pointwise = Refl
allListPointwise left right (value :: rest) pointwise =
  let headSame = pointwise value Here
      tailSame = allListPointwise left right rest
        (\selected, present => pointwise selected (There present))
  in rewrite headSame in rewrite tailSame in Refl

0 allProviderPredicatesCandidate :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : List key) -> (supported : List name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  allList (\k => providerFromPredicate @{nameEq} @{keyEq} {value = value} {world = world} {error = error} k
    (\selected => listMember @{nameEq} selected supported) entries) wanted =
  allList (\k => providerFromCandidate @{nameEq} @{keyEq} {value = value} {world = world} {error = error} k supported entries)
    wanted
allProviderPredicatesCandidate {value} {world} {error}
  nameEq keyEq wanted supported entries =
    allListPointwise
      (\k => providerFromPredicate @{nameEq} @{keyEq} {value = value}
        {world = world} {error = error} k
        (\selected => listMember @{nameEq} selected supported) entries)
      (\k => providerFromCandidate @{nameEq} @{keyEq} {value = value}
        {world = world} {error = error} k supported entries)
      wanted
      (\selected, present => providerPredicateCandidate {value = value}
        {world = world} {error = error} nameEq keyEq selected supported entries)

0 supportParentEta :
  (nameEq : DecEq name) -> (supported : List name) ->
  (fiber : Fiber name key value world error) -> (providers : Bool) ->
  (not (retired fiber) &&
    ((case fiberParent fiber of
      Root => True
      ChildOf parent => listMember @{nameEq} parent supported) && providers)) =
  (not (retired fiber) &&
    ((case fiberParent fiber of
      Root => True
      ChildOf parent => (\selected => listMember @{nameEq} selected supported)
        parent) && providers))
supportParentEta nameEq supported
  (MkFiber component Root retiredFlag table lifecycle) providers = Refl
supportParentEta nameEq supported
  (MkFiber component (ChildOf parent) retiredFlag table lifecycle) providers = Refl

0 reverseEquation : left = right -> right = expected -> expected = left
reverseEquation Refl Refl = Refl

0 reverseSupportCore :
  (nameEq : DecEq name) -> (supported : List name) ->
  (fiber : Fiber name key value world error) -> (providers, candidate, expected : Bool) ->
  (not (retired fiber) &&
    ((case fiberParent fiber of
      Root => True
      ChildOf parent => (\selected => listMember @{nameEq} selected supported)
        parent) && providers)) =
    candidate ->
  candidate = expected ->
  expected =
    (not (retired fiber) &&
      ((case fiberParent fiber of
        Root => True
        ChildOf parent => (\selected => listMember @{nameEq} selected supported)
          parent) && providers))
reverseSupportCore nameEq supported
  (MkFiber component Root retiredFlag table lifecycle) providers candidate expected
  clause candidateValue = reverseEquation clause candidateValue
reverseSupportCore nameEq supported
  (MkFiber component (ChildOf parent) retiredFlag table lifecycle)
  providers candidate expected clause candidateValue =
    reverseEquation clause candidateValue

0 supportClauseCoreCandidate :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (supported : List name) -> (selected : name) ->
  (fiber : Fiber name key value world error) ->
  (not (retired fiber) &&
    ((case fiberParent fiber of
      Root => True
      ChildOf parent => (\selected => listMember @{nameEq} selected supported)
        parent) &&
     allList (\k => providerFromPredicate @{nameEq} @{keyEq} {value = value}
       {world = world} {error = error} k
       (\n => listMember @{nameEq} n supported) entries)
       (dependencies (componentDependencies (fiberComponent fiber))))) =
  supportCandidate @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} entries supported (Bind selected fiber)
supportClauseCoreCandidate {value} {world} {error} nameEq keyEq entries
  supported selected fiber@(MkFiber component Root retiredFlag table lifecycle) =
    rewrite allProviderPredicatesCandidate {value = value} {world = world}
      {error = error} nameEq keyEq
      (dependencies (componentDependencies component)) supported entries in Refl
supportClauseCoreCandidate {value} {world} {error} nameEq keyEq entries
  supported selected
  fiber@(MkFiber component (ChildOf parent) retiredFlag table lifecycle) =
    rewrite allProviderPredicatesCandidate {value = value} {world = world}
      {error = error} nameEq keyEq
      (dependencies (componentDependencies component)) supported entries in Refl

0 finishSupportCore :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (supported : List name) -> (selected : name) ->
  (fiber : Fiber name key value world error) -> (expected : Bool) ->
  supportCandidate @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} entries supported (Bind selected fiber) = expected ->
  expected =
    (not (retired fiber) &&
      ((case fiberParent fiber of
        Root => True
        ChildOf parent => (\chosen => listMember @{nameEq} chosen supported)
          parent) &&
       allList (\k => providerFromPredicate @{nameEq} @{keyEq} {value = value}
         {world = world} {error = error} k
         (\chosen => listMember @{nameEq} chosen supported) entries)
         (dependencies (componentDependencies (fiberComponent fiber)))))
finishSupportCore {value} {world} {error} nameEq keyEq entries supported selected
  fiber@(MkFiber component Root retiredFlag table lifecycle) expected candidateValue =
    reverseEquation
      (supportClauseCoreCandidate nameEq keyEq entries supported selected fiber)
      candidateValue
finishSupportCore {value} {world} {error} nameEq keyEq entries supported selected
  fiber@(MkFiber component (ChildOf parent) retiredFlag table lifecycle)
  expected candidateValue =
    reverseEquation
      (supportClauseCoreCandidate nameEq keyEq entries supported selected fiber)
      candidateValue

0 supportClauseCandidate :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (unique : UniqueKeys (bindingKeys entries)) ->
  (supported : List name) -> (selected : name) ->
  (fiber : Fiber name key value world error) ->
  lookupEntries @{nameEq} selected entries = Just fiber ->
  supportClause @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
    (\n => listMember @{nameEq} n supported) selected
    (MkSystemState ambient (MkCoeffectContext entries unique)) =
  supportCandidate @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries supported (Bind selected fiber)
supportClauseCandidate {value} {world} {error} nameEq keyEq ambient entries
  unique supported selected
  fiber@(MkFiber component Root retiredFlag table lifecycle) found =
    rewrite found in
    rewrite allProviderPredicatesCandidate {value = value} {world = world}
      {error = error} nameEq keyEq
      (dependencies (componentDependencies component)) supported entries in Refl
supportClauseCandidate {value} {world} {error} nameEq keyEq ambient entries
  unique supported selected
  fiber@(MkFiber component (ChildOf parent) retiredFlag table lifecycle) found =
    rewrite found in
    rewrite allProviderPredicatesCandidate {value = value} {world = world}
      {error = error} nameEq keyEq
      (dependencies (componentDependencies component)) supported entries in Refl

0 transportListMemberTrue :
  (nameEq : DecEq name) -> (selected : name) ->
  (left, right : List name) -> left = right ->
  listMember @{nameEq} selected right = True ->
  listMember @{nameEq} selected left = True
transportListMemberTrue nameEq selected values values Refl present = present

0 eligibleAppearsPass :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (scan : List (Binding name (FiberAt name key value world error))) ->
  UniqueKeys (bindingKeys scan) ->
  (supported : List name) ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  Elem (Bind selected fiber) scan ->
  listMember @{nameEq} selected supported = False ->
  supportCandidate @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries supported
    (Bind selected fiber) = True ->
  listMember @{nameEq} selected
    (supportPassEntries @{nameEq} @{keyEq} {value = value} {world = world} {error = error} entries scan supported) = True
eligibleAppearsPass {value} {world} {error} nameEq keyEq entries scan unique
  supported selected fiber present missing candidate =
    supportPassEntriesEligible nameEq keyEq entries scan unique supported selected
      fiber present missing candidate
      (\added, current, eligible =>
        supportCandidateMonotone {value = value} {world = world} {error = error}
          entries current (added :: current) namesSubsetCons
          (Bind selected fiber) eligible)


emptyNamesSubset : (values : List name) -> NamesSubset [] values
emptyNamesSubset values selected present impossible

lookupNothingNoElem : DecEq key => (wanted : key) ->
  (entries : List (Binding key value)) ->
  lookupEntries wanted entries = Nothing -> Not (Elem wanted (bindingKeys entries))
lookupNothingNoElem wanted [] absent present impossible
lookupNothingNoElem wanted (Bind current observed :: rest) absent present
  with (decEq wanted current)
  lookupNothingNoElem current (Bind current observed :: rest) absent present |
    Yes Refl = case absent of Refl impossible
  lookupNothingNoElem current (Bind current observed :: rest) absent Here |
    No different = void (different Refl)
  lookupNothingNoElem wanted (Bind current observed :: rest) absent (There later) |
    No different = lookupNothingNoElem wanted rest absent later

supportListSoundAtFound :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (supported : List name) ->
  SupportListSound {value = value} {world = world} {error = error}
    nameEq keyEq entries supported ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupEntries @{nameEq} selected entries = Just fiber ->
  listMember @{nameEq} selected supported = True ->
  supportCandidate @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} entries supported (Bind selected fiber) = True
supportListSoundAtFound nameEq keyEq entries supported sound selected fiber found
  present = case sound selected present of
    (observed ** (observedFound, candidate)) =>
      case maybeJustInjective (trans (sym observedFound) found) of
        Refl => candidate

||| The executable bounded support closure satisfies Definition 67's equation.
public export
0 supportSetIsSolution :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  SupportSolution @{nameEq} @{keyEq}
    (\selected => isSupported @{nameEq} @{keyEq} selected state) state
supportSetIsSolution {value} {world} {error} nameEq keyEq
  state@(MkSystemState ambient (MkCoeffectContext entries unique)) selected
  with (lookupEntries @{nameEq} selected entries) proof found
  supportSetIsSolution {value} {world} {error} nameEq keyEq
    state@(MkSystemState ambient (MkCoeffectContext entries unique)) selected |
    Nothing
    with (listMember @{nameEq} selected
      (supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
        {error = error} (length entries) entries [])) proof member
    supportSetIsSolution {value} {world} {error} nameEq keyEq
      state@(MkSystemState ambient (MkCoeffectContext entries unique)) selected |
      Nothing | False = Refl
    supportSetIsSolution {value} {world} {error} nameEq keyEq
      state@(MkSystemState ambient (MkCoeffectContext entries unique)) selected |
      Nothing | True =
        let finalSubset = supportFuelSubset @{nameEq} @{keyEq} (length entries)
              entries [] (emptyNamesSubset (bindingKeys entries))
            inFinal = listMemberTrueElem selected
              (supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
                {error = error} (length entries) entries []) member
            inEntries = finalSubset selected inFinal
        in void (lookupNothingNoElem selected entries found inEntries)
  supportSetIsSolution {value} {world} {error} nameEq keyEq
    state@(MkSystemState ambient (MkCoeffectContext entries unique)) selected |
    Just fiber
    with (listMember @{nameEq} selected
      (supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
        {error = error} (length entries) entries [])) proof member
    supportSetIsSolution {value} {world} {error} nameEq keyEq
      state@(MkSystemState ambient (MkCoeffectContext entries unique)) selected |
      Just fiber | True
      with (fiber) proof fiberCase
      supportSetIsSolution {value} {world} {error} nameEq keyEq
        state@(MkSystemState ambient (MkCoeffectContext entries unique)) selected |
        Just fiber | True | MkFiber component Root retiredFlag table lifecycle =
          case fiberCase of
            Refl =>
              let finalSound = supportFuelSound nameEq keyEq (length entries)
                    entries unique [] (emptySupportListSound nameEq keyEq entries)
                  candidateTrue = supportListSoundAtFound {value = value}
                    {world = world} {error = error} nameEq keyEq entries
                    (supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
                      {error = error} (length entries) entries []) finalSound
                    selected fiber found member
              in finishSupportCore nameEq keyEq entries
                (supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
                  {error = error} (length entries) entries []) selected fiber True
                candidateTrue
      supportSetIsSolution {value} {world} {error} nameEq keyEq
        state@(MkSystemState ambient (MkCoeffectContext entries unique)) selected |
        Just fiber | True | MkFiber component (ChildOf parent) retiredFlag table lifecycle =
          case fiberCase of
            Refl =>
              let finalSound = supportFuelSound nameEq keyEq (length entries)
                    entries unique [] (emptySupportListSound nameEq keyEq entries)
                  candidateTrue = supportListSoundAtFound {value = value}
                    {world = world} {error = error} nameEq keyEq entries
                    (supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
                      {error = error} (length entries) entries []) finalSound
                    selected fiber found member
              in finishSupportCore nameEq keyEq entries
                (supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
                  {error = error} (length entries) entries []) selected fiber True
                candidateTrue
    supportSetIsSolution {value} {world} {error} nameEq keyEq
      state@(MkSystemState ambient (MkCoeffectContext entries unique)) selected |
      Just fiber | False
      with (supportCandidate @{nameEq} @{keyEq} {value = value} {world = world}
        {error = error} entries
        (supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
          {error = error} (length entries) entries [])
        (Bind selected fiber)) proof candidate
      supportSetIsSolution {value} {world} {error} nameEq keyEq
        state@(MkSystemState ambient (MkCoeffectContext entries unique)) selected |
        Just fiber | False | False
        with (fiber) proof fiberCase
        supportSetIsSolution {value} {world} {error} nameEq keyEq
          state@(MkSystemState ambient (MkCoeffectContext entries unique)) selected |
          Just fiber | False | False | MkFiber component Root retiredFlag table lifecycle =
            case fiberCase of
              Refl => finishSupportCore nameEq keyEq entries
                (supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
                  {error = error} (length entries) entries []) selected fiber False
                candidate
        supportSetIsSolution {value} {world} {error} nameEq keyEq
          state@(MkSystemState ambient (MkCoeffectContext entries unique)) selected |
          Just fiber | False | False | MkFiber component (ChildOf parent) retiredFlag table lifecycle =
            case fiberCase of
              Refl => finishSupportCore nameEq keyEq entries
                (supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
                  {error = error} (length entries) entries []) selected fiber False
                candidate
      supportSetIsSolution {value} {world} {error} nameEq keyEq
        state@(MkSystemState ambient (MkCoeffectContext entries unique)) selected |
        Just fiber | False | True =
          let entryIn = lookupEntryElem selected entries fiber found
              appears = eligibleAppearsPass nameEq keyEq entries entries unique
                (supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
                  {error = error} (length entries) entries []) selected fiber
                entryIn member candidate
              stable = supportFuelLengthStable nameEq keyEq entries
              finalMember = trans
                (sym (cong (listMember @{nameEq} selected) stable)) appears
          in case trans (sym member) finalMember of Refl impossible


0 supportAndTrueLeft : (left, right : Bool) ->
  left && right = True -> left = True
supportAndTrueLeft False right eq = case eq of Refl impossible
supportAndTrueLeft True right eq = Refl

0 supportAndTrueRight : (left, right : Bool) ->
  left && right = True -> right = True
supportAndTrueRight False right eq = case eq of Refl impossible
supportAndTrueRight True right eq = eq

0 supportOrTrueRight : (left, right : Bool) ->
  right = True -> left || right = True
supportOrTrueRight False True Refl = Refl
supportOrTrueRight True right eq = Refl

0 supportBothTrue : (left, right : Bool) ->
  left = True -> right = True -> left && right = True
supportBothTrue True True Refl Refl = Refl
supportBothTrue False right eq rest = case eq of Refl impossible
supportBothTrue True False eq rest = case rest of Refl impossible

0 PredicateSubset : {name : Type} -> (name -> Bool) -> (name -> Bool) -> Type
PredicateSubset smaller larger = (selected : name) -> smaller selected = True ->
  larger selected = True

0 solutionProviderMonotone :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  DecEq name => DecEq key =>
  (smaller, larger : name -> Bool) -> PredicateSubset smaller larger ->
  (wanted : key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  providerFromPredicate {value = value} {world = world} {error = error} wanted smaller entries = True ->
  providerFromPredicate {value = value} {world = world} {error = error} wanted larger entries = True
solutionProviderMonotone smaller larger subset wanted [] eq =
  case eq of Refl impossible
solutionProviderMonotone smaller larger subset wanted
  (Bind selected fiber :: rest) eq
  with (smaller selected) proof smallerValue
  solutionProviderMonotone smaller larger subset wanted
    (Bind selected fiber :: rest) eq | False =
      supportOrTrueRight _ _
        (solutionProviderMonotone smaller larger subset wanted rest eq)
  solutionProviderMonotone smaller larger subset wanted
    (Bind selected fiber :: rest) eq | True
    with (listMember wanted
      (dependencies (componentProvisions (fiberComponent fiber)))) proof provides
    solutionProviderMonotone smaller larger subset wanted
      (Bind selected fiber :: rest) eq | True | False =
        supportOrTrueRight _ _
          (solutionProviderMonotone smaller larger subset wanted rest eq)
    solutionProviderMonotone smaller larger subset wanted
      (Bind selected fiber :: rest) eq | True | True =
        rewrite subset selected smallerValue in Refl

0 allProviderPredicatesMonotone :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  DecEq name => DecEq key =>
  (smaller, larger : name -> Bool) -> PredicateSubset smaller larger ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (wanted : List key) ->
  allList (\k => providerFromPredicate {value = value} {world = world} {error = error} k smaller entries) wanted = True ->
  allList (\k => providerFromPredicate {value = value} {world = world} {error = error} k larger entries) wanted = True
allProviderPredicatesMonotone smaller larger subset entries [] eq = Refl
allProviderPredicatesMonotone smaller larger subset entries (wanted :: rest) eq =
  let first = solutionProviderMonotone smaller larger subset wanted entries
        (supportAndTrueLeft _ _ eq)
      later = allProviderPredicatesMonotone smaller larger subset entries rest
        (supportAndTrueRight _ _ eq)
  in supportBothTrue _ _ first later

0 supportClausePredicateMonotone :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (smaller, larger : name -> Bool) -> PredicateSubset smaller larger ->
  (selected : name) -> (state : SystemState name key value world error) ->
  supportClause @{nameEq} @{keyEq} {value = value} {world = world} {error = error} smaller selected state = True ->
  supportClause @{nameEq} @{keyEq} {value = value} {world = world} {error = error} larger selected state = True
supportClausePredicateMonotone nameEq keyEq smaller larger subset selected
  state@(MkSystemState ambient (MkCoeffectContext entries unique)) eq
  with (lookupEntries @{nameEq} selected entries) proof found
  supportClausePredicateMonotone nameEq keyEq smaller larger subset selected
    state@(MkSystemState ambient (MkCoeffectContext entries unique)) eq |
    Nothing = case eq of Refl impossible
  supportClausePredicateMonotone nameEq keyEq smaller larger subset selected
    state@(MkSystemState ambient (MkCoeffectContext entries unique)) eq |
    Just fiber
    with (fiberParent fiber)
    supportClausePredicateMonotone nameEq keyEq smaller larger subset selected
      state@(MkSystemState ambient (MkCoeffectContext entries unique)) eq |
      Just fiber | Root =
        let active = supportAndTrueLeft _ _ eq
            dependenciesTrue = supportAndTrueRight _ _ eq
            dependenciesLarger = allProviderPredicatesMonotone smaller larger
              subset entries
              (dependencies (componentDependencies (fiberComponent fiber)))
              dependenciesTrue
        in supportBothTrue _ _ active dependenciesLarger
    supportClausePredicateMonotone nameEq keyEq smaller larger subset selected
      state@(MkSystemState ambient (MkCoeffectContext entries unique)) eq |
      Just fiber | ChildOf parent =
        let active = supportAndTrueLeft _ _ eq
            restTrue = supportAndTrueRight _ _ eq
            parentTrue = supportAndTrueLeft _ _ restTrue
            parentLarger = subset parent parentTrue
            dependenciesTrue = supportAndTrueRight _ _ restTrue
            dependenciesLarger = allProviderPredicatesMonotone smaller larger
              subset entries
              (dependencies (componentDependencies (fiberComponent fiber)))
              dependenciesTrue
        in supportBothTrue _ _ active
          (supportBothTrue _ _ parentLarger dependenciesLarger)

0 NamesSatisfy : {name : Type} -> List name -> (name -> Bool) -> Type
NamesSatisfy names predicate = (selected : name) -> Elem selected names ->
  predicate selected = True

namesSatisfyCons : {name : Type} -> {predicate : name -> Bool} -> {selected : name} ->
  {current : List name} -> predicate selected = True -> NamesSatisfy current predicate ->
  NamesSatisfy (selected :: current) predicate
namesSatisfyCons selectedTrue current selected Here = selectedTrue
namesSatisfyCons selectedTrue current other (There later) = current other later

emptyNamesSatisfy : {name : Type} -> {predicate : name -> Bool} ->
  NamesSatisfy [] predicate
emptyNamesSatisfy selected present impossible

0 supportPassEntriesSatisfiesSolution :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (scan : List (Binding name (FiberAt name key value world error))) ->
  (unique : UniqueKeys (bindingKeys entries)) ->
  EntriesSubset scan entries ->
  (candidate : name -> Bool) ->
  SupportSolution @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} candidate
    (MkSystemState ambient (MkCoeffectContext entries unique)) ->
  (current : List name) -> NamesSatisfy current candidate ->
  NamesSatisfy
    (supportPassEntries @{nameEq} @{keyEq} {value = value} {world = world}
      {error = error} entries scan current) candidate
supportPassEntriesSatisfiesSolution nameEq keyEq ambient entries [] unique scanSubset
  candidate solution current satisfies = satisfies
supportPassEntriesSatisfiesSolution {value} {world} {error} nameEq keyEq ambient
  entries (entry@(Bind selected fiber) :: rest) unique scanSubset candidate solution current
  satisfies with (listMember @{nameEq} selected current)
  supportPassEntriesSatisfiesSolution {value} {world} {error} nameEq keyEq
    ambient entries (entry@(Bind selected fiber) :: rest) unique scanSubset candidate
    solution current satisfies | True =
      supportPassEntriesSatisfiesSolution nameEq keyEq ambient entries rest unique
        (\later, present => scanSubset later (There present)) candidate solution current
        satisfies
  supportPassEntriesSatisfiesSolution {value} {world} {error} nameEq keyEq ambient
    entries (entry@(Bind selected fiber) :: rest) unique scanSubset candidate
    solution current satisfies | False
    with (not (retired fiber) &&
      (parentFromCandidate @{nameEq} (fiberParent fiber) current &&
       allList (\k => providerFromCandidate @{nameEq} @{keyEq} {value = value}
         {world = world} {error = error} k current entries)
         (dependencies (componentDependencies (fiberComponent fiber)))))
      proof eligible
    supportPassEntriesSatisfiesSolution {value} {world} {error} nameEq keyEq
      ambient entries (entry@(Bind selected fiber) :: rest) unique scanSubset candidate
      solution current satisfies | False | False =
        supportPassEntriesSatisfiesSolution nameEq keyEq ambient entries rest unique
          (\later, present => scanSubset later (There present)) candidate solution current
          satisfies
    supportPassEntriesSatisfiesSolution {value} {world} {error} nameEq keyEq
      ambient entries (entry@(Bind selected fiber) :: rest) unique scanSubset candidate
      solution current satisfies | False | True =
        let found = entryLookupFromElem entries unique selected fiber
              (scanSubset (Bind selected fiber) Here)
            clauseCandidate = supportClauseCandidate nameEq keyEq ambient entries
              unique current selected fiber found
            clauseCurrent = trans clauseCandidate eligible
            predicateSubset : PredicateSubset
              (\n => listMember @{nameEq} n current) candidate
            predicateSubset = \n, present => satisfies n (listMemberTrueElem n current present)
            selectedCandidate = trans (solution selected)
              (supportClausePredicateMonotone nameEq keyEq
                (\n => listMember @{nameEq} n current) candidate predicateSubset
                selected (MkSystemState ambient (MkCoeffectContext entries unique))
                clauseCurrent)
        in supportPassEntriesSatisfiesSolution nameEq keyEq ambient entries rest unique
          (\later, present => scanSubset later (There present)) candidate solution
          (selected :: current) (namesSatisfyCons selectedCandidate satisfies)


0 supportFuelSatisfiesSolution :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (unique : UniqueKeys (bindingKeys entries)) ->
  (candidate : name -> Bool) ->
  SupportSolution @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} candidate
    (MkSystemState ambient (MkCoeffectContext entries unique)) ->
  (fuel : Nat) -> (current : List name) -> NamesSatisfy current candidate ->
  NamesSatisfy
    (supportFuel @{nameEq} @{keyEq} {value = value} {world = world}
      {error = error} fuel entries current) candidate
supportFuelSatisfiesSolution nameEq keyEq ambient entries unique candidate solution
  Z current satisfies = satisfies
supportFuelSatisfiesSolution nameEq keyEq ambient entries unique candidate solution
  (S fuel) current satisfies =
    supportFuelSatisfiesSolution nameEq keyEq ambient entries unique candidate
      solution fuel (supportPass @{nameEq} @{keyEq} entries current)
      (supportPassEntriesSatisfiesSolution nameEq keyEq ambient entries entries
        unique entriesSubsetIdentity candidate solution current satisfies)

0 computedSupportIncludedInSolution :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  (candidate : name -> Bool) ->
  SupportSolution @{nameEq} @{keyEq} candidate state ->
  (selected : name) -> isSupported @{nameEq} @{keyEq} selected state = True ->
  candidate selected = True
computedSupportIncludedInSolution nameEq keyEq
  (MkSystemState ambient (MkCoeffectContext entries unique)) candidate solution
  selected present =
    supportFuelSatisfiesSolution nameEq keyEq ambient entries unique candidate
      solution (length entries) [] emptyNamesSatisfy selected
      (listMemberTrueElem selected
        (supportFuel @{nameEq} @{keyEq} (length entries) entries []) present)


0 RankCandidateIncluded :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) ->
  (state : SystemState name key value world error) ->
  (candidate : name -> Bool) -> (computed : List name) -> Nat -> Type
RankCandidateIncluded protocol nameEq state candidate computed rank =
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry state) = Just fiber ->
  registrationRank protocol (fiberComponent fiber) = Just rank ->
  candidate selected = True -> listMember @{nameEq} selected computed = True

0 providerCandidateIncludedBelow :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (unique : UniqueKeys (bindingKeys entries)) ->
  registry state = MkCoeffectContext entries unique ->
  RegistryProtocolRanked protocol nameEq state ->
  (candidate : name -> Bool) -> (computed : List name) ->
  (consumerName : name) ->
  (consumerFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} consumerName (registry state) = Just consumerFiber ->
  (consumerRank : Nat) ->
  registrationRank protocol (fiberComponent consumerFiber) = Just consumerRank ->
  ((providerRank : Nat) -> LT providerRank consumerRank ->
    RankCandidateIncluded protocol nameEq state candidate computed providerRank) ->
  (wanted : key) ->
  Elem wanted (dependencies (componentDependencies (fiberComponent consumerFiber))) ->
  (scan : List (Binding name (FiberAt name key value world error))) ->
  EntriesSubset scan entries ->
  providerFromPredicate {value = value} {world = world} {error = error}
    wanted candidate scan = True ->
  providerFromPredicate {value = value} {world = world} {error = error}
    wanted (\n => listMember @{nameEq} n computed) scan = True
providerCandidateIncludedBelow protocol nameEq keyEq state entries unique stateRegistry ranked
  candidate computed consumerName consumerFiber consumerFound consumerRank
  consumerRanked recurse wanted consumerDeclares [] scanSubset eq =
    case eq of Refl impossible
providerCandidateIncludedBelow {value} {world} {error} protocol nameEq keyEq state
  entries unique stateRegistry ranked candidate computed consumerName consumerFiber consumerFound
  consumerRank consumerRanked recurse wanted consumerDeclares
  (Bind providerName providerFiber :: rest) scanSubset eq
  with (candidate providerName) proof candidateProvider
  providerCandidateIncludedBelow {value} {world} {error} protocol nameEq keyEq state
    entries unique stateRegistry ranked candidate computed consumerName consumerFiber consumerFound
    consumerRank consumerRanked recurse wanted consumerDeclares
    (Bind providerName providerFiber :: rest) scanSubset eq | False =
      supportOrTrueRight _ _
        (providerCandidateIncludedBelow protocol nameEq keyEq state entries unique
          stateRegistry ranked candidate computed consumerName consumerFiber consumerFound
          consumerRank consumerRanked recurse wanted consumerDeclares rest
          (\entry, present => scanSubset entry (There present)) eq)
  providerCandidateIncludedBelow {value} {world} {error} protocol nameEq keyEq state
    entries unique stateRegistry ranked candidate computed consumerName consumerFiber consumerFound
    consumerRank consumerRanked recurse wanted consumerDeclares
    (Bind providerName providerFiber :: rest) scanSubset eq | True
    with (listMember @{keyEq} wanted
      (dependencies (componentProvisions (fiberComponent providerFiber)))) proof provides
    providerCandidateIncludedBelow {value} {world} {error} protocol nameEq keyEq state
      entries unique stateRegistry ranked candidate computed consumerName consumerFiber consumerFound
      consumerRank consumerRanked recurse wanted consumerDeclares
      (Bind providerName providerFiber :: rest) scanSubset eq | True | False =
        supportOrTrueRight _ _
          (providerCandidateIncludedBelow protocol nameEq keyEq state entries unique
            stateRegistry ranked candidate computed consumerName consumerFiber consumerFound
            consumerRank consumerRanked recurse wanted consumerDeclares rest
            (\entry, present => scanSubset entry (There present)) eq)
    providerCandidateIncludedBelow {value} {world} {error} protocol nameEq keyEq state
      entries unique stateRegistry ranked candidate computed consumerName consumerFiber consumerFound
      consumerRank consumerRanked recurse wanted consumerDeclares
      (Bind providerName providerFiber :: rest) scanSubset eq | True | True =
        let providerFound = entryLookupFromElem entries unique providerName providerFiber
              (scanSubset (Bind providerName providerFiber) Here)
            providerFoundState = trans
              (cong (lookupFiber @{nameEq} providerName) stateRegistry) providerFound
            (providerRank ** providerRanked) =
              ranked providerName providerFiber providerFoundState
            providerLower = precedenceRankIncreases protocol
              (fiberComponent providerFiber) (fiberComponent consumerFiber)
              providerRank consumerRank providerRanked consumerRanked wanted
              (listMemberTrueElem wanted
                (dependencies (componentProvisions (fiberComponent providerFiber)))
                provides)
              consumerDeclares
            providerComputed = recurse providerRank providerLower providerName
              providerFiber providerFoundState providerRanked candidateProvider
        in rewrite providerComputed in Refl

0 allCandidateProvidersIncludedBelow :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (unique : UniqueKeys (bindingKeys entries)) ->
  registry state = MkCoeffectContext entries unique ->
  RegistryProtocolRanked protocol nameEq state ->
  (candidate : name -> Bool) -> (computed : List name) ->
  (consumerName : name) ->
  (consumerFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} consumerName (registry state) = Just consumerFiber ->
  (consumerRank : Nat) ->
  registrationRank protocol (fiberComponent consumerFiber) = Just consumerRank ->
  ((providerRank : Nat) -> LT providerRank consumerRank ->
    RankCandidateIncluded protocol nameEq state candidate computed providerRank) ->
  (wanted : List key) ->
  NamesSubset wanted
    (dependencies (componentDependencies (fiberComponent consumerFiber))) ->
  allList (\k => providerFromPredicate {value = value} {world = world}
    {error = error} k candidate entries) wanted = True ->
  allList (\k => providerFromPredicate {value = value} {world = world}
    {error = error} k (\n => listMember @{nameEq} n computed) entries) wanted = True
allCandidateProvidersIncludedBelow protocol nameEq keyEq state entries unique stateRegistry ranked
  candidate computed consumerName consumerFiber consumerFound consumerRank
  consumerRanked recurse [] wantedSubset eq = Refl
allCandidateProvidersIncludedBelow protocol nameEq keyEq state entries unique stateRegistry ranked
  candidate computed consumerName consumerFiber consumerFound consumerRank
  consumerRanked recurse (wanted :: rest) wantedSubset eq =
    let first = providerCandidateIncludedBelow protocol nameEq keyEq state entries unique
          stateRegistry ranked candidate computed consumerName consumerFiber consumerFound consumerRank
          consumerRanked recurse wanted (wantedSubset wanted Here) entries
          entriesSubsetIdentity (supportAndTrueLeft _ _ eq)
        later = allCandidateProvidersIncludedBelow protocol nameEq keyEq state entries
          unique stateRegistry ranked candidate computed consumerName consumerFiber consumerFound
          consumerRank consumerRanked recurse rest
          (\key, present => wantedSubset key (There present))
          (supportAndTrueRight _ _ eq)
    in supportBothTrue _ _ first later

0 stableEligibleMember :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (unique : UniqueKeys (bindingKeys entries)) ->
  (supported : List name) -> (selected : name) ->
  (fiber : Fiber name key value world error) ->
  Elem (Bind selected fiber) entries ->
  supportCandidate @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} entries supported (Bind selected fiber) = True ->
  supportPass @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} entries supported = supported ->
  listMember @{nameEq} selected supported = True
stableEligibleMember nameEq keyEq entries unique supported selected fiber present
  eligible stable with (listMember @{nameEq} selected supported) proof member
  stableEligibleMember nameEq keyEq entries unique supported selected fiber present
    eligible stable | True = Refl
  stableEligibleMember nameEq keyEq entries unique supported selected fiber present
    eligible stable | False =
      let appears = eligibleAppearsPass nameEq keyEq entries entries unique supported
            selected fiber present member eligible
          finalMember = trans
            (sym (cong (listMember @{nameEq} selected) stable)) appears
      in case trans (sym member) finalMember of Refl impossible


0 supportClausePredicateAtFound :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (unique : UniqueKeys (bindingKeys entries)) ->
  (predicate : name -> Bool) -> (selected : name) ->
  (fiber : Fiber name key value world error) ->
  lookupEntries @{nameEq} selected entries = Just fiber ->
  supportClause @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} predicate selected
    (MkSystemState ambient (MkCoeffectContext entries unique)) =
  (not (retired fiber) &&
    ((case fiberParent fiber of
      Root => True
      ChildOf parent => predicate parent) &&
     allList (\k => providerFromPredicate {value = value} {world = world}
       {error = error} k predicate entries)
       (dependencies (componentDependencies (fiberComponent fiber)))))
supportClausePredicateAtFound nameEq keyEq ambient entries unique predicate selected
  fiber@(MkFiber component Root retiredFlag table lifecycle) found =
    rewrite found in Refl
supportClausePredicateAtFound nameEq keyEq ambient entries unique predicate selected
  fiber@(MkFiber component (ChildOf parent) retiredFlag table lifecycle) found =
    rewrite found in Refl

0 candidateFiberIncludedFromLowerRanks :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (unique : UniqueKeys (bindingKeys entries)) ->
  RegistryProtocolRanked protocol nameEq
    (MkSystemState ambient (MkCoeffectContext entries unique)) ->
  RegistryParentRanksIncrease protocol nameEq
    (MkSystemState ambient (MkCoeffectContext entries unique)) ->
  (candidate : name -> Bool) ->
  SupportSolution @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} candidate
    (MkSystemState ambient (MkCoeffectContext entries unique)) ->
  (computed : List name) ->
  supportPass @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} entries computed = computed ->
  (rank : Nat) ->
  ((lowerRank : Nat) -> LT lowerRank rank ->
    RankCandidateIncluded protocol nameEq
      (MkSystemState ambient (MkCoeffectContext entries unique))
      candidate computed lowerRank) ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupEntries @{nameEq} selected entries = Just fiber ->
  registrationRank protocol (fiberComponent fiber) = Just rank ->
  candidate selected = True -> listMember @{nameEq} selected computed = True
candidateFiberIncludedFromLowerRanks {value} {world} {error} protocol nameEq keyEq
  ambient entries unique ranked parentOrdered candidate solution computed stable rank
  recurse selected
  fiber@(MkFiber component Root retiredFlag table lifecycle) found fiberRanked
  candidateTrue =
    let 0 clauseCore = supportClausePredicateAtFound nameEq keyEq ambient
          entries unique candidate selected fiber found
        0 clauseTrue = trans (sym clauseCore)
          (trans (sym (solution selected)) candidateTrue)
        0 active = supportAndTrueLeft _ _ clauseTrue
        0 providersCandidate = supportAndTrueRight _ _ clauseTrue
        0 providersComputed = allCandidateProvidersIncludedBelow protocol nameEq keyEq
          (MkSystemState ambient (MkCoeffectContext entries unique)) entries unique
          Refl ranked candidate computed selected fiber found rank fiberRanked recurse
          (dependencies (componentDependencies component)) (\key, present => present)
          providersCandidate
        0 providersEquation = allProviderPredicatesCandidate {value = value}
          {world = world} {error = error} nameEq keyEq
          (dependencies (componentDependencies component)) computed entries
        0 providersForCandidate = trans (sym providersEquation) providersComputed
        0 eligible = supportBothTrue _ _ active providersForCandidate
        0 present = lookupEntryElem selected entries fiber found
    in stableEligibleMember nameEq keyEq entries unique computed selected fiber present
      eligible stable
candidateFiberIncludedFromLowerRanks {value} {world} {error} protocol nameEq keyEq
  ambient entries unique ranked parentOrdered candidate solution computed stable rank
  recurse selected
  fiber@(MkFiber component (ChildOf parent) retiredFlag table lifecycle) found
  fiberRanked candidateTrue =
    let 0 clauseCore = supportClausePredicateAtFound nameEq keyEq ambient
          entries unique candidate selected fiber found
        0 clauseTrue = trans (sym clauseCore)
          (trans (sym (solution selected)) candidateTrue)
        0 active = supportAndTrueLeft _ _ clauseTrue
        0 restTrue = supportAndTrueRight _ _ clauseTrue
        0 parentCandidate = supportAndTrueLeft _ _ restTrue
        0 providersCandidate = supportAndTrueRight _ _ restTrue
        0 witness = parentOrdered parent selected fiber found Refl
        0 sameChildRank = maybeJustInjective
          (trans (sym (childComponentRanked witness)) fiberRanked)
        0 parentLower = replace {p = \childRank =>
            LT (parentRank witness) childRank}
          sameChildRank (parentRankLower witness)
        0 parentComputed = recurse (parentRank witness) parentLower parent
          (parentFiber witness) (parentFound witness)
          (parentComponentRanked witness) parentCandidate
        0 providersComputed = allCandidateProvidersIncludedBelow protocol nameEq keyEq
          (MkSystemState ambient (MkCoeffectContext entries unique)) entries unique
          Refl ranked candidate computed selected fiber found rank fiberRanked recurse
          (dependencies (componentDependencies component)) (\key, present => present)
          providersCandidate
        0 providersEquation = allProviderPredicatesCandidate {value = value}
          {world = world} {error = error} nameEq keyEq
          (dependencies (componentDependencies component)) computed entries
        0 providersForCandidate = trans (sym providersEquation) providersComputed
        0 eligible = supportBothTrue _ _ active
          (supportBothTrue _ _ parentComputed providersForCandidate)
        0 present = lookupEntryElem selected entries fiber found
    in stableEligibleMember nameEq keyEq entries unique computed selected fiber present
      eligible stable

0 candidateIncludedAtAccessibleRank :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (unique : UniqueKeys (bindingKeys entries)) ->
  RegistryProtocolRanked protocol nameEq
    (MkSystemState ambient (MkCoeffectContext entries unique)) ->
  RegistryParentRanksIncrease protocol nameEq
    (MkSystemState ambient (MkCoeffectContext entries unique)) ->
  (candidate : name -> Bool) ->
  SupportSolution @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} candidate
    (MkSystemState ambient (MkCoeffectContext entries unique)) ->
  (computed : List name) ->
  supportPass @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} entries computed = computed ->
  (rank : Nat) -> Accessible LT rank ->
  RankCandidateIncluded protocol nameEq
    (MkSystemState ambient (MkCoeffectContext entries unique))
    candidate computed rank
candidateIncludedAtAccessibleRank protocol nameEq keyEq ambient entries unique
  ranked parentOrdered candidate solution computed stable rank (Access smaller)
  selected fiber found fiberRanked candidateTrue =
    candidateFiberIncludedFromLowerRanks protocol nameEq keyEq ambient entries unique
      ranked parentOrdered candidate solution computed stable rank
      (\lowerRank, lower =>
        candidateIncludedAtAccessibleRank protocol nameEq keyEq ambient entries unique
          ranked parentOrdered candidate solution computed stable lowerRank
          (smaller lowerRank lower))
      selected fiber found fiberRanked candidateTrue


0 supportClausePredicateAtNothing :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (predicate : name -> Bool) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  lookupFiber @{nameEq} {value = value} {world = world} {error = error}
    selected (registry state) = Nothing ->
  supportClause @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} predicate selected state = False
supportClausePredicateAtNothing nameEq keyEq predicate selected
  (MkSystemState ambient (MkCoeffectContext entries unique)) absent =
    rewrite absent in Refl

0 candidateIncludedInComputedSupport :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  RegistryProtocolRanked protocol nameEq state ->
  RegistryParentRanksIncrease protocol nameEq state ->
  (candidate : name -> Bool) ->
  SupportSolution @{nameEq} @{keyEq} candidate state ->
  (selected : name) -> candidate selected = True ->
  isSupported @{nameEq} @{keyEq} selected state = True
candidateIncludedInComputedSupport protocol nameEq keyEq
  (MkSystemState ambient (MkCoeffectContext entries unique)) ranked
  parentOrdered candidate solution selected candidateTrue
  with (lookupEntries @{nameEq} selected entries) proof found
  candidateIncludedInComputedSupport protocol nameEq keyEq
    (MkSystemState ambient (MkCoeffectContext entries unique)) ranked
    parentOrdered candidate solution selected candidateTrue | Nothing =
      let 0 absentClause = supportClausePredicateAtNothing nameEq keyEq candidate
            selected (MkSystemState ambient (MkCoeffectContext entries unique)) found
          0 candidateFalse = trans (solution selected) absentClause
      in case trans (sym candidateTrue) candidateFalse of Refl impossible
  candidateIncludedInComputedSupport protocol nameEq keyEq
    (MkSystemState ambient (MkCoeffectContext entries unique)) ranked
    parentOrdered candidate solution selected candidateTrue | Just fiber =
      let 0 (rank ** fiberRanked) = ranked selected fiber found
      in candidateIncludedAtAccessibleRank protocol nameEq keyEq ambient entries
        unique ranked parentOrdered candidate solution
        (supportFuel @{nameEq} @{keyEq} (length entries) entries [])
        (supportFuelLengthStable nameEq keyEq entries) rank
        (wellFounded {rel = LT} rank) selected fiber found fiberRanked candidateTrue

0 boolEqualFromTrueIff : (left, right : Bool) ->
  (left = True -> right = True) ->
  (right = True -> left = True) -> left = right
boolEqualFromTrueIff False False forward backward = Refl
boolEqualFromTrueIff False True forward backward =
  case backward Refl of Refl impossible
boolEqualFromTrueIff True False forward backward =
  case forward Refl of Refl impossible
boolEqualFromTrueIff True True forward backward = Refl

||| Any Definition-67 Boolean solution equals the executable bounded closure.
public export
0 supportSolutionUniqueFromRanks :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  RegistryProtocolRanked protocol nameEq state ->
  RegistryParentRanksIncrease protocol nameEq state ->
  (candidate : name -> Bool) ->
  SupportSolution @{nameEq} @{keyEq} candidate state ->
  (selected : name) ->
  candidate selected = isSupported @{nameEq} @{keyEq} selected state
supportSolutionUniqueFromRanks protocol nameEq keyEq state ranked parentOrdered
  candidate solution selected =
    boolEqualFromTrueIff (candidate selected)
      (isSupported @{nameEq} @{keyEq} selected state)
      (candidateIncludedInComputedSupport protocol nameEq keyEq state ranked
        parentOrdered candidate solution selected)
      (computedSupportIncludedInSolution nameEq keyEq state candidate solution selected)


||| Constructive implementation of the accepted paper-Lemma-68 statement.
||| The precedence-acyclic premise is redundant once the stronger protocol-rank
||| invariant has been recovered from the aligned reached trace.
public export
0 supportWellFoundedTheoremProof :
  (name : Type) -> (key : Type) -> (value : key -> Type) ->
  (world, error : Type) -> supportWellFoundedTheorem name key value world error
supportWellFoundedTheoremProof name key value world error nameEq keyEq protocol
  state reached provenance precedenceAcyclic =
    let 0 ranked = reachedRegistryProtocolRanked protocol nameEq keyEq reached provenance
        0 parentOrdered = reachedRegistryParentRanksIncrease protocol nameEq keyEq
          reached provenance
        0 combined = supportCombinedWellFounded protocol nameEq state ranked parentOrdered
    in MkSupportWellFoundedResult combined
      (supportSolutionUniqueFromRanks protocol nameEq keyEq state ranked parentOrdered)

0 registrationStepDisciplineProvenance :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) ->
  (action : Action name key value world error) ->
  (before : SystemState name key value world error) ->
  {afterState, finalState : SystemState name key value world error} ->
  (rest : Transitions afterState finalState) ->
  RegistrationStepDiscipline protocol nameEq action before rest ->
  RegistrationStepProvenance protocol nameEq action before
registrationStepDisciplineProvenance protocol nameEq
  (OInsert child Root component) before rest ranked = ranked
registrationStepDisciplineProvenance protocol nameEq
  (OInsert child (ChildOf parent) component) before rest
  (provenance, retirement) = provenance
registrationStepDisciplineProvenance protocol nameEq (ORetire child) before rest step = ()
registrationStepDisciplineProvenance protocol nameEq (ORemove child) before rest step = ()
registrationStepDisciplineProvenance protocol nameEq (LBegin child) before rest step = ()
registrationStepDisciplineProvenance protocol nameEq (LAdvance child) before rest step = ()
registrationStepDisciplineProvenance protocol nameEq (LDivert child) before rest step = ()
registrationStepDisciplineProvenance protocol nameEq (LLeave child) before rest step = ()
registrationStepDisciplineProvenance protocol nameEq (LUnload child) before rest step = ()

||| RegistrationDiscipline entails the exact provenance fragment needed by
||| Lemma 68; its additional child-retirement witness is intentionally erased.
public export
0 registrationDisciplineProvenance :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) ->
  (trace : Transitions first finalState) ->
  RegistrationDiscipline protocol nameEq trace ->
  RegistrationProvenance protocol nameEq trace
registrationDisciplineProvenance protocol nameEq NoTransitions
  RegistrationDisciplineEnd = RegistrationProvenanceEnd
registrationDisciplineProvenance protocol nameEq
  (MoreTransitions transition rest)
  (RegistrationDisciplineStep transition rest stepDiscipline tailDiscipline) =
    RegistrationProvenanceStep transition rest
      (registrationStepDisciplineProvenance protocol nameEq
        (transitionAction transition) _ rest stepDiscipline)
      (registrationDisciplineProvenance protocol nameEq rest tailDiscipline)

||| Stronger entry point phrased directly with RegistrationDiscipline, as used
||| by the CP4 constructive-proof program.
public export
0 supportWellFoundedUnderDiscipline :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (state : SystemState name key value world error) ->
  (reached : ReachedFromEmpty name key world error value nameEq keyEq state) ->
  RegistrationDiscipline protocol nameEq (reachTrace reached) ->
  PrecedenceAcyclic nameEq state ->
  SupportWellFoundedResult name key world error value nameEq keyEq state
supportWellFoundedUnderDiscipline nameEq keyEq protocol state reached discipline
  precedenceAcyclic =
    supportWellFoundedTheoremProof name key value world error nameEq keyEq protocol
      state reached
      (registrationDisciplineProvenance protocol nameEq (reachTrace reached) discipline)
      precedenceAcyclic
