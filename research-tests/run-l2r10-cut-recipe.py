#!/usr/bin/env python3
"""L2R10 native move-cut observation recipe, using L2R9's one-declaration pattern.
Not a move or square producer. Writes one requested total observation helper
only, to the absolute lane2-owned file. No compiler/commit/main-tree operations.
"""
from pathlib import Path
import sys
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
p=ROOT/'research-tests/O6-L2R10-Sources/DGamma/L2R10MoveCutObservation.idr'
unit=sys.argv[1]
base='''  {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 initial, finalState : SystemState name key value world error} ->
  {0 trace : Transitions initial finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
'''
entry='''  (entry : RootCatalogEntry name key world error value) ->
  (before, after : List (RootCatalogEntry name key world error value)) ->
  (predecessor : Nat) ->
  (0 member : Elem entry (scanRootCatalog 0 trail)) ->
  (0 split : scanRootCatalog 0 trail = before ++ entry :: after) ->
  (0 zeros : All (\\item => rootDistance nameEq keyEq trail (catalogOrdinal item) = 0) before) ->
  (0 positive : rootDistance nameEq keyEq trail (catalogOrdinal entry) = S predecessor) ->
'''
query="head' (drop (pred (catalogOrdinal entry)) (trailSourceActions trail))"
pair='(SystemState name key value world error, Action name key value world error)'
result='  Maybe (SelectedSquareCut name key world error value nameEq keyEq trail)\n'
args='nameEq keyEq trail entry before after predecessor member split zeros positive'
imp='{name} {key} {world} {error} {value}'
if unit=='D5':
 name='selectedCutAtPair'
 text='''\n||| Eliminate the already observed source/action PAIR once. Source classifier,
||| native early-root evaluator, and catalog-birth decoding are computed HERE.
public export
selectedCutAtPair :
'''+base+entry+f'''  (observed : {pair}) ->
  (0 equation : {query} = Just observed) ->
'''+result
 text+=f'''{name} {imp} {args} (source, action) equation =
  Just (MkSelectedSquareCut entry before after predecessor source action
    (classifyPredecessor nameEq (catalogRoot entry) source action)
    (checkedApplyAction {{name}} {{key}} {{value}} {{world}} {{error}} @{{nameEq}} @{{keyEq}}
      (OInsert (catalogRoot entry) Root (catalogComponent entry)) source)
    Refl member split zeros positive equation (scanCatalogBirth 0 trail entry member))
'''
elif unit=='D6':
 name='selectedCutAtLookup'
 text='''\n||| Eliminate ONLY the explicit predecessor-data Maybe. Nothing is retained
||| honestly; no native predecessor existence or move is supplied by fiat.
public export
selectedCutAtLookup :
'''+base+entry+f'''  (observed : Maybe {pair}) ->
  (0 equation : {query} = observed) ->
'''+result
 text+=f'''{name} {args} Nothing equation = Nothing
{name} {args} (Just observed) equation =
  selectedCutAtPair {args} observed equation
'''
elif unit=='D7':
 name='selectedCutAtSearch'
 text='''\n||| Consume the explicitly observed ACTUAL first-positive search. Earlier
||| zero distances, catalog split, and positive equation remain in the result.
public export
selectedCutAtSearch :
'''+base+'''  (distance : RootCatalogEntry name key world error value -> Nat) ->
  (items : List (RootCatalogEntry name key world error value)) ->
  (0 distanceEquation : (\\entry => rootDistance nameEq keyEq trail (catalogOrdinal entry)) = distance) ->
  (0 catalogEquation : scanRootCatalog 0 trail = items) ->
  (observed : DistanceSearch distance items) ->
  (0 equation : searchDistance distance items = observed) ->
'''+result
 text+=f'''{name} nameEq keyEq trail distance items distanceEquation catalogEquation (AllDistancesZero zeros) equation = Nothing
{name} nameEq keyEq trail distance items distanceEquation catalogEquation (FoundFirstPositive entry before after predecessor member split zeros positive) equation =
  selectedCutAtLookup nameEq keyEq trail entry before after predecessor
    (replace {{p = Elem entry}} (sym catalogEquation) member)
    (trans catalogEquation split)
    (replace {{p = \\fn => All (\\item => fn item = 0) before}} (sym distanceEquation) zeros)
    (trans (cong (\\fn => fn entry) distanceEquation) positive)
    ({query}) Refl
'''
elif unit=='D8':
 name='observeSelectedMoveCut'
 text='''\n||| GENERAL executable, oracle-free square-availability REQUEST producer.
||| Selects through selectNativeDistanceRoot, reads its actual predecessor
||| position, classifies the native source/action and executes early OInsert.
||| It does NOT assume success, cross replay, endpoints, forcing or decrement;
||| hence it is not produceAdmittedDistanceMove or a terminating normalizer.
public export
observeSelectedMoveCut :
'''+base+result
 text+=f'''{name} nameEq keyEq trail =
  selectedCutAtSearch nameEq keyEq trail
    (\\entry => rootDistance nameEq keyEq trail (catalogOrdinal entry)) (scanRootCatalog 0 trail) Refl Refl
    (nativeSearch (selectNativeDistanceRoot nameEq keyEq trail))
    (nativeSearchEquation (selectNativeDistanceRoot nameEq keyEq trail))
'''
else:raise SystemExit('Unknown requested unit')
s=p.read_text();assert name+' :' not in s
p.write_text(s+text)
print(unit,name,p)
