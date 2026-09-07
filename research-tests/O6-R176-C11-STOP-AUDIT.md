# R176 C11 mandatory 3/3 stop

C11 `canonicalWorkRankStepProgress` exhausted exactly three compiler attempts.
All failed source is REMOVED. C12 is UNSPENT; no fourth attempt or replacement
helper was started. Retained C1–C10 are separately checked/committed. The working
CanonicalSort source is restored to the last successful declaration prefix;
its dependency refresh will be validated only under the supervisor gate.

## Semantic result and exact wall

C1–C8 prove the actual sealed suffix preserves R175 rank segments and the actual
reached worklist has the exact transposed rank-fold measure under the SAME fixed
order. They do not choose an applicable descending pair or prove strict decrease.
C9–C10 define structural segmented rank progress and prove its WHOLE-sum drop.

C11 tried to lift that structural packet through one actual untouched prefix
action while preserving every unowned barrier. Attempt 1 used the imported
`rankLiftProgress`; its export-level body is opaque, so its target projections
cannot be identified definitionally. Attempt 2 opened the genuine rank packet
and constructed the lifted packet directly, using the same R175 arithmetic.
The rewrite failed at the computed ownership-rank/first-segment decrease field;
the diagnostic exposes captured erased source/target lets, not a false theorem.
Attempt 3 made the packet's exact source index explicit, but reproduced that
same rewrite rejection. These compiler failures are NOT semantic countermodels.
No additional spelling, helper, visibility change, or fourth probe was made.

Remaining: check a concrete pair selected from the authentic reached rank
segments; derive its required orientation/early applicability; construct the
local descending packet together with that actual result; lift through the
whole prefix and close actual worklist decrease. Abstract `rankSelectProgress`
remains insufficient by itself. Old unconditional grouping may cycle and is
NOT restored. Root placement and O17/O19/O21 bodies remain untouched.

## Full charged transcripts and removed declarations

### C11 attempt 1/3

```idris
||| Lift an authentic segmented rank choice through one ACTUAL prefix action.
||| Owned actions extend the same first segment; unowned actions retain a
||| barrier. No action is dropped, reordered, or classified as root placement.
0 canonicalWorkRankStepProgress :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (fixedOrder : List name) ->
  (action : Action name key value world error) ->
  {source, target : List (List Nat)} -> (SegmentedRankProgress source target) ->
  (SegmentedRankProgress
    (canonicalWorkRankStep name key world error value nameEq fixedOrder action source)
    (canonicalWorkRankStep name key world error value nameEq fixedOrder action target))
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (OInsert child Root component)
  (FirstRankSegment {sourceHead} later progress) =
    LaterRankSegment [] (FirstRankSegment later progress)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (OInsert child Root component)
  (LaterRankSegment untouched later) =
    LaterRankSegment [] (LaterRankSegment untouched later)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (OInsert child (ChildOf parent) component)
  (FirstRankSegment {sourceHead} later progress) =
    FirstRankSegment later (rankLiftProgress (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
      Yes same => False
      No distinct => True) fixedOrder)) sourceHead progress)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (OInsert child (ChildOf parent) component)
  (LaterRankSegment untouched later) =
    LaterRankSegment ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
      Yes same => False
      No distinct => True) fixedOrder)) :: untouched) later
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (ORetire actor)
  (FirstRankSegment {sourceHead} later progress) =
    LaterRankSegment [] (FirstRankSegment later progress)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (ORetire actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment [] (LaterRankSegment untouched later)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (ORemove actor)
  (FirstRankSegment {sourceHead} later progress) =
    LaterRankSegment [] (FirstRankSegment later progress)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (ORemove actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment [] (LaterRankSegment untouched later)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LBegin actor)
  (FirstRankSegment {sourceHead} later progress) =
    FirstRankSegment later (rankLiftProgress (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
      Yes same => False
      No distinct => True) fixedOrder)) sourceHead progress)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LBegin actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
      Yes same => False
      No distinct => True) fixedOrder)) :: untouched) later
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LAdvance actor)
  (FirstRankSegment {sourceHead} later progress) =
    FirstRankSegment later (rankLiftProgress (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
      Yes same => False
      No distinct => True) fixedOrder)) sourceHead progress)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LAdvance actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
      Yes same => False
      No distinct => True) fixedOrder)) :: untouched) later
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LDivert actor)
  (FirstRankSegment {sourceHead} later progress) =
    FirstRankSegment later (rankLiftProgress (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
      Yes same => False
      No distinct => True) fixedOrder)) sourceHead progress)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LDivert actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
      Yes same => False
      No distinct => True) fixedOrder)) :: untouched) later
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LLeave actor)
  (FirstRankSegment {sourceHead} later progress) =
    FirstRankSegment later (rankLiftProgress (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
      Yes same => False
      No distinct => True) fixedOrder)) sourceHead progress)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LLeave actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
      Yes same => False
      No distinct => True) fixedOrder)) :: untouched) later
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LUnload actor)
  (FirstRankSegment {sourceHead} later progress) =
    FirstRankSegment later (rankLiftProgress (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
      Yes same => False
      No distinct => True) fixedOrder)) sourceHead progress)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LUnload actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
      Yes same => False
      No distinct => True) fixedOrder)) :: untouched) later

```

```text
START C11-1 2026-09-07T02:19:00.377386+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
END {"unit": "C11-1", "start": "2026-09-07T02:19:00.377386+00:00", "end": "2026-09-07T02:19:55.364363+00:00", "exit": 1, "maxSampleRSSKiB": 17970416, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr", "diagnosticErrors": true}
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted

Error: While processing right hand side of canonicalWorkRankStepProgress. Can't solve constraint between: rankedPrefix (rankLiftProgress (length (takeWhile (\candidate => case decEq candidate parent of { Yes same => False ; No distinct => True }) fixedOrder)) sourceHead progress) ++ (rankedRight (rankLiftProgress (length (takeWhile (\candidate => case decEq candidate parent of { Yes same => False ; No distinct => True }) fixedOrder)) sourceHead progress) :: (rankedLeft (rankLiftProgress (length (takeWhile (\candidate => case decEq candidate parent of { Yes same => False ; No distinct => True }) fixedOrder)) sourceHead progress) :: rankedSuffix (rankLiftProgress (length (takeWhile (\candidate => case decEq candidate parent of { Yes same => False ; No distinct => True }) fixedOrder)) sourceHead progress))) and length (takeWhile (\candidate => case decEq candidate parent of { Yes same => False ; No distinct => True }) fixedOrder) :: (rankedPrefix progress ++ (rankedRight progress :: (rankedLeft progress :: rankedSuffix progress))).

DGamma.CP5ConfluenceCanonicalSortSpike:5224:5--5226:61
 5224 |     FirstRankSegment later (rankLiftProgress (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
 5225 |       Yes same => False
 5226 |       No distinct => True) fixedOrder)) sourceHead progress)



```

### C11 attempt 2/3

```idris
||| Lift an authentic segmented rank choice through one ACTUAL prefix action.
||| Owned actions extend the same first segment; unowned actions retain a
||| barrier. No action is dropped, reordered, or classified as root placement.
0 canonicalWorkRankStepProgress :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (fixedOrder : List name) ->
  (action : Action name key value world error) ->
  {source, target : List (List Nat)} -> (SegmentedRankProgress source target) ->
  (SegmentedRankProgress
    (canonicalWorkRankStep name key world error value nameEq fixedOrder action source)
    (canonicalWorkRankStep name key world error value nameEq fixedOrder action target))
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (OInsert child Root component)
  (FirstRankSegment later progress) =
    LaterRankSegment [] (FirstRankSegment later progress)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (OInsert child Root component)
  (LaterRankSegment untouched later) =
    LaterRankSegment [] (LaterRankSegment untouched later)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (OInsert child (ChildOf parent) component)
  (FirstRankSegment later (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased)) =
    FirstRankSegment later (MkRankedAdjacentProgress ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
        Yes same => False
        No distinct => True) fixedOrder)) :: prior) lower upper suffix
      (cong ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
        Yes same => False
        No distinct => True) fixedOrder)) ::) exact)
      (\pivot => cong (rankCrossing pivot (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
        Yes same => False
        No distinct => True) fixedOrder)) +) (weights pivot))
      (rewrite weights (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
        Yes same => False
        No distinct => True) fixedOrder)) in
       rewrite decreased in
         sym (plusSuccRightSucc
           (foldr (+) Z (map (rankCrossing (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
        Yes same => False
        No distinct => True) fixedOrder))) (prior ++ upper :: lower :: suffix)))
           (rankInversions (prior ++ upper :: lower :: suffix)))))
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (OInsert child (ChildOf parent) component)
  (LaterRankSegment untouched later) =
    LaterRankSegment ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
        Yes same => False
        No distinct => True) fixedOrder)) :: untouched) later
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (ORetire actor)
  (FirstRankSegment later progress) =
    LaterRankSegment [] (FirstRankSegment later progress)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (ORetire actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment [] (LaterRankSegment untouched later)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (ORemove actor)
  (FirstRankSegment later progress) =
    LaterRankSegment [] (FirstRankSegment later progress)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (ORemove actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment [] (LaterRankSegment untouched later)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LBegin actor)
  (FirstRankSegment later (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased)) =
    FirstRankSegment later (MkRankedAdjacentProgress ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: prior) lower upper suffix
      (cong ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) ::) exact)
      (\pivot => cong (rankCrossing pivot (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) +) (weights pivot))
      (rewrite weights (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) in
       rewrite decreased in
         sym (plusSuccRightSucc
           (foldr (+) Z (map (rankCrossing (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder))) (prior ++ upper :: lower :: suffix)))
           (rankInversions (prior ++ upper :: lower :: suffix)))))
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LBegin actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: untouched) later
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LAdvance actor)
  (FirstRankSegment later (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased)) =
    FirstRankSegment later (MkRankedAdjacentProgress ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: prior) lower upper suffix
      (cong ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) ::) exact)
      (\pivot => cong (rankCrossing pivot (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) +) (weights pivot))
      (rewrite weights (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) in
       rewrite decreased in
         sym (plusSuccRightSucc
           (foldr (+) Z (map (rankCrossing (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder))) (prior ++ upper :: lower :: suffix)))
           (rankInversions (prior ++ upper :: lower :: suffix)))))
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LAdvance actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: untouched) later
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LDivert actor)
  (FirstRankSegment later (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased)) =
    FirstRankSegment later (MkRankedAdjacentProgress ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: prior) lower upper suffix
      (cong ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) ::) exact)
      (\pivot => cong (rankCrossing pivot (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) +) (weights pivot))
      (rewrite weights (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) in
       rewrite decreased in
         sym (plusSuccRightSucc
           (foldr (+) Z (map (rankCrossing (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder))) (prior ++ upper :: lower :: suffix)))
           (rankInversions (prior ++ upper :: lower :: suffix)))))
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LDivert actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: untouched) later
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LLeave actor)
  (FirstRankSegment later (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased)) =
    FirstRankSegment later (MkRankedAdjacentProgress ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: prior) lower upper suffix
      (cong ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) ::) exact)
      (\pivot => cong (rankCrossing pivot (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) +) (weights pivot))
      (rewrite weights (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) in
       rewrite decreased in
         sym (plusSuccRightSucc
           (foldr (+) Z (map (rankCrossing (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder))) (prior ++ upper :: lower :: suffix)))
           (rankInversions (prior ++ upper :: lower :: suffix)))))
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LLeave actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: untouched) later
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LUnload actor)
  (FirstRankSegment later (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased)) =
    FirstRankSegment later (MkRankedAdjacentProgress ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: prior) lower upper suffix
      (cong ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) ::) exact)
      (\pivot => cong (rankCrossing pivot (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) +) (weights pivot))
      (rewrite weights (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) in
       rewrite decreased in
         sym (plusSuccRightSucc
           (foldr (+) Z (map (rankCrossing (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder))) (prior ++ upper :: lower :: suffix)))
           (rankInversions (prior ++ upper :: lower :: suffix)))))
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LUnload actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: untouched) later

```

```text
START C11-2 2026-09-07T02:20:50.758772+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
END {"unit": "C11-2", "start": "2026-09-07T02:20:50.758772+00:00", "end": "2026-09-07T02:21:45.751546+00:00", "exit": 1, "maxSampleRSSKiB": 17952400, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr", "diagnosticErrors": true}
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted

Error: While processing right hand side of canonicalWorkRankStepProgress. Rewriting by foldr (+) 0 (map (rankCrossing ?pivot) sourceHead) = foldr (+) 0 (map (rankCrossing ?pivot) (prior ++ (upper :: (lower :: suffix)))) did not change type rankInversions (length (takeWhile (\candidate => let 0 target = (rankedPrefix (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) ++ (rankedRight (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) :: (rankedLeft (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) :: rankedSuffix (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased)))) :: later in let 0 source = sourceHead :: later in case decEq candidate parent of { Yes same => False ; No distinct => True }) fixedOrder) :: sourceHead) = S (rankInversions ((length (takeWhile (\candidate => let 0 target = (rankedPrefix (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) ++ (rankedRight (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) :: (rankedLeft (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) :: rankedSuffix (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased)))) :: later in let 0 source = sourceHead :: later in case decEq candidate parent of { Yes same => False ; No distinct => True }) fixedOrder) :: prior) ++ (upper :: (lower :: suffix)))).

DGamma.CP5ConfluenceCanonicalSortSpike:5233:8--5241:65
 5233 |       (rewrite weights (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
 5234 |         Yes same => False
 5235 |         No distinct => True) fixedOrder)) in
 5236 |        rewrite decreased in
 5237 |          sym (plusSuccRightSucc
 5238 |            (foldr (+) Z (map (rankCrossing (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of



```

### C11 attempt 3/3

```idris


||| Lift an authentic segmented rank choice through one ACTUAL prefix action.
||| Owned actions extend the same first segment; unowned actions retain a
||| barrier. No action is dropped, reordered, or classified as root placement.
0 canonicalWorkRankStepProgress :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (fixedOrder : List name) ->
  (action : Action name key value world error) ->
  {source, target : List (List Nat)} -> (SegmentedRankProgress source target) ->
  (SegmentedRankProgress
    (canonicalWorkRankStep name key world error value nameEq fixedOrder action source)
    (canonicalWorkRankStep name key world error value nameEq fixedOrder action target))
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (OInsert child Root component)
  (FirstRankSegment later progress) =
    LaterRankSegment [] (FirstRankSegment later progress)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (OInsert child Root component)
  (LaterRankSegment untouched later) =
    LaterRankSegment [] (LaterRankSegment untouched later)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (OInsert child (ChildOf parent) component)
  (FirstRankSegment {sourceHead} later (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased)) =
    FirstRankSegment later (MkRankedAdjacentProgress {source = (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
        Yes same => False
        No distinct => True) fixedOrder)) :: sourceHead} ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
        Yes same => False
        No distinct => True) fixedOrder)) :: prior) lower upper suffix
      (cong ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
        Yes same => False
        No distinct => True) fixedOrder)) ::) exact)
      (\pivot => cong (rankCrossing pivot (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
        Yes same => False
        No distinct => True) fixedOrder)) +) (weights pivot))
      (rewrite weights (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
        Yes same => False
        No distinct => True) fixedOrder)) in
       rewrite decreased in
         sym (plusSuccRightSucc
           (foldr (+) Z (map (rankCrossing (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
        Yes same => False
        No distinct => True) fixedOrder))) (prior ++ upper :: lower :: suffix)))
           (rankInversions (prior ++ upper :: lower :: suffix)))))
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (OInsert child (ChildOf parent) component)
  (LaterRankSegment untouched later) =
    LaterRankSegment ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
        Yes same => False
        No distinct => True) fixedOrder)) :: untouched) later
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (ORetire actor)
  (FirstRankSegment later progress) =
    LaterRankSegment [] (FirstRankSegment later progress)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (ORetire actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment [] (LaterRankSegment untouched later)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (ORemove actor)
  (FirstRankSegment later progress) =
    LaterRankSegment [] (FirstRankSegment later progress)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (ORemove actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment [] (LaterRankSegment untouched later)
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LBegin actor)
  (FirstRankSegment {sourceHead} later (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased)) =
    FirstRankSegment later (MkRankedAdjacentProgress {source = (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: sourceHead} ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: prior) lower upper suffix
      (cong ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) ::) exact)
      (\pivot => cong (rankCrossing pivot (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) +) (weights pivot))
      (rewrite weights (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) in
       rewrite decreased in
         sym (plusSuccRightSucc
           (foldr (+) Z (map (rankCrossing (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder))) (prior ++ upper :: lower :: suffix)))
           (rankInversions (prior ++ upper :: lower :: suffix)))))
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LBegin actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: untouched) later
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LAdvance actor)
  (FirstRankSegment {sourceHead} later (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased)) =
    FirstRankSegment later (MkRankedAdjacentProgress {source = (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: sourceHead} ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: prior) lower upper suffix
      (cong ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) ::) exact)
      (\pivot => cong (rankCrossing pivot (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) +) (weights pivot))
      (rewrite weights (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) in
       rewrite decreased in
         sym (plusSuccRightSucc
           (foldr (+) Z (map (rankCrossing (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder))) (prior ++ upper :: lower :: suffix)))
           (rankInversions (prior ++ upper :: lower :: suffix)))))
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LAdvance actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: untouched) later
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LDivert actor)
  (FirstRankSegment {sourceHead} later (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased)) =
    FirstRankSegment later (MkRankedAdjacentProgress {source = (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: sourceHead} ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: prior) lower upper suffix
      (cong ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) ::) exact)
      (\pivot => cong (rankCrossing pivot (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) +) (weights pivot))
      (rewrite weights (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) in
       rewrite decreased in
         sym (plusSuccRightSucc
           (foldr (+) Z (map (rankCrossing (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder))) (prior ++ upper :: lower :: suffix)))
           (rankInversions (prior ++ upper :: lower :: suffix)))))
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LDivert actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: untouched) later
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LLeave actor)
  (FirstRankSegment {sourceHead} later (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased)) =
    FirstRankSegment later (MkRankedAdjacentProgress {source = (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: sourceHead} ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: prior) lower upper suffix
      (cong ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) ::) exact)
      (\pivot => cong (rankCrossing pivot (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) +) (weights pivot))
      (rewrite weights (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) in
       rewrite decreased in
         sym (plusSuccRightSucc
           (foldr (+) Z (map (rankCrossing (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder))) (prior ++ upper :: lower :: suffix)))
           (rankInversions (prior ++ upper :: lower :: suffix)))))
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LLeave actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: untouched) later
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LUnload actor)
  (FirstRankSegment {sourceHead} later (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased)) =
    FirstRankSegment later (MkRankedAdjacentProgress {source = (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: sourceHead} ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: prior) lower upper suffix
      (cong ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) ::) exact)
      (\pivot => cong (rankCrossing pivot (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) +) (weights pivot))
      (rewrite weights (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) in
       rewrite decreased in
         sym (plusSuccRightSucc
           (foldr (+) Z (map (rankCrossing (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder))) (prior ++ upper :: lower :: suffix)))
           (rankInversions (prior ++ upper :: lower :: suffix)))))
canonicalWorkRankStepProgress name key world error value nameEq fixedOrder (LUnload actor)
  (LaterRankSegment untouched later) =
    LaterRankSegment ((length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate actor of
        Yes same => False
        No distinct => True) fixedOrder)) :: untouched) later

```

```text
START C11-3 2026-09-07T02:22:37.745629+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
END {"unit": "C11-3", "start": "2026-09-07T02:22:37.745629+00:00", "end": "2026-09-07T02:23:32.738640+00:00", "exit": 1, "maxSampleRSSKiB": 17951024, "cmd": "idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr", "diagnosticErrors": true}
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted

Error: While processing right hand side of canonicalWorkRankStepProgress. Rewriting by foldr (+) 0 (map (rankCrossing ?pivot) sourceHead) = foldr (+) 0 (map (rankCrossing ?pivot) (prior ++ (upper :: (lower :: suffix)))) did not change type rankInversions (length (takeWhile (\candidate => let 0 target = (rankedPrefix (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) ++ (rankedRight (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) :: (rankedLeft (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) :: rankedSuffix (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased)))) :: later in let 0 source = sourceHead :: later in case decEq candidate parent of { Yes same => False ; No distinct => True }) fixedOrder) :: sourceHead) = S (rankInversions ((length (takeWhile (\candidate => let 0 target = (rankedPrefix (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) ++ (rankedRight (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) :: (rankedLeft (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased) :: rankedSuffix (MkRankedAdjacentProgress prior lower upper suffix exact weights decreased)))) :: later in let 0 source = sourceHead :: later in case decEq candidate parent of { Yes same => False ; No distinct => True }) fixedOrder) :: prior) ++ (upper :: (lower :: suffix)))).

DGamma.CP5ConfluenceCanonicalSortSpike:5235:8--5243:65
 5235 |       (rewrite weights (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of
 5236 |         Yes same => False
 5237 |         No distinct => True) fixedOrder)) in
 5238 |        rewrite decreased in
 5239 |          sym (plusSuccRightSucc
 5240 |            (foldr (+) Z (map (rankCrossing (length (Data.List.takeWhile (\candidate => case decEq @{nameEq} candidate parent of



```
