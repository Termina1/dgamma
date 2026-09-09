# L2R4 Unit B — original-edge role coverage and structural park

Boundary **a6579477**, B14 slot reached, 13 retained declarations (B7 fully reverted/exhausted). No B15–B18 attempt yet. Native original-edge-only additions: B6 foreign ORetire (**0ff957b3**), B13 ALL-parent OInsert (**0f2afa91**, stronger than other-parent child insertion, with no own-parent metadata premise). B14 (**a6579477**) assembles a **total orchestration-domain** dispatcher by all eight Action constructors, with the explicit domain premise `isLifecycleAction action = True -> Void`. This is NOT the requested all-role `single` callback and cannot instantiate it by hiding that premise.

| Role | Status | Evidence / exact limit |
|---|---|---|
| Root OInsert | Original-edge-only proved | B13 includes Root; unlike L2R3 root-only branch, no child-parent metadata input. |
| Other-parent child OInsert | Original-edge-only proved | B13 permits every Parent, including ChildOf the retired actor, since native parentPresent survives retirement. Full native parent/provision guards retained. |
| Foreign ORemove | Inherited proved | L2R3RemoveDispatch.replayRemoveAfterRetirement reused by B14. |
| Foreign ORetire | Original-edge-only proved | B6 uses actual RetireSuccessView, checked native replay, exact ordered replacement commutation, snapshot coherence. |
| LBegin | PARKED | B7 3/3 hidden dependent Bool observed-value wall; supervisor ratified, no restatement. |
| LIter / LFinish | STRUCTURAL DEPENDENCY PARK proposed | L2R2 Advance square is for ORemove, not ORetire; native LAdvance checks targetMatches/targetFiber after resolving iterator capability. The missing retirement provider/target frame crosses the stopped B7 seam. |
| Other LAdvance tags, LDivert/LUnload/LLeave | OPEN | Full generic Action domain admits these; not silently dropped. |
| All-role dispatcher | OPEN | Exact obligation is unchanged L2R2ForeignReplay `single`, lines52–65 (and repeated in replayRetirementBeforeForeignRun). No oracle record masquerades as its inhabitant. |
| Whole R191 ForeignReplay instance | OPEN | That fold requires the all-role callback, not merely two selected lifecycle fixture edges. B14's explicit nonLifecycle premise cannot be supplied for R191 actor1 lifecycle edges. |

## Why the L2R2 Advance square is not an admissible role adapter

`L2R2RemoveSquare.commuteAdvanceChildRemove` takes an actual child lookup of `MkFiber component (ChildOf parent) True table (Inactive outcome)`, source `hasChild child = False`, both original checked LAdvance and **ORemove child** equations, then constructs a deletion-state alternate route. The retirement fold instead requires replay at the **replaceBinding child (retireFiber fiber)** runtime snapshot for arbitrary child fiber. It has no inactive, empty-table, childlessness or deletion premise. Delete and Retire have different ordered binding lists, even if the retired fiber is an inactive leaf. Thus this is a literal codomain/input mismatch, not a compiler-budget excuse or a weakened theorem.

The native `applyAction (LAdvance actor)` code checks `targetMatches (targetFiber actorFiber registry) view` both for empty finish and after an effectful iterator result. `resolveCommittedValuesRetireRegistry` proves capability preservation, but alone does not discharge that target-matching branch. A new retirement target-provider scan proof would re-enter the supervisor-stopped B7 seam; no new equivalent B7 statement or hidden flag observer is attempted.

Remaining exact work: native original-edge-only lifecycle replay with explicit observed Bool/state equations and exact runtime successor; then a total all-role Action dispatcher with NO extra nonLifecycle premise; then instantiate the unchanged ForeignReplay fold on the R191 trace. B14 is useful verified orchestration capital, not a whole-run oracle.

Supervisor RATIFIED the structural park immediately: lifecycle roles need a retirement-provider frame (declared keys versus resolver/target guard) in an explicit observed-Bool + equation shape; that is an **L2R5 candidate**, not a B7 restatement here. Full single and R191 instance remain parked. B15–B18 remain unused; proceed to Unit C. No additional B source attempt is authorized in this shift.
