# R194 preflight clarification — original56-slot plan withdrawn unrun

After C1/a7ec1bdd and before ANY final compiler, a read-only import inspection
found main fixtures R174O17ProvisionCollisionCandidate and
R192RemovedBirthCurrentNameProbe import inherited main baseline variant modules.
The lead requested exclusion of those two, in addition to three already omitted
baseline targets. **The supervisor rejected that interpretation.**

## Verbatim supervisor ruling (contact_supervisor need_decision)

> RULING: NOT approved — keep the FULL immutable plan (restore the 56 slots, and re-add the 3 earlier exclusions if they are main-tree files). Clarification of the separation rule: "no lane-owned checks" forbids editing, certifying or merging lane-2 RESULTS; it does not exclude MAIN-tree fixtures whose imports (CP5AvailabilityAwarePlacement, CP5ActorLifecycleOnlyExtended) are baseline modules that exist in your tree. Lane 2 has NOT modified either module in any lane shift (L2R1–L2R3 changed only new files; the L2R1 review confirmed "R178 placement and inherited extended grammar unchanged"), so checking R174O17ProvisionCollisionCandidate and R192RemovedBirthCurrentNameProbe in the main tree validates the main tree's own regression fixtures (A8/A9/A11 evidence) — exactly what the final plan is for. Exclude ONLY targets that do not exist in your tree (lane-created files) — record each such exclusion by path with the reason "file absent from main tree". Preserve the original plan + hash and write the preflight memo as you proposed; then run the plan. No Idris edits, no budget extension.

## Applied scope

All52 inherited R193 targets exist in main and are byte-pinned to b81362d8.
Together with7 changed main proof targets, the restored plan contains
**59 checks:52 positives and7 expected negatives**, with no exclusions.
The restored three are:
- research/DGamma/CP5ActorLifecycleOnlyExtended.idr
- research-tests/DGamma/R192ExtendedChildBlockProbe.idr
- research/DGamma/CP5AvailabilityAwarePlacement.idr

They are inherited MAIN baseline validations, not checks/merges/certificates of
ongoing lane2-created results. The check guard now explicitly pins the two
baseline variant modules to b81362d8 and permits them only in planned validation.
No sibling-worktree operation, source edit, source retry or budget extension.

The original56-slot plan is retained as O6-R194-PREFLIGHT-PLAN.json, with its
original scope as O6-R194-PREFLIGHT-SCOPE.json. Original plan SHA256:
`73ddfc58ea6e13473f31a61366fcbad931a18cc69b62b1de6ceb58985fa31bfe`.
It is **withdrawn before execution**, not silently substituted after a failure.
No V invocation exists at replacement time; the restoration guard enforces it.
The restored plan is immutable before the first V invocation. Earlier C1
exclusion claims and the corresponding earlier test log are historical and
superseded by this ruling, not retroactively presented as the correct rule.
