# R199 owner policy change — cross-lane lock abolished

Owner's mid-run steering, verbatim:

> SUPERVISOR RULE CHANGE (owner decision, effective now): the CROSS-LANE heavy lock is ABOLISHED (256 GiB machine; known peaks; worst case one heavy check per lane ≈ 100 GiB). Keep: ONE idris2 check at a time in YOUR lane (evidence rule), your RSS guards (52 GiB unchanged LocalDiamond, 48 GiB otherwise), worktree-scoped orphan handling (never signal lane-2 compilers), per-module records. Drop: acquiring/polling /tmp/dgamma-heavy.lock (release the one you hold when the current check ends and do not acquire again; do not touch a lane-2 lock file if one appears); rebuild-window files are no longer required (worktrees are independent). Record in the ledger that from this point concurrent heavy checks across lanes are permitted, and log any overlap (timestamps only). Continue the final validation.
>
> Incorporate this guidance at the next safe point. Do not restart the task unless the guidance explicitly asks you to.

## Safe-boundary implementation

The old Python final-validation scheduler pinned one runner hash. Only that
scheduler was paused at12:30:17Z; its current V11 native compiler was NOT
signalled. V11 completed PASS12:35:17.403538Z, and its original checker released
its own historical lock12:35:17.405344Z. The paused scheduler was replaced,
NOT its compiler. This operational driver replacement is not a task restart.

At12:36:56.499127Z the same immutable158-target plan continued at V12. V1–V11
remain original authenticated records; no target was rerun and the plan/source
hashes did not change. Both runner/driver versions, the owner receipt, boundary,
old release and continuation are recorded in `O6-R199-EXECUTION-POLICY-CHANGE.json`
and the raw policy-events ledger. Subsequent native checks do not acquire,
inspect, poll, remove or otherwise access any shared-lock path. They retain
one MAIN-lane compiler and52/48GiB own RSS guards. Foreign-lane overlap samples
are timestamps only, not commands/PIDs or a complete OS scheduler trace.

The old current checker retained its existing instrumentation until the allowed
safe boundary. Older raw lock and foreign-process records remain immutable
historical evidence; they are not retroactively rewritten as lock-free runs.
The original plan's `heavyLock: true` annotation is historical and explicitly
superseded by this owner decision; changing that annotation would break the
immutable plan. Runtime records and future-cost policy identify the new rule.
No rebuild-window files are required or introduced; no lane2 lock is inspected.

21 original adversarial evidence tests were rechecked;7 additional policy tests
reject post-change lock use, wrong runner hashes, repeated old units, foreign
command logging and non-timestamp overlap records. The policy transition does
not reopen A/B budgets, permit C, extend clocks, or change any proof source.
