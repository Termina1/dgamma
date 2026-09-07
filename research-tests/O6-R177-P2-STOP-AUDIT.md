# R177 P2 — mandatory 3/3 stop and rollback

UTC stop verdict: **2026-09-07 04:02:04**, reconciled **04:06 UTC**.
Probe window authorized at 03:49, at most six micro-units / until 04:34 UTC.
Only two micro-units attempted; P1 PASS, P2 FAIL 3/3. No fourth attempt.

## What remains proved / reviewed

* P1 (03:53:21–03:54:10, exit 0) proves the actual R45 generated-child
  retirement is not a RootOrchestrationStep. Its checked snapshot is retained.
* The supervisor's independent read-only review confirms that the frozen
  SameOrchestrationModuloGenerated only couples external root orchestration and
  generated insertion births; generated retirement is skipped. This may be a
  fidelity gap against paper pp.2328–2331, NOT an O18 body theorem.
* Neither quiet endpoint reachability nor both IndependentCanonicalSchedule
  capitals has yet been constructed. No complete counterexample is claimed.

## Exact failed unit / attempts

P2 attempted a producer for two traces extending the R45 common prefix: root
insert, root begin, generated child insert; then parent finish in both traces,
child begin/finish only on the left, child retirement only on the right.

1. **P2-1**, 03:55:30–03:55:31, exit 1. Concrete endpoint/transition producer.
   Refl cannot reduce the new target's registryWellFormed conditional across the
   imported fixture boundary. This version retired before parent finish.
2. **P2-2**, 03:59:12–03:59:14, exit 1. Moved retirement after the common parent
   finish to make the proposed parent block contiguous, and used checkedFromRaw
   plus raw preservation. The old imported R45 child-insertion raw equation is
   opaque to Refl. No raw equation was assumed/postulated.
3. **P2-3**, 04:02:02–04:02:04, exit 1. Weakened honestly to an executable Maybe
   producer using checkedNamedFire, so no guessed concrete target is needed.
   Rejected before proof elaboration: record projection was over-qualified as
   `DGamma.CP3StatementChecks.namedAfter`; the actual qualified name includes
   `CheckedNamedTransition`. This superficially simple error STILL triggers the
   mandatory three-attempt stop. No namespace fix has been attempted.

All exact attempted sources, logs, and JSON verdicts are under
`research-tests/r177-probes/P{1,2}-*-RetirementTransport.*`.
The disposable `.idr` has been removed; its successful P1 snapshot remains.
Build seeds were preserved. No live Idris backend remains at this boundary.
No production/premise/body change; six holes remain inherited.

## Gate

STOPPED. Await an explicit supervisor decision before any new proof/compiler
attempt. A fresh explicitly gated executable producer can correct the projection
namespace and runtime-check actual quiet/support outcomes, or the probe can stay
frozen while independently authorized metadata work resumes. Do not promote the
read-only premise review or P1 alone to (a)+(b)+(c) inhabitation.

## Explicit supervisor exception P2-4 (04:09 UTC)

The stop was RATIFIED. The supervisor then authorized exactly one D1-4-style
mechanical repair invocation, subsequently clarifying that BOTH `namedAfter`
and `namedTransition` could receive the missing `CheckedNamedTransition` record
namespace, with **every other source byte unchanged**. This exact constraint is
machine-checked in `P2-4-RetirementTransport-freshness.json`.

The ONE invocation used Idris `--exec` to typecheck the repaired producer and
execute the quiet/support query in the same compiler process. **Exit 0**,
04:09:54–04:09:57, sampled peak 4,479,152 KiB. Exact output:

```
R177_P2_PAIR=Just; leftQuiet=True; rightQuiet=True; leftChildSupported=True; rightChildSupported=False; leftParentActive=True; rightParentActive=True; leftLength=6; rightLength=5
```

Thus a checked executable pair is actually produced; both endpoints are quiet,
both parents remain Active, and child support differs. Quiescence does NOT force
re-registration or restore support truth for this pair. The six-/five-step traces
share root insert, root begin, child insert, parent finish. Left then begins and
finishes the child; right instead retires it.

**Evidence qualification:** --exec suppresses the usual Building marker, so the
unchanged standard check wrapper conservatively records `fresh:false` and
`passed:false` despite compiler **exit 0**. Do not relabel that JSON as a standard
fresh --check PASS. The separate freshness JSON records target TTC mtime strictly
after this exact repaired source mtime; the runtime expression references the new
P2 symbol absent from the only prior successful P1 compilation. The source was
removed again and all seeds preserved. No second repair/compiler invocation.

**Still not established:** BOTH IndependentCanonicalSchedule capitals, a typed
SameOrchestrationModuloGenerated witness for this full quiet pair, and therefore
a complete counterexample to the six-premise O18 statement. The independent
review establishes invisibility of this generated-retirement difference at the
frozen premise-definition level, not these missing capital inhabitants.
A9 remains an OPEN owner finding. Candidate cure: a research-side explicit
GeneratedOrchestrationMatched hypothesis modulo the accepted generation
bijection, threaded like uniqueness; **no premise change this shift**.
Probe now frozen. Resume only independent dependency/provision/parent metadata.
