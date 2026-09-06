# O6 R171 — O11 cumulative accounting grind

## Baseline and protocol

Started **2026-09-06 07:00:15 UTC**, required HEAD **919a548**, branch
`cp5-thm73-scoping`, verified. Initial tree contained only permitted untracked
`paper/` and `review-o6-body-adversarial.md`. Idris **0.8.0**, CLI spelling
`--source-dir <dir>` and `--check` verified before first check. Read all 746
lines of R170 first, then full R169 and R146; read the entire 3882-line extracted
paper in contiguous bounded chunks. No subagent launched.

No-new-attempt boundary **10:20:15 UTC**; safe-gate deadline **10:45:15 UTC**;
timeout **11:00:15 UTC**. Sequential, target-fresh, seeded checks only. Process
inspection precedes each invocation. No build/ or TTC deletion, production
touch, from-scratch rebuild, concurrent Idris process, or orphan detected.
Temporary snippets/scripts/transcripts reside in `/tmp/dgamma-r171*`.

Common command:

```sh
idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr
```

Fixture checks additionally pass `--source-dir research-tests`. A16 added
`--timing 2`, and A17 added `--timing 5` after help verified the flag. These
were budgeted proof invocations, not hidden extra compiler probes.

## Six-part chain, interim

1. **Identity endpoint/accounting COMPLETE:** `00ffc76`, `631dea7`. Empty actual
   omissions and historical withdrawals, all four registration clauses.
2. **Authentic pullback generation/name seal COMPLETE:** `5eab693` emits the
   original source birth classification, backward-generation equation and raw
   name equation together. `ec91b96` projects its equation for the authentic
   existing history map. No raw-name birth inference or occurrence proof
   irrelevance is used.
3. **Complete recurrence/history coherence COMPLETE:** `24bb89c` computes the
   full derivation history as selected source births followed by every tail
   birth pulled back via the actual operational inverse. `7ae5e4b` proves the
   exact map/append equation, including current selected census. `de06142`
   seals it at the O10 constructors. No empty-history shortcut.
4. **Cumulative endpoint omission composition:** pending.
5. **Four-clause registration composition:** pending; `a7c781a` establishes the
   sealed step accounting's exact backward-generation equation.
6. **Sealed derivation accounting fold:** pending.

O11 remains untouched **0/3**. No closure or Theorem-73 claim.

## Coherence: witness first, then authorized research fields

The simultaneous live classification/generation/name witness was constructed
first (`08ee8c4`, `5eab693`). Its complete step map/append recurrence was proved
before the Core surface revision. This supplies the authentic producer, but
cannot equate an arbitrary Core constructor's independent typed list with its
recursive derivation. Similarly, arbitrary Step accounting can select a
separate occurrence origin, whereas the authentic O9 producer already chooses
the frozen operational origin. Both missing equations therefore need the
explicit research-only seals authorized by the R170 owner ruling.

### Core clause mapping — `de06142`

| Original clause | Revised clause / producer |
|---|---|
| `coreReducedFinal`, `coreReducedTrace`, `coreReducedPremises` | Unchanged; exact recursive target and full TARGET bundle retained |
| `coreClosingFree`, `coreSameExternalInputs`, `coreReplayCorrespondence` | Unchanged; same recursive producers |
| `coreDeletionDerivation` | Unchanged actual `ClosingFreeDeletionDone/Step` |
| `coreDeletionGenerationHistory` | Unchanged complete typed list and authentic pullback computation |
| No history/derivation alignment field | Add erased `coreDeletionHistoryExact`, comparing projected generations to `closingFreeDeletionGenerations coreDeletionDerivation` |
| `scopedClosingFreeCoreDone` | Same arguments/fields plus constructor-owned `Refl` |
| `scopedClosingFreeCoreStep` | Same arguments/fields plus `scopedStepHistoryExact` composed with recursive tail's seal |

A1–A11 capital was moved before the Core-step producer to make its dependencies
available. No original proof body was changed by that move. Core constructor
search found only the two actual producers. O10 signature and body unchanged.
`R171CoreHistoryCloneNegative` rejects a record update that substitutes an
arbitrary typed history, at the expected map/history mismatch (`9db0d0a`).

### Step clause mapping — `43efb5f`

| Original clause | Revised clause / producer |
|---|---|
| `deletionResult`, `deletionProducerCapital` | Unchanged actual result/capital |
| Replay and operational occurrence fields, including `deletionOccurrenceCorrespondenceExact` | Unchanged, same frozen origin |
| SameExternal and endpoint, including exact selected withdrawal list | Unchanged |
| `deletionGenerationClassified`, `deletionRegistrationAccounting` | Unchanged classifications and full four-clause accounting |
| No accounting/operational-origin alignment | Add erased `deletionRegistrationOriginExact`: pointwise equality of complete located generated occurrences |
| `nextPremises`, `deletionStrictlyShorter` | Unchanged full TARGET bundle and actual strict decrease |
| `scopedDeletionStepFromAccounting` | Add explicit origin-equation argument, emitted after exact withdrawal-list transport using `scopedAccountingTransportOrigin` |
| Live producer | Emits its authentic equation, not a new O9 caller premise |

`R11DirectDeletionStepCloneNegative` adds the new field to both constructor
spellings (`3e8849e`), and still rejects at **occurrences vs alternate** in the
original operational seal. `R171StepAccountingCloneNegative` separately rejects
replacing accounting at **deletionRegistrationAccounting vs alternate**
(`2fbd510`). No production record was changed; O9 signature/body unchanged.

### Elaboration cost and producer boundary — `465ce36`

A14's first invocation hit the tool's 180-second timeout; no diagnostic was
flushed. Process inspection immediately afterwards found neither wrapper nor
compiler. It counts as **A14-1**, not a hidden attempt. A14-2 passed at 8m29s,
about 13.3 GiB sampled RSS. A15's abstract origin equation alone did not remove
the slowdown. A16 timing attributed nearly all cost to declaration processing.
A17 timing isolated **363.219 seconds** in the private intermediate
`scopedEnrichedStepFromAccounting`: its argument type exposed the equality
at the fully computed live result. This was not a missing semantic premise.

A17 replaces that *now-unused private intermediate* with
`scopedStepFromResultCapital`, which constructs endpoint, complete registration
accounting and its seal while the exact result/capital are explicit parameters.
The live `scopedEnrichedStepFromExternal` supplies those same actual result,
capital, replay, full TARGET bundle and SameExternal. The more general
`scopedDeletionStepFromAccounting` remains available; no proof obligation is
removed. Repository consumer search found only the migrated live assembler.
The redundant eager intermediate is removed rather than preserved as legacy.
Fresh check returned to **75.5 seconds**, sampled RSS **4,190,592 KiB**. This
is a producer-boundary refactor, not a semantic route change or surface weakening.

## Budgeted failures, interim

- **A8-1:** unqualified bare `classifiedGeneration` under `map` in a top-level
  proposition was implicitly rebound. Full qualification fixed A8-2.
- **A14-1:** 180-second tool timeout described above; A14-2 passed unchanged
  source (R11 fixture arity was updated between checks).
- **N2-1:** the new negative fixture initially lacked a direct LocalDiamond
  import, giving an undefined projection diagnostic, not the intended negative
  result. N2-2 adds that import and rejects at the required accounting mismatch.
- **A17-1:** omitted `protocol` argument at the migrated SameExternal producer;
  diagnostic `DecEq name` versus `RegistrationProtocol ...`. Corrected A17-2,
  which also removes the measured redundant eager intermediate.

No unit exhausted three failed attempts. Full diagnostics and final ledger
will be appended before the safe gate. No new escape hatch, retained proof
hole, `with` block, local let alias, frozen deletion theorem call, production
change, O14/O17/O19 proof body, or O21 withdrawal branch has been introduced.
LocalDiamond is untouched.

## Status

**Fully proved:** identity cumulative accounting; authentic classified pullback
and generation/name seal; exact complete history recurrence; constructor-owned
Core history and Step operational-origin coherence, both negative-tested.

**Partial:** O11 cumulative endpoint/registration fold (parts 4–6).

**Merely stated:** O11, still 0/3, and seven other research holes. Next: full
endpoint omission composition and bidirectional registration composition at the
sealed exact origin, then the derivation fold and mandatory closure gate.
