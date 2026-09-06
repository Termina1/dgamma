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

## O11 CLOSED — mandatory milestone checkpoint

**`assembleClosingFreeAccountingSpike` CLOSED 1/3 at `8356a64`.** Fresh body
check **09:17:13–09:18:34 UTC**, unchanged original signature. It applies
`scopedClosingReductionFromAccounting` to the full structural
`scopedDerivationAccounting` fold of the actual Core derivation. It retains
all exact Core fields, including the full original typed history and full
TARGET `coreReducedPremises`; history alignment is `coreDeletionHistoryExact`
followed by the inverse of the fold's checked recurrence. No caller premise,
empty-history shortcut, discarded tail entry, or raw exclusion cast.

### Completed six-part chain

| Part | Final producer capital | Status |
|---|---|---|
| 1. Identity endpoint and all four registration clauses | `scopedCumulativeEndpointIdentity` / `scopedCumulativeRegistrationIdentity`, `00ffc76` / `631dea7` | COMPLETE |
| 2. Authentic source classification and exact generation/name equations | `scopedClassifiedPullback`, `5eab693`; projected by `scopedPullClassificationGeneration`, `ec91b96` | COMPLETE |
| 3. Complete selected-plus-pulled-tail recurrence and Core seal | `closingFreeDeletionGenerations`, `24bb89c`; `scopedStepHistoryExact`, `7ae5e4b`; `coreDeletionHistoryExact`, `de06142` | COMPLETE |
| 4. Full endpoint omission composition | `scopedCumulativeEndpoint`, `0ca6cbb`; authentic name-preservation input discharged in `cae15e9` | COMPLETE |
| 5. Full bidirectional registration composition at exact map | `scopedComposeRegistrationAccounting`, `0224856`; exact composed operational-origin equation `679c7d3` | COMPLETE |
| 6. Sealed structural derivation fold and final constructor | `scopedDerivationAccounting`, `58d139e`; `scopedClosingReductionFromAccounting`, `3e132c1`; O11 `8356a64` | COMPLETE |

Endpoint composition uses the union of actual raw omission lists, not the list
of historical withdrawn raw names. A name absent at an intermediate endpoint
cannot be inserted by the endpoint relation; every composed omission therefore
really is absent at the final endpoint. The source-present withdrawal branch
transports **retirement, inactivity, and literal ordered empty bindings** through
control and effect agreement; the source-absent branch remains distinct.
Later live roots sharing a historical child's raw name are not newly omitted.
The justification for a pulled historical raw name is derived from the actual
withdrawn occurrence, not from global name preservation of an arbitrary
bijection at unrealized generations.

The registration composer constructs all four original CP3 clauses. Its chosen
map is exactly the composition of the two accounting maps. Coverage uses the
sealed backward-generation equation even when existential occurrence witnesses
differ; the right-withdrawal exclusion uses the inverse law to establish
**global** generation injectivity across different parent/component shapes.
It does not run the narrower fixed-shape occurrence injectivity law backwards.
`scopedComposedAccountingOrigin` proves full located-occurrence equality of that
composition with the actual composed operational origin. This equation survives
withdrawal metadata transport and is retained in the constructor-owned
`ScopedDerivationAccounting.foldedOriginExact` at every recursive node.

The simultaneous witness cure thus succeeds for the live producer. The two
explicit research seals remain necessary for the *generic* Core/Step consumer:
Core's generation-list equality and Step's pointwise complete-origin equality.
Both seals are emitted by the actual O9/O10 producer chain, projected by O11,
and separately negative-tested. No production or LocalDiamond field changes.

## Unit C disposition

**NOT STARTED.** At closure, fewer than 90 minutes remain before the
**10:20:15 UTC** no-new-attempt boundary (about 62 minutes before gate
validation, about 59 afterwards). Unit C is therefore barred by its explicit
time precondition even after a milestone reply. No next-phase reconnaissance
memo or THM73-PLAN.md update is claimed. O14/O17/O19 bodies and O21 withdrawal
branches remain unopened. The mandatory supervisor/reviewer milestone gate
comes before any further work.

## Final incremental ledger

Every implementation success has a fresh DeletionChain `Building` marker and
exit 0, followed by an immediate commit. **57 checked source commits**, **54
new top-level declarations**, **60 source implementation invocations**: 57
successes, two corrected compiler errors, one counted tool timeout. A17 removes
one obsolete private intermediate, so net new source declarations are 53.
No invocation introduced more than one new declaration. A12/A14/O11 add none.
The two new negative fixtures each contain one declaration; the existing R11
negative fixture changes constructor arity only.

| Unit | Declaration/surface | Attempts | Commit | Fresh check ended UTC |
|---|---|---:|---|---|
| A1 | `scopedCumulativeEndpointIdentity` | 1/3 | `00ffc76` | 07:04:00 |
| A2 | `scopedCumulativeRegistrationIdentity` | 1/3 | `631dea7` | 07:05:38 |
| A3 | `scopedGeneratedOriginBackward` | 1/3 | `5fd6cc8` | 07:07:42 |
| A4 | `ScopedClassifiedPullback` | 1/3 | `08ee8c4` | 07:09:30 |
| A5 | `scopedClassifiedPullback` | 1/3 | `5eab693` | 07:11:21 |
| A6 | `scopedPullClassificationGeneration` | 1/3 | `ec91b96` | 07:13:51 |
| A7 | `scopedHistoryMapExact` | 1/3 | `c1051c9` | 07:15:36 |
| A8 | `scopedClassifiedGenerationsExact` | 2/3 | `378e0d3` | 07:18:50 |
| A9 | `closingFreeDeletionGenerations` | 1/3 | `24bb89c` | 07:20:31 |
| A10 | `scopedHistoryAppendExact` | 1/3 | `e3bc03a` | 07:22:15 |
| A11 | `scopedStepHistoryExact` | 1/3 | `7ae5e4b` | 07:24:08 |
| A12 | `surface` | 1/3 | `de06142` | 07:25:57 |
| A13 | `scopedAccountingTransportOrigin` | 1/3 | `1037390` | 07:27:38 |
| A14 | `surface` | 2/3 | `43efb5f` | 07:40:20 |
| A15 | `scopedDeletionAccountingOriginExact` | 1/3 | `5740b2a` | 07:49:52 |
| A16 | `scopedStepAccountingBackward` | 1/3 | `a7c781a` | 08:00:52 |
| A17 | `scopedStepFromResultCapital` | 2/3 | `465ce36` | 08:11:48 |
| A18 | `scopedWithdrawnAbsent` | 1/3 | `6c87d58` | 08:17:09 |
| A19 | `scopedControlAbsentRight` | 1/3 | `dbb67f0` | 08:18:29 |
| A20 | `scopedEndpointAbsentAt` | 1/3 | `9b249a3` | 08:19:50 |
| A21 | `scopedEndpointAbsent` | 1/3 | `cfdf4d1` | 08:21:06 |
| A22 | `scopedWithdrawalExtend` | 1/3 | `965219c` | 08:22:22 |
| A23 | `scopedAppendMemberLeft` | 1/3 | `7a82fc0` | 08:23:37 |
| A24 | `scopedAppendMemberRight` | 1/3 | `686edca` | 08:24:53 |
| A25 | `scopedAppendMembership` | 1/3 | `53121aa` | 08:27:34 |
| A26 | `scopedControlFoundLeft` | 1/3 | `4cd29b8` | 08:28:49 |
| A27 | `scopedLifecycleInstalledSame` | 1/3 | `0276d2f` | 08:30:05 |
| A28 | `scopedFiberWithdrawalFlags` | 1/3 | `15e75c4` | 08:31:21 |
| A29 | `scopedWithdrawalFromControlCell` | 1/3 | `e665041` | 08:32:42 |
| A30 | `scopedWithdrawalThroughControls` | 1/3 | `47fae0c` | 08:33:57 |
| A31 | `scopedWithdrawalRightAt` | 1/3 | `bb89457` | 08:36:22 |
| A32 | `scopedCumulativeNamesWithdrawn` | 1/3 | `a1089c7` | 08:37:38 |
| A33 | `scopedCumulativeBirthLeft` | 1/3 | `c5a621c` | 08:38:59 |
| A34 | `scopedCumulativeBirthRight` | 1/3 | `0a22ec2` | 08:40:19 |
| A35 | `scopedCumulativeEndpoint` | 1/3 | `0ca6cbb` | 08:41:40 |
| A36 | `ScopedCanonicalAccounting` | 1/3 | `a44bd99` | 08:45:07 |
| A37 | `scopedBackwardInjective` | 1/3 | `98a49fa` | 08:46:23 |
| A38 | `scopedMappedMembership` | 1/3 | `69e7f02` | 08:47:39 |
| A39 | `ScopedRegistrationRemoval` | 1/3 | `53657aa` | 08:48:55 |
| A40 | `scopedCoverageTarget` | 1/3 | `fb54e9e` | 08:51:02 |
| A41 | `scopedCoverageMiddleDecision` | 1/3 | `639f8f1` | 08:52:18 |
| A42 | `scopedCoverageMiddle` | 1/3 | `3e7e1ff` | 08:53:33 |
| A43 | `scopedCoverageSourceDecision` | 1/3 | `042325e` | 08:54:54 |
| A44 | `scopedRemovalLeft` | 1/3 | `c51915d` | 08:56:54 |
| A45 | `scopedRemovalRight` | 1/3 | `277d4a9` | 08:58:10 |
| A46 | `scopedCumulativeRegistrationRemoved` | 1/3 | `1275b2f` | 08:59:26 |
| A47 | `scopedComposeRegistrationAccounting` | 1/3 | `0224856` | 09:00:42 |
| A48 | `scopedAccountingPullName` | 1/3 | `c271e0a` | 09:03:30 |
| A49 | `scopedStepSealedAccounting` | 1/3 | `59fd56c` | 09:04:51 |
| A50 | `scopedComposedAccountingOrigin` | 1/3 | `679c7d3` | 09:06:12 |
| A51 | `ScopedDerivationAccounting` | 1/3 | `e023dad` | 09:07:33 |
| A52 | `scopedDerivationAccountingDone` | 1/3 | `cbcbc91` | 09:10:15 |
| A53 | `scopedDerivationAccountingStepAt` | 1/3 | `909b806` | 09:11:36 |
| A54 | `scopedDerivationAccountingStep` | 1/3 | `cae15e9` | 09:12:57 |
| A55 | `scopedDerivationAccounting` | 1/3 | `58d139e` | 09:14:18 |
| A56 | `scopedClosingReductionFromAccounting` | 1/3 | `3e132c1` | 09:16:04 |
| B-O11 | `surface` | 1/3 | `8356a64` | 09:18:34 |

### Fixture micro-units

| Unit | Attempts | Commit | Result |
|---|---:|---|---|
| A14-fixture | 1 | `3e8849e` | Updated direct clone still rejects at occurrences vs alternate |
| N1 | 1/3 | `9db0d0a` | New Core history clone rejects at intended map/history equality |
| N2 | 2/3 | `2fbd510` | Missing import fixed; new Step accounting clone rejects at intended origin equality |

### Exact budgeted failure diagnostics

The failed spells were corrected/removed in their own original micro-unit
budgets. Timing telemetry is excluded from the diagnostic quote for A17;
full telemetry remains in `/tmp/dgamma-r171/A17-1.log`. A14-1 had no flushed
compiler output; the tool returned `Command timed out after 180 seconds` and
the following process scan found no compiler or wrapper. This invocation was
not counted as a successful check or concealed as preparation.

#### A8-1

```text
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  surviving is shadowing DGamma.CP4DeletionGenerationFilter.GenerationFilterResult.surviving

DGamma.CP5ConfluenceDeletionChainSpike:3011:1--3013:19
 3011 | generationSubsequenceSourceOrdinal :
 3012 |   GenerationActionSubsequence nameEq deletable ordinal live original surviving ->
 3013 |   Nat -> Maybe Nat

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  classifiedGeneration is shadowing DGamma.CP5ConfluenceDeletionChainSpike.classifiedGeneration

DGamma.CP5ConfluenceDeletionChainSpike:29791:3--29796:156
 29791 | 0 scopedClassifiedGenerationsExact :
 29792 |   (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
 29793 |   (initial, finalState : SystemState name key value world error) -> (global : Transitions initial finalState) ->
 29794 |   (generations : List (RegistrationGeneration name)) ->
 29795 |   (classified : ((generation : RegistrationGeneration name) -> Elem generation generations -> DeletedGenerationClassification name key world error value nameEq global generation)) ->
 29796 |   (map classifiedGeneration (scopedClassifiedGenerations name key world error value nameEq initial finalState global generations classified) = generations)

Error: While processing type of scopedClassifiedGenerationsExact. Can't solve constraint between: ?type_of_classifiedGeneration [no locals in scope] and (generation : RegistrationGeneration name ** DeletedGenerationClassification name key world error value nameEq global generation) -> RegistrationGeneration name.

DGamma.CP5ConfluenceDeletionChainSpike:29796:8--29796:28
 29792 |   (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
 29793 |   (initial, finalState : SystemState name key value world error) -> (global : Transitions initial finalState) ->
 29794 |   (generations : List (RegistrationGeneration name)) ->
 29795 |   (classified : ((generation : RegistrationGeneration name) -> Elem generation generations -> DeletedGenerationClassification name key world error value nameEq global generation)) ->
 29796 |   (map classifiedGeneration (scopedClassifiedGenerations name key world error value nameEq initial finalState global generations classified) = generations)
                ^^^^^^^^^^^^^^^^^^^^

Error: No type declaration for DGamma.CP5ConfluenceDeletionChainSpike.scopedClassifiedGenerationsExact.

DGamma.CP5ConfluenceDeletionChainSpike:29797:1--29797:114
 29793 |   (initial, finalState : SystemState name key value world error) -> (global : Transitions initial finalState) ->
 29794 |   (generations : List (RegistrationGeneration name)) ->
 29795 |   (classified : ((generation : RegistrationGeneration name) -> Elem generation generations -> DeletedGenerationClassification name key world error value nameEq global generation)) ->
 29796 |   (map classifiedGeneration (scopedClassifiedGenerations name key world error value nameEq initial finalState global generations classified) = generations)
 29797 | scopedClassifiedGenerationsExact name key world error value nameEq initial finalState global [] classified = Refl
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Did you mean: scopedClassifiedGenerations?
```

#### N2-1

```text
Error: While processing right hand side of replaceStepAccounting. When unifying:
    (birth : LocatedGeneratedRegistration child parent component (appendTransitions (deletionResult3183 .survivingBefore) (appendTransitions (deletionResult3183 .survivingEpisode) (deletionResult3183 .survivingAfter)))) -> deletionRegistrationAccounting3192 .canonicalToOriginal birth = replayGeneratedRegistrationOrigin name3170 key3171 world3172 error3173 value3174 initial3178 finalState3179 initial3178 (deletionResult3183 .survivingFinal) trace3180 (appendTransitions (deletionResult3183 .survivingBefore) (appendTransitions (deletionResult3183 .survivingEpisode) (deletionResult3183 .survivingAfter))) deletionOccurrenceCorrespondence3186 child parent component birth
and:
    (birth : LocatedGeneratedRegistration child parent component (survivingTrace ?postpone)) -> canonicalToOriginal ?postpone birth = replayGeneratedRegistrationOrigin name3170 key3171 world3172 error3173 value3174 initial3178 finalState3179 initial3178 (survivingFinal ?postpone) trace3180 (survivingTrace ?postpone) ?postpone child parent component birth
Undefined name DGamma.CP5ConfluenceLocalDiamondSpike.ActionRegistrationReplayCorrespondence.replayGeneratedRegistrationOrigin. 

DGamma.R171StepAccountingCloneNegative:17:40--17:92
 13 |   (step : DeletionChainStep name key world error value protocol nameEq keyEq trace premises candidate) ->
 14 |   (alternate : CanonicalRegistrationCorrespondence trace (survivingTrace (deletionResult step))
 15 |     (endpointWithdrawnGenerations (deletionEndpoint step))) ->
 16 |   DeletionChainStep name key world error value protocol nameEq keyEq trace premises candidate
 17 | replaceStepAccounting step alternate = { deletionRegistrationAccounting := alternate } step
                                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Did you mean: isGeneratedRegistrationAction?
```

#### A17-1

```text
Error: While processing right hand side of scopedEnrichedStepFromExternal. When unifying:
    DecEq name
and:
    RegistrationProtocol key value world error
Mismatch between: DecEq name and RegistrationProtocol key value world error.

DGamma.CP5ConfluenceDeletionChainSpike:28993:69--28993:75
 28989 |     (scopedEnrichedOperationalCapital name key world error value protocol nameEq keyEq initial finalState global candidate folds (replayAligned (chainReplayCapital premises)))
 28990 |     (scopedEnrichedReplayFromHeads name key world error value protocol nameEq keyEq initial finalState global candidate folds
 28991 |       (scopedEnrichedHeadReplays name key world error value protocol nameEq keyEq initial finalState global candidate folds))
 28992 |     (scopedEnrichedTargetFromHeads name key world error value protocol nameEq keyEq initial finalState global candidate folds premises)
 28993 |     (scopedEnrichedExternalOrchestration name key world error value nameEq keyEq initial finalState global candidate folds (replayAligned (chainReplayCapital premises)))
                                                                             ^^^^^^
```

## Fresh post-closure gate evidence

All eight checks ran sequentially at proof HEAD **8356a64**, after the final
proof edit, **09:18:41–09:20:53 UTC**. No proof attempt follows this batch.

| Check | Expected exit | Result |
|---|---:|---|
| Fresh direct DeletionChain | 0 | PASS |
| `R11DeletionCertificateProjectionPositive` | 0 | PASS |
| `R11DirectDeletionStepCloneNegative` | 1 | Correct rejection, occurrences vs alternate |
| `R11DeletionFillerMapCertificateNegative` | 1 | Correct rejection, `generationSubsequenceSourceOrdinal` |
| `R10DeletionStepMapCloneNegative` | 1 | Correct rejection, alternate vs step occurrence correspondence |
| `R171CoreHistoryCloneNegative` | 1 | Correct rejection, old vs alternate projected history |
| `R171StepAccountingCloneNegative` | 1 | Correct rejection, old vs alternate accounting |
| Seeded `idris2 --build dgamma.ipkg` | 0 | PASS; 207/207 retained TTCs, no missing module |

All non-package checks show their own fresh `Building` marker. Negative error
fragments were explicitly asserted; exit 1 by itself was not treated as success.
The initial N2 import error is excluded from intended negative evidence.
The four inherited fixture commands are reproduced in the R169/R170 audits;
new fixture commands are:

```sh
idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R171CoreHistoryCloneNegative.idr
idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R171StepAccountingCloneNegative.idr
```

No runtime or wider R11 suite check is claimed. Total compiler check/build
invocations: **72** = 60 source + 4 fixture micro-unit + 8 gate invocations.
Of these, 60 exit 0; eight are intended negative-fixture rejections; three
are corrected diagnostic failures (two source, one fixture); one is the tool
timeout. Maximum sampled RSS in completed wrapper telemetry: **14926464 KiB**;
this is not an OS exact peak and the timed-out invocation has no final RSS
sample ledger. No orphan, OOM, LocalDiamond rebuild or seed deletion occurred.

### Frozen surfaces and asserting self-validation

```json
{
  "head": "8356a64",
  "fullSurfaceBytes": 1470,
  "fullSurfaceSHA": "2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf",
  "statementBytes": 1154,
  "statementSHA": "3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf",
  "seeded": "207/207",
  "missing": [],
  "CP3Blob": "2c697e532e83989de8591fa6a4378747c6a501c0",
  "ipkgBlob": "da0c007ee08c4648e459296eb6f0e72a40e2ac89",
  "productionDiffEmpty": true,
  "reviewSHA": "61fc23ae4cea4565b442c840be39c41746ecbac73b8c2f73d04f1e3b4f4681e8",
  "holes": {
    "CanonicalSort": 2,
    "CrossTrace": 4,
    "DeletionChain": 0,
    "LocalDiamond": 0,
    "RenamingComposition": 1
  },
  "holeDelta": -1,
  "withCounts": [
    9,
    9
  ],
  "proofCommits": 57,
  "newDeclarations": 54,
  "implementationInvocations": 60,
  "implementationFailures": [
    "A8-1",
    "A14-1",
    "A17-1"
  ],
  "noStagedFiles": true,
  "LocalDiamond": "UNCHANGED byte-for-byte versus 919a548; no visibility exports",
  "prohibitedAdditions": {
    "\\bbelieve_me\\b": [],
    "\\bassert_total\\b": [],
    "^\\s*partial\\b": [],
    "\\?\\w+": [],
    "^\\s*let\\b": [],
    "\\bwith\\s*\\(": [],
    "\\bdeletionTheoremProof\\b": [],
    "\\bpostulate\\b": []
  },
  "status": "?? paper/\n?? review-o6-body-adversarial.md"
}
```

The validator also asserts byte-identical O9/O10 signatures **and bodies**,
the unchanged O11 signature, unchanged other hole names, per-source-commit
maximum of one new declaration, matching fresh-check evidence for every source
commit, sequential check windows, no added prohibited constructs, and whitespace
cleanliness over the whole shift diff. The net source deletion is the obsolete
private eager intermediate described above, not a theorem or premise downgrade.

The frozen `adjacentSwapSuffixSpike` extraction excludes its preceding export
keyword and following newline (which is separately verified). LocalDiamond is
**byte-identical to 919a548**, zero holes, no visibility exports, and hence no
new exported names/consumers to list. Production `src/` and `dgamma.ipkg` are
**byte-identical to 34b21c9**; CP3 blob is exactly
`2c697e532e83989de8591fa6a4378747c6a501c0`. The adversarial review remains
untracked and byte-unchanged, never staged, modified, committed or deleted.
No stray untracked research artifact or staged file remains. Audit-only changes
after the proof checks do not invalidate that source evidence.

## Status

**Fully proved this shift:** all six O11 producer parts; exact identity and
composed endpoint/registration accounting; authentic complete history recurrence;
constructor-owned Core/Step coherence; sealed total structural derivation fold;
**O11 at 8356a64**, so **DeletionChain has zero holes**. The full surviving
RegistrationDiscipline and full TARGET ReplayInvariantBundle remain retained.

**Partial overall:** the Theorem-73 campaign, not the DeletionChain module.

**Merely stated:** seven remaining research holes, split **CanonicalSort 2 /
CrossTrace 4 / DeletionChain 0 / LocalDiamond 0 / RenamingComposition 1**,
delta **-1** this shift. No new hole or escape hatch. Theorem 73 is not claimed.

**Next:** mandatory supervisor/reviewer milestone decision. Unit C is not
eligible under the remaining-time condition and stays unstarted. Independent
reviewer acceptance remains required; these reproducible self-checks are not
an independent review.
