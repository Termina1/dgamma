# R195 micro-unit receipts

Source freeze `3bd991710c76170d358dd5dadc07c676dfdb21f0`. A26/B16;42 retained declarations.
Every row is one exact-source guarded commit immediately after the named fresh PASS.
Rejected source/log/JSON snapshots remain in the compiler archive. No exhausted3/3 or body invocation.

| Unit | PASS invocation | Commit | Seconds | Sampled KiB | Declaration |
| --- | --- | --- | ---: | ---: | --- |
| A1 | A1-1 | `23f50e84` | 3.121 | 2,882,512 | `O20RootReplayOrdinals` |
| A2 | A2-1 | `4aa45649` | 3.113 | 2,882,304 | `o20IdentityRootReplayOrdinals` |
| A3 | A3-1 | `7d0f261c` | 3.108 | 4,744,528 | `o20ComposeRootReplayOrdinals` |
| A4 | A4-1 | `3045e188` | 3.131 | 5,660,992 | `o20RootOrdinalsAttached` |
| A5 | A5-1 | `d94c015e` | 3.116 | 2,472,112 | `r195RootOnlyNoChildBirth` |
| A6 | A6-1 | `d79669de` | 3.123 | 2,595,824 | `r195SwapRootOrdinals` |
| A7 | A7-1 | `af20f0b7` | 3.109 | 2,472,096 | `r195SwapRootOrdinalsInvolutive` |
| A8 | A8-1 | `f83259b4` | 3.132 | 2,595,792 | `r195RootLawFreeCorrespondence` |
| A9 | A9-1 | `5fa7af54` | 3.127 | 2,472,080 | `r195ActualRootOccurrence` |
| A10 | A10-1 | `7b5b3593` | 3.142 | 2,595,808 | `r195ReplayRecordDoesNotOwnRootLaw` |
| A11 | A11-1 | `07694389` | 3.121 | 2,366,000 | `O20GenerationOnlyDisposition` |
| A12 | A12-1 | `25e394c3` | 3.146 | 5,661,264 | `o20MatchedDispositionPacket` |
| A13 | A13-1 | `66800f62` | 3.133 | 5,659,200 | `o20DispositionChoice` |
| A14 | A14-1 | `93f4af42` | 3.121 | 5,659,136 | `o20DispositionPacket` |
| A15 | A15-2 | `06b85d9c` | 3.137 | 2,880,672 | `o20CanonicalGenerationDisposition` |
| A16 | A16-1 | `07091a90` | 3.140 | 2,882,848 | `o20CoveredGenerationDisposition` |
| A17 | A17-1 | `28db5873` | 3.113 | 2,884,128 | `o20OriginalGenerationDisposition` |
| A18 | A18-1 | `4fc66814` | 3.139 | 2,880,176 | `O20GenerationOnlyHistory` |
| A19 | A19-1 | `afdaa3bf` | 3.127 | 3,806,432 | `o20WholeOriginalGenerationHistory` |
| A20 | A20-1 | `19cb05d4` | 3.131 | 2,880,192 | `o20HistoryThroughReplay` |
| A21 | A21-1 | `ea7f660d` | 3.128 | 5,669,504 | `o20HistoryReplayAttachment` |
| A22 | A22-1 | `ffa63066` | 2.103 | 749,728 | `r195ClosingEvent` |
| A23 | A23-1 | `9203d2b3` | 2.081 | 875,296 | `r195ClosingScannedBirth` |
| A24 | A24-1 | `7ad87563` | 2.106 | 898,480 | `r195ActualClosingDisposition` |
| A25 | A25-1 | `6f7107c8` | 2.091 | 707,744 | `r195ClosingHistoryRetained` |
| A26 | A26-1 | `993d7fe4` | 2.091 | 672,480 | `r195ClosingReplayRetention` |
| B1 | B1-1 | `4f809252` | 3.143 | 3,810,720 | `o20IdentityProviderWord` |
| B2 | B2-1 | `ba5aa36e` | 3.143 | 3,816,384 | `o20IdentityParent` |
| B3 | B3-2 | `65d0b11e` | 3.139 | 3,816,384 | `o20IdentityLifecycle` |
| B4 | B4-1 | `97c53cf9` | 3.129 | 3,814,816 | `o20IdentityFiber` |
| B5 | B5-1 | `13e966e0` | 3.122 | 3,814,800 | `o20IdentityMaybeFiber` |
| B6 | B6-3 | `b049d5b0` | 3.140 | 3,816,384 | `o20IdentityAllNameCut` |
| B7 | B7-1 | `0069ab9d` | 3.131 | 3,816,400 | `o20IdentityHistoryCut` |
| B8 | B8-1 | `f5e4dd17` | 3.120 | 2,664,176 | `o20PresentAbsentImpossible` |
| B9 | B9-1 | `c9200390` | 3.125 | 2,761,904 | `o20CutRejectsPresentAbsent` |
| B10 | B10-1 | `58e74e64` | 2.080 | 2,067,312 | `r195VestigialCurrentCutImpossible` |
| B11 | B11-1 | `d8bfe2a5` | 2.102 | 2,204,560 | `r195VestigialInternalHistoryCut` |
| B12 | B12-1 | `0b25902b` | 2.106 | 1,937,280 | `r195OriginalEndpointRebaseObstruction` |
| B13 | B13-1 | `7a3540f5` | 3.105 | 2,217,392 | `o20DisagreementVestigialChoice` |
| B14 | B14-1 | `490dd369` | 3.118 | 2,217,392 | `o20DisagreementVestigial` |
| B15 | B15-1 | `fa57d30b` | 2.097 | 2,087,952 | `r195MismatchOwnsVestigialRemainder` |
| B16 | B16-1 | `3bd99171` | 2.094 | 1,444,384 | `r195RemovedRemainderActuallyAbsent` |

## Rejected invocations (not proof results)

- **A15-1**: exit1, fresh=True; Error: While processing right hand side of o20CanonicalGenerationDisposition. Undefined name acceptedAuthenticatedRegistrationMatching. . SHA256 `efff259ede8f8f1c8578054a955b6a0ee0d31d5fcc19c292c8d0203cb0d42bd7`.
- **B3-1**: exit1, fresh=True; Error: Unsolved holes:. SHA256 `1359da9cd5f0e2f87003cde3c0c0bb89ebfbc0b8d087b4b0cfc4045bf44fa983`.
- **B6-1**: exit1, fresh=True; Error: While processing right hand side of o20IdentityAllNameCut. Undefined name MkRenamedRuntimeEffects. . SHA256 `862772bdd4b4b5ebaae44f62376437b221567857e2db56e3dd99e1bbfa78ac6d`.
- **B6-2**: exit1, fresh=True; Error: While processing right hand side of o20IdentityAllNameCut. When unifying:. SHA256 `f0c127e116b8474c2dd7087b0febfa32fcb33b0e7aa305cba708a4d608e558a7`.

B6 passed on its THIRD permitted invocation; this is not an exhausted/reverted unit.
No fourth attempt, successful proof recheck exception, target mutation or source edit during a check.
S0-1 is the baseline CrossTrace check, not a new declaration. Final V checks are separate.
