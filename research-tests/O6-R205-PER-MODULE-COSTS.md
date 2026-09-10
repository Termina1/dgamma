# R205 per-invocation sampled costs

One compiler at a time. KiB are one-second SAMPLED RSS maxima, not OS high-water; zero means no compiler RSS sample was captured. Stops are not PASS.

| Invocation | Target | Seconds | Sample peak KiB | Guard KiB | Outcome |
|---|---|---:|---:|---:|---|
| P1 | `package` | 369.549 | 100669328 | 100663296 | RSS STOP |
| S1 | `src/DGamma/CP3.idr` | 1.063 | 0 | 67108864 | FAIL |
| S1-2 | `src/DGamma/CP3.idr` | 12.515 | 871120 | 67108864 | PASS |
| S2 | `src/DGamma/CP4AccumulatorControlChecks.idr` | 1.060 | 0 | 67108864 | PASS |
| S3 | `src/DGamma/CP4DeletionCommittedProviderPersistence.idr` | 1.065 | 0 | 67108864 | PASS |
| S4 | `src/DGamma/CP4DeletionGenerationBounds.idr` | 1.060 | 0 | 67108864 | PASS |
| S5 | `src/DGamma/CP4DeletionGenerationChecks.idr` | 1.062 | 0 | 67108864 | PASS |
| S6 | `src/DGamma/CP4DeletionGenerationFilter.idr` | 1.068 | 0 | 67108864 | PASS |
| S7 | `src/DGamma/CP4DeletionGenerationScan.idr` | 1.057 | 0 | 67108864 | PASS |
| S8 | `src/DGamma/CP4DeletionGenerationStamped.idr` | 1.070 | 0 | 67108864 | PASS |
| S9 | `src/DGamma/CP4DeletionSelectedForeignLifecycleAnchorCore.idr` | 1.067 | 0 | 67108864 | PASS |
| S10 | `src/DGamma/CP4DeletionSelectedForeignLifecycleAnchorRelianceResolved.idr` | 1.062 | 0 | 67108864 | PASS |
| S11 | `src/DGamma/CP4ParentSafety.idr` | 2.100 | 227696 | 67108864 | PASS |
| S12 | `src/DGamma/CP4ProgressBound.idr` | 1.065 | 0 | 67108864 | PASS |
| S13 | `src/DGamma/CP4ProgressFinite.idr` | 1.056 | 0 | 67108864 | PASS |
| S14 | `src/DGamma/CP4ProgressProgramBound.idr` | 1.056 | 0 | 67108864 | PASS |
| S15 | `src/DGamma/CP4ProgressUnloadingShape.idr` | 1.057 | 0 | 67108864 | PASS |
| S16 | `src/DGamma/CP4Support.idr` | 2.111 | 225872 | 67108864 | PASS |
| S17 | `src/DGamma/CP4SupportQuiescence.idr` | 2.098 | 239088 | 67108864 | PASS |
| S18 | `src/DGamma/CalculusChecks.idr` | 1.066 | 0 | 50331648 | PASS |
| S19 | `src/DGamma/Ordering.idr` | 9.401 | 2101280 | 50331648 | PASS |
| S20 | `src/DGamma/CP3Support.idr` | 2.108 | 332112 | 50331648 | PASS |
| S21 | `src/DGamma/CP4DeletionControl.idr` | 1.065 | 0 | 67108864 | PASS |
| S22 | `src/DGamma/CP4DeletionFilterSuccess.idr` | 1.066 | 0 | 67108864 | PASS |
| S23 | `src/DGamma/CP4DeletionPremiseSplit.idr` | 2.110 | 249296 | 67108864 | PASS |
| S24 | `src/DGamma/CP4DeletionSelectedForeignLifecycleAnchorTrace.idr` | 1.062 | 0 | 67108864 | PASS |
| S25 | `src/DGamma/CP4ProgressChecks.idr` | 2.104 | 243584 | 67108864 | PASS |
| S26 | `src/DGamma/CP4ProgressPotential.idr` | 1.058 | 0 | 67108864 | PASS |
| S27 | `src/DGamma/CP4ProgressPrecedence.idr` | 1.061 | 0 | 67108864 | PASS |
| S28 | `src/DGamma/CP4ProgressReliance.idr` | 2.102 | 243024 | 67108864 | PASS |
| S29 | `src/DGamma/CP4RestrictionChecks.idr` | 1.060 | 0 | 67108864 | PASS |
| S30 | `src/DGamma/CP4SupportActive.idr` | 1.064 | 0 | 67108864 | PASS |
| S31 | `src/DGamma/CP4SupportSolution.idr` | 209.255 | 67128512 | 67108864 | RSS STOP |
| S31-2 | `src/DGamma/CP4SupportSolution.idr` | 419.813 | 134435632 | 134217728 | RSS STOP |
| S31-3 | `src/DGamma/CP4SupportSolution.idr` | 476.350 | 154783872 | 209715200 | PRESSURE STOP |
| S31-4 | `src/DGamma/CP4SupportSolution.idr` | 986.352 | 168575296 | 209715200 | PASS |
| S32 | `src/DGamma/CP4TotalityChecks.idr` | 2.106 | 261856 | 67108864 | PASS |
| S33 | `src/DGamma/CP3StatementChecks.idr` | 22.953 | 1442528 | 67108864 | FAIL |
| S34 | `src/DGamma/CP4DeletionControlPlan.idr` | 1.052 | 0 | 67108864 | PASS |
| S35 | `src/DGamma/CP4DeletionReadiness.idr` | 1.067 | 0 | 67108864 | PASS |
| S36 | `src/DGamma/CP4DeletionSelectedForeignLifecycleAnchorClassify.idr` | 2.103 | 224304 | 67108864 | PASS |
| S37 | `src/DGamma/CP4DeletionSkeleton.idr` | 2.104 | 245344 | 67108864 | PASS |
| S38 | `src/DGamma/CP4FailureOutcomeChecks.idr` | 1.053 | 0 | 67108864 | PASS |
| S39 | `src/DGamma/CP4Lemma70.idr` | 1.053 | 0 | 67108864 | PASS |
| S40 | `src/DGamma/CP4ProgressNoDeadlock.idr` | 2.101 | 193712 | 67108864 | PASS |
| S41 | `src/DGamma/CP4ProgressStepCore.idr` | 1.059 | 0 | 67108864 | PASS |
| S42 | `src/DGamma/CP4ProgressUnloadingActive.idr` | 1.064 | 0 | 67108864 | PASS |
| S44 | `src/DGamma/CP4DeletionControlChecks.idr` | 1.067 | 0 | 67108864 | PASS |
| S45 | `src/DGamma/CP4DeletionPlanBuilder.idr` | 1.061 | 0 | 67108864 | PASS |
| S46 | `src/DGamma/CP4DeletionPlanEffects.idr` | 1.060 | 0 | 67108864 | PASS |
| S47 | `src/DGamma/CP4DeletionSelectedForeignLifecycleAnchorEndpoint.idr` | 1.062 | 0 | 67108864 | PASS |
| S48 | `src/DGamma/CP4DeletionSkeletonSuccess.idr` | 2.094 | 247616 | 67108864 | PASS |
| S49 | `src/DGamma/CP4ProgressStepAdvanceExit.idr` | 1.057 | 0 | 67108864 | PASS |
| S50 | `src/DGamma/CP4ProgressStepAdvanceStable.idr` | 1.060 | 0 | 67108864 | PASS |
| S51 | `src/DGamma/CP4ProgressStepBegin.idr` | 1.059 | 0 | 67108864 | PASS |
| S52 | `src/DGamma/CP4ProgressStepDivert.idr` | 1.074 | 0 | 67108864 | PASS |
| S53 | `src/DGamma/CP4ProgressStepLeave.idr` | 1.053 | 0 | 67108864 | PASS |
| S54 | `src/DGamma/CP4ProgressStepUnload.idr` | 1.061 | 0 | 67108864 | PASS |
| S55 | `src/DGamma/CP4ProgressUnloadingActiveStep.idr` | 1.056 | 0 | 67108864 | PASS |
| S56 | `src/DGamma/CP4ProgressUnloadingReloading.idr` | 1.066 | 0 | 67108864 | PASS |
| S57 | `src/DGamma/CP4DeletionGenerationUnique.idr` | 1.058 | 0 | 67108864 | PASS |
| S58 | `src/DGamma/CP4ProgressStepAdvance.idr` | 2.095 | 249312 | 67108864 | PASS |
| S59 | `src/DGamma/CP4ProgressUnloadingClassify.idr` | 1.068 | 0 | 67108864 | PASS |
| S60 | `src/DGamma/CP4DeletionInactiveInvariant.idr` | 2.091 | 229664 | 67108864 | PASS |
| S61 | `src/DGamma/CP4DeletionPlanSuccess.idr` | 1.061 | 0 | 67108864 | PASS |
| S62 | `src/DGamma/CP4ProgressStep.idr` | 1.063 | 0 | 67108864 | PASS |
| S63 | `src/DGamma/CP4ProgressUnloadingDescent.idr` | 1.060 | 0 | 67108864 | PASS |
| S64 | `src/DGamma/CP4RecoverySelectedReplayStep.idr` | 2.097 | 231040 | 67108864 | PASS |
| S65 | `src/DGamma/CP4DeletionControlOrchestration.idr` | 2.097 | 232064 | 67108864 | PASS |
| S66 | `src/DGamma/CP4DeletionEmptyTableInvariant.idr` | 1.061 | 0 | 67108864 | PASS |
| S67 | `src/DGamma/CP4DeletionPlanBoundary.idr` | 1.063 | 0 | 67108864 | PASS |
| S68 | `src/DGamma/CP4DeletionWithdrawalCurrent.idr` | 1.061 | 0 | 67108864 | PASS |
| S69 | `src/DGamma/CP4ProgressNoDeadlockFinal.idr` | 1.060 | 0 | 67108864 | PASS |
| S70 | `src/DGamma/CP4ProgressNumeric.idr` | 2.118 | 233504 | 67108864 | PASS |
| S71 | `src/DGamma/CP4RecoveryReplay.idr` | 2.103 | 228688 | 67108864 | PASS |
| S72 | `src/DGamma/CP4DeletionChildlessInvariant.idr` | 2.099 | 224416 | 67108864 | PASS |
| S73 | `src/DGamma/CP4DeletionRetainedAction.idr` | 2.098 | 228432 | 67108864 | PASS |
| S74 | `src/DGamma/CP4DeletionSelectedEffectCore.idr` | 1.069 | 0 | 67108864 | PASS |
| S75 | `src/DGamma/CP4ProgressProof.idr` | 1.055 | 0 | 67108864 | PASS |
| S76 | `src/DGamma/CP4TerminalRecovery.idr` | 2.100 | 260128 | 67108864 | PASS |
| S77 | `src/DGamma/CP4DeletionPlanComplete.idr` | 1.057 | 0 | 67108864 | PASS |
| S78 | `src/DGamma/CP4DeletionSelectedCloseEffect.idr` | 1.059 | 0 | 67108864 | PASS |
| S79 | `src/DGamma/CP4DeletionSelectedEffectForeign.idr` | 1.056 | 0 | 67108864 | PASS |
| S80 | `src/DGamma/CP4DeletionSelectedForeignLifecycleAdvanceOutcome.idr` | 2.104 | 198880 | 67108864 | PASS |
| S81 | `src/DGamma/CP4ResolutionCoherence.idr` | 1.069 | 0 | 67108864 | PASS |
| S82 | `src/DGamma/CP4DeletionNoEpisodeReplay.idr` | 2.092 | 224944 | 67108864 | PASS |
| S83 | `src/DGamma/CP4DeletionPlanEmpty.idr` | 1.060 | 0 | 67108864 | PASS |
| S84 | `src/DGamma/CP4DeletionPlanRuntime.idr` | 1.059 | 0 | 67108864 | PASS |
| S85 | `src/DGamma/CP4DeletionSelectedBoundary.idr` | 2.099 | 246064 | 67108864 | PASS |
| S86 | `src/DGamma/CP4DeletionPlanCommute.idr` | 2.098 | 221152 | 67108864 | PASS |
| S87 | `src/DGamma/CP4DeletionRelationalBoundary.idr` | 1.058 | 0 | 67108864 | PASS |
| S88 | `src/DGamma/CP4DeletionSelectedEpisodeFoldCore.idr` | 2.110 | 214304 | 67108864 | PASS |
| S89 | `src/DGamma/CP4DeletionSelectedForeignControlCore.idr` | 1.055 | 0 | 67108864 | PASS |
| S90 | `src/DGamma/CP4DeletionSelectedForeignTables.idr` | 1.062 | 0 | 67108864 | PASS |
| S91 | `src/DGamma/CP4DeletionSelectedStart.idr` | 2.101 | 256512 | 67108864 | PASS |
| S92 | `src/DGamma/CP4DeletionBoundaryLifecycleCore.idr` | 2.103 | 227856 | 67108864 | PASS |
| S93 | `src/DGamma/CP4DeletionBoundaryPlan.idr` | 1.060 | 0 | 67108864 | PASS |
| S94 | `src/DGamma/CP4DeletionPostCloseUpgrade.idr` | 1.065 | 0 | 67108864 | PASS |
| S95 | `src/DGamma/CP4DeletionRelationalActionCore.idr` | 1.058 | 0 | 67108864 | PASS |
| S96 | `src/DGamma/CP4DeletionSelectedForeignLifecycleCore.idr` | 1.061 | 0 | 67108864 | PASS |
| S97 | `src/DGamma/CP4DeletionBoundaryDeleted.idr` | 3.134 | 239584 | 67108864 | PASS |
| S98 | `src/DGamma/CP4DeletionBoundaryLifecycleAdvance.idr` | 3.143 | 273552 | 67108864 | PASS |
| S99 | `src/DGamma/CP4DeletionBoundaryLifecycleBegin.idr` | 1.058 | 0 | 67108864 | PASS |
| S100 | `src/DGamma/CP4DeletionBoundaryLifecycleDivert.idr` | 1.061 | 0 | 67108864 | PASS |
| S101 | `src/DGamma/CP4DeletionBoundaryLifecycleLeave.idr` | 1.058 | 0 | 67108864 | PASS |
| S102 | `src/DGamma/CP4DeletionBoundaryLifecycleUnload.idr` | 1.062 | 0 | 67108864 | PASS |
| S103 | `src/DGamma/CP4DeletionRelatedLifecycleEffectMap.idr` | 2.098 | 251296 | 67108864 | PASS |
| S104 | `src/DGamma/CP4DeletionSelectedDeletedPlan.idr` | 2.105 | 239120 | 67108864 | PASS |
| S105 | `src/DGamma/CP4DeletionSelectedForeignLifecycleAnchorOpen.idr` | 2.110 | 255456 | 67108864 | PASS |
| S106 | `src/DGamma/CP4DeletionSelectedForeignLifecycleAnchorRelianceSelected.idr` | 1.062 | 0 | 67108864 | PASS |
| S107 | `src/DGamma/CP4DeletionSelectedForeignLifecycleReplayCore.idr` | 1.053 | 0 | 67108864 | PASS |
| S108 | `src/DGamma/CP4DeletionSelectedOwn.idr` | 3.139 | 369040 | 67108864 | PASS |
| S109 | `src/DGamma/CP4DeletionBoundaryRetained.idr` | 7.346 | 407136 | 67108864 | PASS |
| S110 | `src/DGamma/CP4DeletionEndpoint.idr` | 2.103 | 254080 | 67108864 | PASS |
| S111 | `src/DGamma/CP4DeletionPostCloseEffectReplay.idr` | 1.060 | 0 | 67108864 | PASS |
| S112 | `src/DGamma/CP4DeletionSelectedDeletedCore.idr` | 2.112 | 217008 | 67108864 | PASS |
| S113 | `src/DGamma/CP4DeletionSelectedForeignLifecycleAdvance.idr` | 4.197 | 291920 | 67108864 | PASS |
| S114 | `src/DGamma/CP4DeletionSelectedForeignLifecycleAnchorRelianceCurrent.idr` | 1.062 | 0 | 67108864 | PASS |
| S115 | `src/DGamma/CP4DeletionSelectedForeignLifecycleFrame.idr` | 2.105 | 233104 | 67108864 | PASS |
| S116 | `src/DGamma/CP4DeletionSelectedForeignLifecycleUnload.idr` | 6.285 | 237216 | 67108864 | PASS |
| S117 | `src/DGamma/CP4DeletionSelectedForeignOrchestration.idr` | 2.106 | 235184 | 67108864 | PASS |
| S118 | `src/DGamma/CP4DeletionSelectedOwnDispatch.idr` | 1.061 | 0 | 67108864 | PASS |
| S119 | `src/DGamma/CP4DeletionRelationalLifecycleSources.idr` | 2.099 | 223728 | 67108864 | PASS |
| S120 | `src/DGamma/CP4DeletionSelectedCloseBoundary.idr` | 2.099 | 241056 | 67108864 | PASS |
| S121 | `src/DGamma/CP4DeletionSelectedDeletedOrchestration.idr` | 3.141 | 377200 | 67108864 | PASS |
| S122 | `src/DGamma/CP4DeletionSelectedForeignLifecycleAnchorRelianceClose.idr` | 1.061 | 0 | 67108864 | PASS |
| S123 | `src/DGamma/CP4DeletionSelectedForeignLifecycleCrossing.idr` | 2.106 | 243776 | 67108864 | PASS |
| S124 | `src/DGamma/CP4DeletionSelectedForeignLifecycleGuards.idr` | 1.061 | 0 | 67108864 | PASS |
| S125 | `src/DGamma/CP4DeletionSelectedRetire.idr` | 3.134 | 311104 | 67108864 | PASS |
| S126 | `src/DGamma/CP4DeletionSuffixFold.idr` | 1.062 | 0 | 67108864 | PASS |
| S127 | `src/DGamma/CP4DeletionPostCloseFinal.idr` | 2.101 | 213904 | 67108864 | PASS |
| S128 | `src/DGamma/CP4DeletionRelationalLifecycleCore.idr` | 2.108 | 252944 | 67108864 | PASS |
| S129 | `src/DGamma/CP4DeletionRelationalSuffixFold.idr` | 2.101 | 247824 | 67108864 | PASS |
| S130 | `src/DGamma/CP4DeletionRetirementPersistence.idr` | 2.109 | 228496 | 67108864 | PASS |
| S131 | `src/DGamma/CP4DeletionSelectedDeletedDispatch.idr` | 1.058 | 0 | 67108864 | PASS |
| S132 | `src/DGamma/CP4DeletionSelectedForeignLifecycleAdvanceDispatchCore.idr` | 1.056 | 0 | 67108864 | PASS |
| S133 | `src/DGamma/CP4DeletionSelectedForeignLifecycleAnchorReliance.idr` | 1.054 | 0 | 67108864 | PASS |
| S134 | `src/DGamma/CP4DeletionSelectedForeignLifecycleBegin.idr` | 2.096 | 220160 | 67108864 | PASS |
| S135 | `src/DGamma/CP4DeletionSelectedForeignLifecycleDivert.idr` | 6.289 | 245280 | 67108864 | PASS |
| S136 | `src/DGamma/CP4DeletionSelectedForeignLifecycleLeave.idr` | 5.243 | 272112 | 67108864 | PASS |
| S137 | `src/DGamma/CP4DeletionSelectedForeignOrchestrationStep.idr` | 2.107 | 230016 | 67108864 | PASS |
| S138 | `src/DGamma/CP4DeletionPostCloseOrchestration.idr` | 3.141 | 273232 | 67108864 | PASS |
| S139 | `src/DGamma/CP4DeletionRelationalActionOrchestration.idr` | 3.144 | 322208 | 67108864 | PASS |
| S140 | `src/DGamma/CP4DeletionRelationalLifecycleAdvanceCases.idr` | 4.172 | 308768 | 67108864 | PASS |
| S141 | `src/DGamma/CP4DeletionSelectedForeignAdvanceAgreement.idr` | 2.097 | 224160 | 67108864 | PASS |
| S142 | `src/DGamma/CP4DeletionSelectedForeignLifecycleAdvanceDispatch.idr` | 3.149 | 255632 | 67108864 | PASS |
| S143 | `src/DGamma/CP4DeletionSelectedForeignLifecycleProviderFrame.idr` | 2.102 | 293872 | 67108864 | PASS |
| S144 | `src/DGamma/CP4DeletionSelectedForeignLifecycleStep.idr` | 2.103 | 249856 | 67108864 | PASS |
| S33-2 | `src/DGamma/CP3StatementChecks.idr` | 17.756 | 1398384 | 67108864 | FAIL |
| S33-3 | `src/DGamma/CP3StatementChecks.idr` | 17.800 | 1465424 | 67108864 | FAIL |
| S34-1 | `src/DGamma/CP3StatementChecks.idr` | 24.023 | 2042880 | 67108864 | PASS |
| S43 | `src/DGamma/CP3VestigialChecks.idr` | 180.604 | 5711968 | 50331648 | PASS |
| S145 | `src/DGamma/CP4DeletionPostCloseDeleted.idr` | 2.114 | 247104 | 67108864 | PASS |
| S146 | `src/DGamma/CP4DeletionPostCloseRemove.idr` | 2.101 | 268368 | 67108864 | PASS |
| S147 | `src/DGamma/CP4DeletionPostCloseSelectedRetire.idr` | 2.102 | 266016 | 67108864 | PASS |
| S148 | `src/DGamma/CP4DeletionRelationalLifecycleAdvanceDispatch.idr` | 3.142 | 285616 | 67108864 | PASS |
| S149 | `src/DGamma/CP4DeletionRelationalLifecycleBegin.idr` | 2.102 | 243616 | 67108864 | PASS |
| S150 | `src/DGamma/CP4DeletionRelationalLifecycleDivert.idr` | 3.145 | 254000 | 67108864 | PASS |
| S151 | `src/DGamma/CP4DeletionRelationalLifecycleLeave.idr` | 3.143 | 302736 | 67108864 | PASS |
| S152 | `src/DGamma/CP4DeletionRelationalLifecycleUnload.idr` | 3.138 | 256208 | 67108864 | PASS |
| S153 | `src/DGamma/CP4DeletionSelectedForeignLifecycleDispatch.idr` | 2.107 | 263376 | 67108864 | PASS |
| S154 | `src/DGamma/CP4DeletionRelationalLifecycleAdvance.idr` | 2.089 | 249264 | 67108864 | PASS |
| S155 | `src/DGamma/CP4DeletionSelectedForeignLifecycleReplay.idr` | 3.142 | 252720 | 67108864 | PASS |
| S156 | `src/DGamma/CP4DeletionPostCloseLifecycle.idr` | 4.169 | 461584 | 67108864 | PASS |
| S157 | `src/DGamma/CP4DeletionRelationalActionReplay.idr` | 2.101 | 258528 | 67108864 | PASS |
| S158 | `src/DGamma/CP4DeletionSelectedEpisodeReplay.idr` | 5.231 | 414432 | 67108864 | PASS |
| S159 | `src/DGamma/CP4DeletionPostCloseFold.idr` | 3.145 | 253872 | 67108864 | PASS |
| S160 | `src/DGamma/CP4DeletionSelectedEpisodeAnchors.idr` | 5.244 | 416080 | 67108864 | PASS |
| S161 | `src/DGamma/CP4DeletionSelectedEpisodeFold.idr` | 4.184 | 340512 | 67108864 | PASS |
| S162 | `src/DGamma/CP4DeletionWithdrawalJoin.idr` | 3.136 | 251024 | 67108864 | PASS |
| S163 | `src/DGamma/CP4DeletionTheorem.idr` | 9.393 | 627184 | 67108864 | PASS |
| P2 | `package` | 15.634 | 230416 | 100663296 | PASS |
| V1 | `research-tests/DGamma/R175OldGroupingPolicyCycle.idr` | 1.058 | 0 | 50331648 | PASS |
| V2 | `research/DGamma/CP5ConfluenceWorkMeasureSpike.idr` | 1.062 | 0 | 50331648 | PASS |
| V3 | `research-tests/DGamma/R7DuplicateLabelNegative.idr` | 1.069 | 0 | 50331648 | PASS expected rejection |
| V4 | `research/DGamma/CP5ConfluenceRankObservationSpike.idr` | 1.079 | 0 | 50331648 | PASS |
| V5 | `research/DGamma/CP5O19CommutedDomainSpike.idr` | 1.052 | 0 | 50331648 | PASS |
| V6 | `research/DGamma/CP5ProviderHeadObservedSpike.idr` | 1.064 | 0 | 50331648 | PASS |
| V7 | `research-tests/DGamma/R13O3IndependentDictionaryNegative.idr` | 1.061 | 0 | 50331648 | PASS expected rejection |
| V8 | `research-tests/DGamma/R14O4IndependentDictionaryNegative.idr` | 1.067 | 0 | 50331648 | PASS expected rejection |
| V9 | `research-tests/DGamma/R15O5IndependentDictionaryNegative.idr` | 1.060 | 0 | 50331648 | PASS expected rejection |
| V10 | `research-tests/DGamma/R34RemoveChildOrientationNegative.idr` | 1.067 | 0 | 50331648 | PASS expected rejection |
| V11 | `research-tests/DGamma/R40RetiredExactMapShapesPositive.idr` | 1.066 | 0 | 50331648 | PASS |
| V12 | `research-tests/DGamma/R43JointAlignedHeadProbePositive.idr` | 1.575 | 0 | 50331648 | PASS |
| V13 | `research-tests/DGamma/R44IteratorForwardNestedCoverageNegative.idr` | 1.067 | 0 | 50331648 | PASS expected rejection |
| V14 | `research-tests/DGamma/R44IteratorStageOccurrencePartitionPositive.idr` | 1.056 | 0 | 50331648 | PASS |
| V15 | `research-tests/DGamma/R44IteratorYieldedNestedCoverageNegative.idr` | 1.060 | 0 | 50331648 | PASS expected rejection |
| V16 | `research-tests/DGamma/R17WrongLookupControlNegative.idr` | 1.055 | 0 | 50331648 | PASS expected rejection |
| V17 | `research-tests/DGamma/R38UnloadExactMapFromRuntimeAccumulatorNegative.idr` | 1.058 | 0 | 50331648 | PASS expected rejection |
| V18 | `research-tests/DGamma/R41PointwiseRelianceProjectionNegative.idr` | 1.066 | 0 | 50331648 | PASS expected rejection |
| V19 | `research/DGamma/CP5ActorLifecycleOnlyExtended.idr` | 2.111 | 276016 | 50331648 | FAIL |
| V20 | `research/DGamma/CP5AvailabilityAwarePlacement.idr` | 1.060 | 0 | 50331648 | FAIL |
| V21 | `research/DGamma/CP5GeneratedOrchestrationMatched.idr` | 1.058 | 0 | 50331648 | PASS |
| V22 | `research/DGamma/CP5O20ActivationPositionStepSpike.idr` | 1.067 | 0 | 50331648 | PASS |
| V23 | `research/DGamma/CP5ObservedInstalledLifecycleSpike.idr` | 1.054 | 0 | 50331648 | PASS |
| V24 | `research/DGamma/CP5RankedTraceSelectionSpike.idr` | 1.059 | 0 | 50331648 | PASS |
| V25 | `research/DGamma/CP5UniqueRawNameInsertions.idr` | 1.067 | 0 | 50331648 | PASS |
| V26 | `research-tests/DGamma/R174O17ProvisionProtocol.idr` | 2.105 | 247168 | 50331648 | PASS |
| V27 | `research-tests/DGamma/R179O19ObservedExecution.idr` | 3.144 | 276912 | 50331648 | PASS |
| V28 | `research-tests/DGamma/R197ProviderHeadObservedPositive.idr` | 1.069 | 0 | 50331648 | PASS |
| V29 | `research/DGamma/CP5O20GlobalActivationHistorySpike.idr` | 2.097 | 231440 | 50331648 | PASS |
| V30 | `research/DGamma/CP5RetiredFlagEvaluationSpike.idr` | 2.100 | 206400 | 50331648 | PASS |
| V31 | `research-tests/DGamma/R180O19ObservedCompletion.idr` | 2.102 | 260400 | 50331648 | PASS |
| V32 | `research-tests/DGamma/R181O19SafetyCompletion.idr` | 32.377 | 2197280 | 50331648 | PASS |
| V33 | `research/DGamma/CP5O19ActualCommutedDomainSpike.idr` | 1.077 | 0 | 50331648 | PASS |
| V34 | `research-tests/DGamma/R181O19LocatedBlocks.idr` | 2.096 | 552144 | 50331648 | FAIL |
| V35 | `research/DGamma/CP5RawClosingRankSpike.idr` | 2.105 | 280544 | 50331648 | PASS |
| V36 | `research/DGamma/CP5CurrentGenerationBirthSpike.idr` | 2.096 | 241600 | 50331648 | PASS |
| V37 | `research/DGamma/CP5ImmutableBirthMetadataSpike.idr` | 2.104 | 236384 | 50331648 | PASS |
| V38 | `research/DGamma/CP5SupportEdgeInductionSpike.idr` | 1.065 | 0 | 50331648 | PASS |
| V39 | `research/DGamma/CP5RegistrationParentBirthSpike.idr` | 1.065 | 0 | 50331648 | PASS |
| V40 | `research/DGamma/CP5RetirementHistorySpike.idr` | 2.098 | 256016 | 50331648 | PASS |
| V41 | `research/DGamma/CP5GeneratedRetirementTransportSpike.idr` | 1.057 | 0 | 50331648 | PASS |
| V42 | `research/DGamma/CP5RootOrchestrationTransportSpike.idr` | 1.057 | 0 | 50331648 | PASS |
| V43 | `research/DGamma/CP5ConfluenceLocalDiamondSpike.idr` | 484.375 | 50508816 | 54525952 | PASS |
| L1-1 | `research/DGamma/CP5AvailabilityAwarePlacement.idr` | 1.070 | 0 | 50331648 | PASS |
| L2-1 | `research-tests/DGamma/R181O19LocatedBlocks.idr` | 3.138 | 552128 | 50331648 | PASS |
| V44 | `research-tests/DGamma/R10AdjacentSwapMapCloneNegative.idr` | 1.054 | 0 | 50331648 | PASS expected rejection |
| V49 | `research-tests/DGamma/R13O3AlignedProducerPositive.idr` | 1.067 | 0 | 50331648 | PASS |
| V50 | `research-tests/DGamma/R14O4AlignedProducerPositive.idr` | 1.060 | 0 | 50331648 | PASS |
| V51 | `research-tests/DGamma/R15O5AlignedProducerPositive.idr` | 2.096 | 671936 | 50331648 | PASS |
| V52 | `research-tests/DGamma/R174O17ProvisionCollisionCandidate.idr` | 5.231 | 641648 | 50331648 | FAIL |
| V53 | `research-tests/DGamma/R17FullResultImpossibility.idr` | 2.106 | 742944 | 50331648 | PASS |
| V54 | `research-tests/DGamma/R181O19UniquenessAndBundle.idr` | 2.102 | 654944 | 50331648 | PASS |
| V55 | `research-tests/DGamma/R18ExternalOrderProducerPositive.idr` | 6.260 | 779328 | 50331648 | FAIL |
| V56 | `research-tests/DGamma/R18OccurrenceFoldArbitrarySuffixImpossibilityPositive.idr` | 2.093 | 742320 | 50331648 | PASS |
| V57 | `research-tests/DGamma/R19CrossStateRetireReplayProbePositive.idr` | 2.107 | 670752 | 50331648 | PASS |
| V58 | `research-tests/DGamma/R19SealedReplayConstructorNegative.idr` | 1.070 | 0 | 50331648 | PASS expected rejection |
| V59 | `research-tests/DGamma/R20WholeBundleMovedAlignmentNegative.idr` | 1.058 | 0 | 50331648 | PASS expected rejection |
| V60 | `research-tests/DGamma/R21RepeatedIterProducerAlignmentNegative.idr` | 1.063 | 0 | 50331648 | PASS expected rejection |
| V61 | `research-tests/DGamma/R21WholeBundleQuietTransportNegative.idr` | 1.063 | 0 | 50331648 | PASS expected rejection |
| V62 | `research-tests/DGamma/R22QuietnessDomainAuditPositive.idr` | 1.053 | 0 | 50331648 | PASS |
| V63 | `research-tests/DGamma/R23PointwiseAdvanceReplayNegative.idr` | 1.064 | 0 | 50331648 | PASS expected rejection |
| V64 | `research-tests/DGamma/R24CorrectedWholeAlignmentNegative.idr` | 1.070 | 0 | 50331648 | PASS expected rejection |
| V65 | `research-tests/DGamma/R30AdjacentSwapResultConstructorNegative.idr` | 1.067 | 0 | 50331648 | PASS expected rejection |
| V66 | `research-tests/DGamma/R39RelationalMapAlgebraPositive.idr` | 1.067 | 0 | 50331648 | PASS |
| V67 | `research-tests/DGamma/R45BareDiamondDisciplineCounterexamplePositive.idr` | 4.184 | 671840 | 50331648 | PASS |
| V68 | `research-tests/DGamma/R46RetirementRecoverySwapSafetyDesignPositive.idr` | 3.137 | 1326176 | 50331648 | PASS |
| V69 | `research-tests/DGamma/R4OADiamondApplication.idr` | 1.062 | 0 | 50331648 | PASS |
| V70 | `research-tests/DGamma/R6OccurrenceFoldPositive.idr` | 1.061 | 0 | 50331648 | PASS |
| V71 | `research/DGamma/CP5O20NativeTargetAttachmentSpike.idr` | 2.109 | 690368 | 50331648 | PASS |
| V72 | `research/DGamma/CP5UniqueRawNameOrdinalCapital.idr` | 296.473 | 44779072 | 50331648 | PASS |
| V75 | `research-tests/DGamma/R178GeneratedOrchestrationFixtures.idr` | 1.062 | 0 | 50331648 | PASS |
| V76 | `research-tests/DGamma/R181O19Independence.idr` | 2.104 | 784656 | 50331648 | PASS |
| V77 | `research-tests/DGamma/R198RepeatedTagStageProbe.idr` | 1.058 | 0 | 50331648 | PASS |
| V78 | `research-tests/DGamma/R39AdvanceYieldedMapProducerPositive.idr` | 1.067 | 0 | 50331648 | PASS |
| V79 | `research-tests/DGamma/R39RelationalHeadProducerPositive.idr` | 2.104 | 727808 | 50331648 | PASS |
| V80 | `research-tests/DGamma/R45BareDiamondFalseDisciplineNegative.idr` | 1.058 | 0 | 50331648 | PASS expected rejection |
| V81 | `research-tests/DGamma/R45BareDiamondSafetyProjectionNegative.idr` | 1.063 | 0 | 50331648 | PASS expected rejection |
| V82 | `research-tests/DGamma/R45GenuineDiamondSafetyDesignPositive.idr` | 1.059 | 0 | 50331648 | PASS |
| V83 | `research-tests/DGamma/R46RetirementRecoveryLiveSafetyNegative.idr` | 1.069 | 0 | 50331648 | PASS expected rejection |
| V84 | `research-tests/DGamma/R39TraceGeneratorRespectPositive.idr` | 2.099 | 671328 | 50331648 | PASS |
| V85 | `research-tests/DGamma/R45OpaqueGenuineAdjacentInputNegative.idr` | 1.068 | 0 | 50331648 | PASS expected rejection |
| V86 | `research-tests/DGamma/R39RelationalIndependenceConsumerPositive.idr` | 2.095 | 0 | 50331648 | PASS |
| V87 | `research/DGamma/CP5ConfluenceDeletionChainSpike.idr` | 77.252 | 4905120 | 50331648 | PASS |
| V88 | `research-tests/DGamma/R10DeletionStepMapCloneNegative.idr` | 1.061 | 0 | 50331648 | PASS expected rejection |
| V89 | `research-tests/DGamma/R10ReductionMapCloneNegative.idr` | 1.059 | 0 | 50331648 | PASS expected rejection |
| V93 | `research-tests/DGamma/R137O8RawNameReuseCountershape.idr` | 3.141 | 361312 | 50331648 | PASS |
| V94 | `research-tests/DGamma/R171CoreHistoryCloneNegative.idr` | 1.067 | 0 | 50331648 | FAIL |
| V95 | `research-tests/DGamma/R171StepAccountingCloneNegative.idr` | 1.065 | 0 | 50331648 | FAIL |
| V96 | `research-tests/DGamma/R19SealedReplayCertificateScopingPositive.idr` | 2.099 | 966624 | 50331648 | PASS |
| V97 | `research-tests/DGamma/R19SuffixFreeFullAdjacentCertificatePositive.idr` | 2.096 | 727568 | 50331648 | PASS |
| V98 | `research-tests/DGamma/R20CorrectedSealedReplayEnvelopeScopingPositive.idr` | 2.101 | 894576 | 50331648 | PASS |
| V99 | `research-tests/DGamma/R7DeletionBoundariesPositive.idr` | 2.101 | 677568 | 50331648 | PASS |
| V100 | `research/DGamma/CP5ConfluenceCanonicalSortSpike.idr` | 159.610 | 18296368 | 50331648 | FAIL |
| V101 | `research/DGamma/CP5O20DeletionRetainedUnloadSpike.idr` | 3.151 | 614000 | 50331648 | PASS |
| V102 | `research/DGamma/CP5SupportedBirthCoverageSpike.idr` | 2.107 | 360880 | 50331648 | PASS |
| V103 | `research/DGamma/CP5UniqueRawNameDeletion.idr` | 2.098 | 619360 | 50331648 | PASS |
| V110 | `research-tests/DGamma/R137O8RawNameReuseCountershapeTrace.idr` | 2.108 | 608768 | 50331648 | PASS |
| V113 | `research-tests/DGamma/R176ReductionUniqueDirectionNegative.idr` | 1.060 | 0 | 50331648 | PASS expected rejection |
| V115 | `research-tests/DGamma/R21MovedOutputAlignmentScopingPositive.idr` | 2.100 | 668592 | 50331648 | PASS |
| V121 | `research-tests/DGamma/R137O8RawNameReuseCountershapeProof.idr` | 3.133 | 635520 | 50331648 | PASS |
| V125 | `research-tests/DGamma/R20WholeBundleAlignmentGapPositive.idr` | 24.018 | 1932192 | 50331648 | PASS |
| V126 | `research-tests/DGamma/R21CandidateIndependentDictionaryNegative.idr` | 1.054 | 0 | 50331648 | PASS expected rejection |
| V143 | `research-tests/DGamma/R137O8GenerationIntervalRatification.idr` | 1.054 | 0 | 50331648 | FAIL |
| V100-2 | `research/DGamma/CP5ConfluenceCanonicalSortSpike.idr` | 53.236 | 22012192 | 50331648 | PASS |
| L3-1 | `research-tests/DGamma/R174O17ProvisionCollisionCandidate.idr` | 6.300 | 999600 | 50331648 | PASS |
| V73 | `research-tests/DGamma/R174O17ProvisionCollisionUnique.idr` | 1.058 | 0 | 50331648 | PASS |
| V74 | `research-tests/DGamma/R174O17SortedProvisionGuard.idr` | 1.062 | 0 | 50331648 | PASS |
| V104 | `research-tests/DGamma/R10CoherentBothHalvesCapitalNegative.idr` | 1.057 | 0 | 50331648 | PASS expected rejection |
| V105 | `research-tests/DGamma/R10ProvenanceProjectionPositive.idr` | 2.106 | 3523920 | 50331648 | PASS |
| V106 | `research-tests/DGamma/R10SortedMapCloneNegative.idr` | 1.062 | 0 | 50331648 | PASS expected rejection |
| V111 | `research-tests/DGamma/R172O17OpenParentRootReuseCandidate.idr` | 47.026 | 1692096 | 50331648 | FAIL |
| V112 | `research-tests/DGamma/R173CanonicalBlockWorklistFixtures.idr` | 2.096 | 2461488 | 50331648 | PASS |
| V114 | `research-tests/DGamma/R176UnsealedOriginUniqueNegative.idr` | 1.061 | 0 | 50331648 | PASS expected rejection |
| V116 | `research-tests/DGamma/R4VestigialSimultaneous.idr` | 2.105 | 3953616 | 50331648 | PASS |
| V117 | `research-tests/DGamma/R8AuthenticationProjectionPositive.idr` | 2.104 | 2399744 | 50331648 | PASS |
| V118 | `research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr` | 9.378 | 3399984 | 50331648 | PASS |
| V119 | `research/DGamma/CP5RankedEarlyApplicabilitySpike.idr` | 2.095 | 926352 | 50331648 | PASS |
| V124 | `research-tests/DGamma/R179RankedTraceSelectionPositive.idr` | 12.525 | 3075488 | 50331648 | PASS |
| V128 | `research-tests/DGamma/R4ScannerProducerConsumers.idr` | 2.105 | 3950848 | 50331648 | PASS |
| V129 | `research-tests/DGamma/R6ScannerRetainedFixturesPositive.idr` | 2.108 | 2943200 | 50331648 | PASS |
| V130 | `research-tests/DGamma/R6ScannerThirdOrdering.idr` | 2.101 | 2941888 | 50331648 | PASS |
| V131 | `research-tests/DGamma/R6ScannerWrongGenerationNegative.idr` | 1.063 | 0 | 50331648 | PASS expected rejection |
| V132 | `research-tests/DGamma/R8BridgeAuthenticatedDirectionPositive.idr` | 2.102 | 2275888 | 50331648 | PASS |
| V133 | `research-tests/DGamma/R8BridgeWrongBirthNegative.idr` | 1.060 | 0 | 50331648 | PASS expected rejection |
| V134 | `research-tests/DGamma/R8PublicScheduleCannotReachBridgeNegative.idr` | 3.139 | 650064 | 50331648 | PASS expected rejection |
| V135 | `research-tests/DGamma/R8WrongOccurrenceBridgeNegative.idr` | 1.058 | 0 | 50331648 | PASS expected rejection |
| V136 | `research/DGamma/CP5AcceptedRetirementTransportSpike.idr` | 3.137 | 2938416 | 50331648 | PASS |
| V137 | `research/DGamma/CP5MatchedBirthMetadataSpike.idr` | 4.189 | 2947968 | 50331648 | PASS |
| V138 | `research/DGamma/CP5O19AdjacentReplayProducerSpike.idr` | 3.156 | 3004352 | 50331648 | PASS |
| V139 | `research/DGamma/CP5O20CanonicalBirthDispositionSpike.idr` | 3.156 | 3004416 | 50331648 | PASS |
| V140 | `research/DGamma/CP5O20DeletionRetainedBirthSpike.idr` | 3.136 | 3004544 | 50331648 | PASS |
| V141 | `research/DGamma/CP5O21EndpointIdentitySpike.idr` | 3.152 | 3015040 | 50331648 | PASS |
| V142 | `research/DGamma/CP5RootBirthCoverageSpike.idr` | 2.104 | 261376 | 50331648 | PASS |
| V144 | `research-tests/DGamma/R179O21CurrentBirthIdentityPositive.idr` | 2.102 | 2934736 | 50331648 | PASS |
| V145 | `research-tests/DGamma/R179O21WrongOriginalBirthNegative.idr` | 1.063 | 0 | 50331648 | PASS expected rejection |
| V150 | `research/DGamma/CP5AllSupportedMetadataSpike.idr` | 3.143 | 2947040 | 50331648 | PASS |
| V151 | `research/DGamma/CP5O19OpeningPropagationSpike.idr` | 2.097 | 1314928 | 50331648 | PASS |
| V152 | `research/DGamma/CP5O19ReplayObservationSpike.idr` | 3.135 | 2884976 | 50331648 | PASS |
| V153 | `research/DGamma/CP5O20GenerationOnlyHistorySpike.idr` | 3.145 | 3004432 | 50331648 | PASS |
| V154 | `research/DGamma/CP5O20RetainedClosingIndexSpike.idr` | 3.141 | 744768 | 50331648 | PASS |
| V155 | `research/DGamma/CP5O20SupportedInsertPositionSpike.idr` | 3.143 | 3012000 | 50331648 | PASS |
| V157 | `research/DGamma/CP5O19AdvanceObservationSpike.idr` | 3.130 | 2524528 | 50331648 | PASS |
| V158 | `research/DGamma/CP5O19CartesianCursorSpike.idr` | 2.096 | 677568 | 50331648 | PASS |
| V159 | `research/DGamma/CP5O19InsertObservationSpike.idr` | 2.103 | 1795888 | 50331648 | PASS |
| V160 | `research/DGamma/CP5SupportClauseTransportSpike.idr` | 3.148 | 3019296 | 50331648 | PASS |
| V162 | `research/DGamma/CP5AcceptedSupportTruthSpike.idr` | 2.101 | 624880 | 50331648 | PASS |
| V163 | `research/DGamma/CP5O19ActivationRowSpike.idr` | 3.149 | 2287328 | 50331648 | PASS |
| V164 | `research/DGamma/CP5O20SingleRoleAdvanceExtractionSpike.idr` | 2.102 | 1021424 | 50331648 | PASS |
| V165 | `research/DGamma/CP5O19SurfaceSpike.idr` | 4.189 | 1876208 | 50331648 | PASS |
| V166 | `research/DGamma/CP5O20SupportedBirthBridgeSpike.idr` | 3.150 | 2400912 | 50331648 | PASS |
| V167 | `research-tests/DGamma/R179O20SupportedBirthPositive.idr` | 2.091 | 2314912 | 50331648 | PASS |
| V168 | `research/DGamma/CP5O19OrdinalPlanSpike.idr` | 47.008 | 20469968 | 50331648 | PASS |
| V169 | `research/DGamma/CP5O20BirthBridgeRemainderSpike.idr` | 3.132 | 3006640 | 50331648 | PASS |
| V170 | `research/DGamma/CP5O20CanonicalOrdinalAttachmentSpike.idr` | 3.141 | 3006496 | 50331648 | PASS |
| V171 | `research/DGamma/CP5O20SupportedEndpointCapitalSpike.idr` | 3.144 | 641856 | 50331648 | PASS |
| V172 | `research/DGamma/CP5O19CartesianSitePlanSpike.idr` | 3.143 | 2886448 | 50331648 | PASS |
| V173 | `research/DGamma/CP5O20EpisodeSynchronizationSpike.idr` | 3.144 | 3004512 | 50331648 | PASS |
| V174 | `research/DGamma/CP5O20RootOrdinalBoundarySpike.idr` | 2.101 | 661248 | 50331648 | PASS |
| V175 | `research-tests/DGamma/R195RootOrdinalBoundaryPositive.idr` | 3.132 | 2472224 | 50331648 | PASS |
| V176 | `research/DGamma/CP5O19CartesianNumericSpike.idr` | 3.125 | 2891088 | 50331648 | PASS |
| V177 | `research/DGamma/CP5O20PairedPrefixProducerSpike.idr` | 3.139 | 3977168 | 50331648 | PASS |
| V178 | `research/DGamma/CP5O19GridCertificationSpike.idr` | 2.107 | 2081712 | 50331648 | PASS |
| V179 | `research/DGamma/CP5O20CanonicalPairSelectionSpike.idr` | 3.142 | 4104960 | 50331648 | PASS |
| V180 | `research-tests/DGamma/R188O19GridCertificationPositive.idr` | 2.110 | 2924160 | 50331648 | PASS |
| V181 | `research/DGamma/CP5O20BeginObservationSpike.idr` | 3.134 | 2884736 | 50331648 | PASS |
| V182 | `research/DGamma/CP5O19ResolvedOpeningRowSpike.idr` | 4.168 | 3002272 | 50331648 | PASS |
| V183 | `research/DGamma/CP5O19SourceShapeSpike.idr` | 3.137 | 3010816 | 50331648 | PASS |
| V184 | `research/DGamma/CP5O20AllNameSynchronizationSpike.idr` | 3.138 | 2942528 | 50331648 | PASS |
| V185 | `research/DGamma/CP5O20RightOpeningTransportSpike.idr` | 5.240 | 663520 | 50331648 | FAIL |
| V186 | `research/DGamma/CP5O19ActivationInsertionRowSpike.idr` | 4.185 | 2884960 | 50331648 | PASS |
| V187 | `research/DGamma/CP5O19ActivationResolutionSpike.idr` | 3.142 | 3905696 | 50331648 | PASS |
| V188 | `research/DGamma/CP5O20IndexedReloadingSourceSpike.idr` | 2.107 | 237440 | 50331648 | PASS |
| V189 | `research/DGamma/CP5O20SharedBeginAdapterSpike.idr` | 3.145 | 2944384 | 50331648 | PASS |
| V190 | `research/DGamma/CP5O20SupportedBridgeAssemblySpike.idr` | 3.137 | 3006480 | 50331648 | PASS |
| V191 | `research/DGamma/CP5O19BodyMetadataSpike.idr` | 4.179 | 2413840 | 50331648 | PASS |
| V192 | `research/DGamma/CP5O19InsertionInsertionRowSpike.idr` | 3.147 | 3002352 | 50331648 | PASS |
| V193 | `research/DGamma/CP5O20PairedAdvanceSpike.idr` | 3.140 | 2128000 | 50331648 | PASS |
| V194 | `research/DGamma/CP5O19CartesianInsertionSpike.idr` | 5.230 | 2996560 | 50331648 | PASS |
| V195 | `research/DGamma/CP5O19MixedActivationRowSpike.idr` | 4.174 | 2363008 | 50331648 | PASS |
| V196 | `research/DGamma/CP5O20NativeAdvanceAttachmentSpike.idr` | 3.144 | 2965280 | 50331648 | PASS |
| V197 | `research/DGamma/CP5O20PairedExecutionSpike.idr` | 3.140 | 2944864 | 50331648 | PASS |
| V198 | `research/DGamma/CP5O19MixedRowDispatcherSpike.idr` | 3.146 | 2279024 | 50331648 | PASS |
| V199 | `research/DGamma/CP5O19PairObservationSpike.idr` | 3.144 | 2404480 | 50331648 | PASS |
| V200 | `research/DGamma/CP5O20CanonicalPairedExtractionSpike.idr` | 3.139 | 3010736 | 50331648 | PASS |
| V201 | `research/DGamma/CP5O20PairedRemovalSpike.idr` | 2.111 | 257152 | 50331648 | PASS |
| V203 | `research/DGamma/CP5O19CartesianLengthSpike.idr` | 3.136 | 3004448 | 50331648 | PASS |
| V204 | `research/DGamma/CP5O19OriginalBlockClassSpike.idr` | 3.143 | 684464 | 50331648 | FAIL |
| V205 | `research/DGamma/CP5O20HistoryNameTransportSpike.idr` | 3.151 | 2941808 | 50331648 | PASS |
| V208 | `research/DGamma/CP5O19CartesianWordRowSpike.idr` | 5.221 | 3012800 | 50331648 | PASS |
| V210 | `research/DGamma/CP5O20EndpointRebaseBoundarySpike.idr` | 3.142 | 3022608 | 50331648 | PASS |
| V211 | `research/DGamma/CP5O20HistoryExecutionSpike.idr` | 3.141 | 3042992 | 50331648 | PASS |
| V216 | `research/DGamma/CP5O19CartesianColumnsSpike.idr` | 7.330 | 2428400 | 50331648 | PASS |
| V217 | `research/DGamma/CP5O20ActualHistoryAdvanceSpike.idr` | 3.137 | 745552 | 50331648 | PASS |
| V218 | `research/DGamma/CP5O20StampedHistoryFoldSpike.idr` | 3.144 | 2174368 | 50331648 | PASS |
| V220 | `research/DGamma/CP5O20OccurrenceStampedHistorySpike.idr` | 3.146 | 2938112 | 50331648 | PASS |
| V221 | `research/DGamma/CP5O20StampedOrdinalNecessitySpike.idr` | 2.101 | 275184 | 50331648 | PASS |
| V94-2 | `research-tests/DGamma/R171CoreHistoryCloneNegative.idr` | 1.064 | 0 | 50331648 | PASS expected rejection |
| V95-2 | `research-tests/DGamma/R171StepAccountingCloneNegative.idr` | 1.062 | 0 | 50331648 | PASS expected rejection |
| P3 | `package` | 15.639 | 230384 | 100663296 | PASS |

## Future policy

**SupportSolution200GiB**, accepted after unchanged-source S31-4 PASS160.765930GiB/986.351957s. Two samples free<15% or three successive Swapouts increases stop; compressor occupancy recorded only. Pre-unfreeze isolated peak UNKNOWN, no CP3 causation claim.

LocalDiamond52GiB; other research48GiB. Production CP3/CP3StatementChecks/CP4*64GiB except SupportSolution200GiB; other production48GiB. Package96GiB. Never silently raise guards.
