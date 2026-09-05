# O6 R162 — two-wall stop audit

## Scope and baseline

R162 ran on branch `cp5-thm73-scoping` from exact HEAD
`d66b2efb61cafea1c50984b09990d698c99251a0`.

The only retained proof-source change is in
`research/DGamma/CP5ConfluenceDeletionChainSpike.idr`. Production `src/`,
`dgamma.ipkg`, the frozen `deletionTheoremProof`, and the LocalDiamond research
module remain unchanged. The only pre-existing untracked paths remain `paper/`
and `review-o6-body-adversarial.md`.

The binding supervisor ruling for R162 required the selected-episode and
post-close fold outputs eventually to retain the **surviving-trace**
`RegistrationDiscipline`, and the final assembler to emit the target
`ReplayInvariantBundle`. Silent reuse of source discipline was prohibited. The
ruling authorized a constructor-owned certificate series (parent-yield
transport, child-retirement transport, then combined discipline preservation)
and required a stop after two genuine 3/3 compiler walls.

## Ratified capital

One copied `with` occurrence was removed by a producer-owned lifecycle view:

- `ScopedFiberLifecycleView` binds the concrete `MkFiber` spine and lifecycle;
- `scopedFiberLifecycleView` produces the exact view;
- `beginFiberTagScopedPostFoldAtLifecycle` performs the lifecycle cases; and
- `beginFiberTagScopedPostFold` now eliminates the view with `case` rather than
  `with (fiberLifecycle fiber)`.

The first formulation failed because an equality
`fiberLifecycle fiber = observed` did not expose the dependent `MkFiber` spine.
The second formulation made that spine constructor-owned and passed. It was
committed as:

```text
8f2725f research: eliminate copied lifecycle with
```

This commit is ratified R162 capital.

## Wall 1 — parent-yield transport (3/3, removed, spelling closed)

The attempted unit introduced a local reloading-control locator, a
`ScopedLocatedParentYieldControl` package, and a transport from
`FiberControlMaybeRelated` plus source `ParentRegistrationYield` to a target
`ParentRegistrationYield`. It was intended to keep all dependent component and
lifecycle indices under one constructor elimination. No version passed. The
entire unit was removed after attempt 3.

The following are the compiler diagnostics from the three attempts. Repeated
copies of the final unsolved-hole report emitted by Idris are represented once;
the diagnostic text itself is unchanged.

### Attempt 1/3

```text
Error: While processing type of scopedLocateParentYieldControl. Can't bind implicit DGamma.CP5ConfluenceDeletionChainSpike.{value:41149} of type ({arg:22545} : ?DGamma.CP5ConfluenceDeletionChainSpike.{key:41146}_[nameEq[3], parent[2], source[1], target[0]]) -> Type

DGamma.CP5ConfluenceDeletionChainSpike:3687:1--3695:40
 3687 | 0 scopedLocateParentYieldControl :
 3688 |   (nameEq : DecEq name) -> (parent : name) ->
 3689 |   (source, target : SystemState name key value world error) ->
 3690 |   FiberControlMaybeRelated
 3691 |     (lookupFiber @{nameEq} parent (registry source))
 3692 |     (lookupFiber @{nameEq} parent (registry target)) ->

Error: No type declaration for DGamma.CP5ConfluenceDeletionChainSpike.scopedLocateParentYieldControl.

DGamma.CP5ConfluenceDeletionChainSpike:3696:1--3710:60
 3696 | scopedLocateParentYieldControl nameEq parent source target related
 3697 |   (MkParentRegistrationYield sourceFiber sourceFound sourceStep
 3698 |     sourceContinuation sourceAccumulator sourceView parentAtYield
 3699 |     sourceBelongsToProgram parentRegistrationRank childRegistrationRank
 3700 |     parentRanked childRanked yieldTag stepYieldsTag catalogYieldsComponent) =
 3701 |       case replace
Did you mean any of: ScopedLocatedParentYieldControl, MkScopedLocatedParentYieldControl, LocatedParentYieldControl (not exported), MkLocatedParentYieldControl (not exported), or locateParentYieldControl (not exported)?

Error: While processing right hand side of scopedSealParentYieldControl. Name DGamma.CP5ConfluenceLocalDiamondSpike.LocatedReloadingControl is private.

DGamma.CP5ConfluenceDeletionChainSpike:3727:9--3740:78
 3727 |         case locateReloadingControl (sourceStep :: sourceContinuation)
 3728 |           sourceAccumulator sourceView sourceLifecycle targetLifecycle
 3729 |           parentAtYield lifecycleRelated of
 3730 |             MkLocatedReloadingControl targetAccumulator targetView
 3731 |               targetLifecycleIsReloading =>
 3732 |                 case targetLifecycleIsReloading of

Suggestion: add an explicit export or public export modifier. By default, all names are private in namespace blocks.

Error: While processing type of scopedTransportParentYield. Can't bind implicit DGamma.CP5ConfluenceDeletionChainSpike.{value:41298} of type ({arg:22545} : ?DGamma.CP5ConfluenceDeletionChainSpike.{key:41295}_[nameEq[3], parent[2], source[1], target[0]]) -> Type

DGamma.CP5ConfluenceDeletionChainSpike:3742:1--3749:71
 3742 | 0 scopedTransportParentYield :
 3743 |   (nameEq : DecEq name) -> (parent : name) ->
 3744 |   (source, target : SystemState name key value world error) ->
 3745 |   FiberControlMaybeRelated
 3746 |     (lookupFiber @{nameEq} parent (registry source))
 3747 |     (lookupFiber @{nameEq} parent (registry target)) ->

Error: While processing right hand side of scopedTransportParentYield. DGamma.CP5ConfluenceDeletionChainSpike.scopedSealParentYieldControl is not accessible in this context.

DGamma.CP5ConfluenceDeletionChainSpike:3751:3--3751:31
 3747 |     (lookupFiber @{nameEq} parent (registry target)) ->
 3748 |   ParentRegistrationYield protocol nameEq parent childComponent source ->
 3749 |   ParentRegistrationYield protocol nameEq parent childComponent target
 3750 | scopedTransportParentYield nameEq parent source target related sourceYield =
 3751 |   scopedSealParentYieldControl
          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Error: Unsolved holes:
DGamma.CP5ConfluenceDeletionChainSpike.{_:41353} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3750:28--3750:34
 3750 | scopedTransportParentYield nameEq parent source target related sourceYield =
                                   ^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{_:41356} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3750:35--3750:41
 3750 | scopedTransportParentYield nameEq parent source target related sourceYield =
                                          ^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{_:41359} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3750:42--3750:48
 3750 | scopedTransportParentYield nameEq parent source target related sourceYield =
                                                 ^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{_:41362} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3750:49--3750:55
 3750 | scopedTransportParentYield nameEq parent source target related sourceYield =
                                                        ^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{_:41365} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3750:56--3750:63
 3750 | scopedTransportParentYield nameEq parent source target related sourceYield =
                                                               ^^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{_:41368} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3750:64--3750:75
 3750 | scopedTransportParentYield nameEq parent source target related sourceYield =
                                                                       ^^^^^^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{_:41370} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3750:1--3752:85
 3750 | scopedTransportParentYield nameEq parent source target related sourceYield =
 3751 |   scopedSealParentYieldControl
 3752 |     (scopedLocateParentYieldControl nameEq parent source target related sourceYield)
```

### Attempt 2/3

This attempt added a local `ScopedLocatedReloadingControl`, corrected the
source-lookup replacement orientation, and made the outer type parameters
explicit. Idris still introduced the dependent `value` index implicitly and
selected the private LocalDiamond constructor because one constructor spelling
had not yet been renamed.

```text
Error: While processing type of scopedLocateParentYieldControl. Can't bind implicit DGamma.CP5ConfluenceDeletionChainSpike.{value:41419} of type ({arg:22545} : ?DGamma.CP5ConfluenceDeletionChainSpike.{key:41416}_[name[10], key[9], world[8], error[7], value[6], protocol[5], childComponent[4], nameEq[3], parent[2], source[1], target[0]]) -> Type

DGamma.CP5ConfluenceDeletionChainSpike:3721:1--3732:40
 3721 | 0 scopedLocateParentYieldControl :
 3722 |   {name, key, world, error : Type} -> {value : key -> Type} ->
 3723 |   {protocol : RegistrationProtocol key value world error} ->
 3724 |   {childComponent : Component key value world error} ->
 3725 |   (nameEq : DecEq name) -> (parent : name) ->
 3726 |   (source, target : SystemState name key value world error) ->

Error: No type declaration for DGamma.CP5ConfluenceDeletionChainSpike.scopedLocateParentYieldControl.

DGamma.CP5ConfluenceDeletionChainSpike:3733:1--3747:60
 3733 | scopedLocateParentYieldControl nameEq parent source target related
 3734 |   (MkParentRegistrationYield sourceFiber sourceFound sourceStep
 3735 |     sourceContinuation sourceAccumulator sourceView parentAtYield
 3736 |     sourceBelongsToProgram parentRegistrationRank childRegistrationRank
 3737 |     parentRanked childRanked yieldTag stepYieldsTag catalogYieldsComponent) =
Did you mean any of: ScopedLocatedParentYieldControl, MkScopedLocatedParentYieldControl, scopedLocateReloadingControl, LocatedParentYieldControl (not exported), MkLocatedParentYieldControl (not exported), or locateParentYieldControl (not exported)?

Error: While processing right hand side of scopedSealParentYieldControl. Name DGamma.CP5ConfluenceLocalDiamondSpike.LocatedReloadingControl is private.

DGamma.CP5ConfluenceDeletionChainSpike:3764:9--3777:78
 3764 |         case scopedLocateReloadingControl (sourceStep :: sourceContinuation)
 3765 |           sourceAccumulator sourceView sourceLifecycle targetLifecycle
 3766 |           parentAtYield lifecycleRelated of
 3767 |             MkLocatedReloadingControl targetAccumulator targetView
 3768 |               targetLifecycleIsReloading =>
 3769 |                 case targetLifecycleIsReloading of

Suggestion: add an explicit export or public export modifier. By default, all names are private in namespace blocks.

Error: While processing type of scopedTransportParentYield. Can't bind implicit DGamma.CP5ConfluenceDeletionChainSpike.{value:41590} of type ({arg:22545} : ?DGamma.CP5ConfluenceDeletionChainSpike.{key:41587}_[name[10], key[9], world[8], error[7], value[6], protocol[5], childComponent[4], nameEq[3], parent[2], source[1], target[0]]) -> Type

DGamma.CP5ConfluenceDeletionChainSpike:3779:1--3789:71
 3779 | 0 scopedTransportParentYield :
 3780 |   {name, key, world, error : Type} -> {value : key -> Type} ->
 3781 |   {protocol : RegistrationProtocol key value world error} ->
 3782 |   {childComponent : Component key value world error} ->
 3783 |   (nameEq : DecEq name) -> (parent : name) ->
 3784 |   (source, target : SystemState name key value world error) ->

Error: While processing right hand side of scopedTransportParentYield. DGamma.CP5ConfluenceDeletionChainSpike.scopedSealParentYieldControl is not accessible in this context.

DGamma.CP5ConfluenceDeletionChainSpike:3791:3--3791:31
 3787 |     (lookupFiber @{nameEq} parent (registry target)) ->
 3788 |   ParentRegistrationYield protocol nameEq parent childComponent source ->
 3789 |   ParentRegistrationYield protocol nameEq parent childComponent target
 3790 | scopedTransportParentYield nameEq parent source target related sourceYield =
 3791 |   scopedSealParentYieldControl
          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

### Attempt 3/3

This attempt renamed the remaining constructor and changed all outer binders to
explicit arguments. The dependent `value` index remained unbindable before the
body could elaborate.

```text
Error: While processing type of scopedLocateParentYieldControl. Can't bind implicit DGamma.CP5ConfluenceDeletionChainSpike.{value:41419} of type ({arg:22545} : ?DGamma.CP5ConfluenceDeletionChainSpike.{key:41416}_[name[10], key[9], world[8], error[7], value[6], protocol[5], childComponent[4], nameEq[3], parent[2], source[1], target[0]]) -> Type

DGamma.CP5ConfluenceDeletionChainSpike:3721:1--3732:40
 3721 | 0 scopedLocateParentYieldControl :
 3722 |   (name, key, world, error : Type) -> (value : key -> Type) ->
 3723 |   (protocol : RegistrationProtocol key value world error) ->
 3724 |   (childComponent : Component key value world error) ->
 3725 |   (nameEq : DecEq name) -> (parent : name) ->
 3726 |   (source, target : SystemState name key value world error) ->

Error: No type declaration for DGamma.CP5ConfluenceDeletionChainSpike.scopedLocateParentYieldControl.

DGamma.CP5ConfluenceDeletionChainSpike:3733:1--3748:60
 3733 | scopedLocateParentYieldControl name key world error value protocol
 3734 |   childComponent nameEq parent source target related
 3735 |   (MkParentRegistrationYield sourceFiber sourceFound sourceStep
 3736 |     sourceContinuation sourceAccumulator sourceView parentAtYield
 3737 |     sourceBelongsToProgram parentRegistrationRank childRegistrationRank
 3738 |     parentRanked childRanked yieldTag stepYieldsTag catalogYieldsComponent) =
Did you mean any of: ScopedLocatedParentYieldControl, MkScopedLocatedParentYieldControl, scopedLocateReloadingControl, LocatedParentYieldControl (not exported), MkLocatedParentYieldControl (not exported), or locateParentYieldControl (not exported)?

Error: While processing type of scopedTransportParentYield. Can't bind implicit DGamma.CP5ConfluenceDeletionChainSpike.{value:41834} of type ({arg:22545} : ?DGamma.CP5ConfluenceDeletionChainSpike.{key:41831}_[name[10], key[9], world[8], error[7], value[6], protocol[5], childComponent[4], nameEq[3], parent[2], source[1], target[0]]) -> Type

DGamma.CP5ConfluenceDeletionChainSpike:3780:1--3790:71
 3780 | 0 scopedTransportParentYield :
 3781 |   (name, key, world, error : Type) -> (value : key -> Type) ->
 3782 |   (protocol : RegistrationProtocol key value world error) ->
 3783 |   (childComponent : Component key value world error) ->
 3784 |   (nameEq : DecEq name) -> (parent : name) ->
 3785 |   (source, target : SystemState name key value world error) ->

Error: While processing right hand side of scopedTransportParentYield. DGamma.CP5ConfluenceDeletionChainSpike.scopedSealParentYieldControl is not accessible in this context.

DGamma.CP5ConfluenceDeletionChainSpike:3793:5--3793:33
 3789 |   ParentRegistrationYield protocol nameEq parent childComponent source ->
 3790 |   ParentRegistrationYield protocol nameEq parent childComponent target
 3791 | scopedTransportParentYield name key world error value protocol childComponent
 3792 |   nameEq parent source target related sourceYield =
 3793 |     scopedSealParentYieldControl
            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Error: Unsolved holes:
DGamma.CP5ConfluenceDeletionChainSpike.{_:41886} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3791:28--3791:32
 3791 | scopedTransportParentYield name key world error value protocol childComponent
                                   ^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{_:41889} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3791:33--3791:36
 3791 | scopedTransportParentYield name key world error value protocol childComponent
                                        ^^^
DGamma.CP5ConfluenceDeletionChainSpike.{_:41892} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3791:37--3791:42
 3791 | scopedTransportParentYield name key world error value protocol childComponent
                                            ^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{_:41895} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3791:43--3791:48
 3791 | scopedTransportParentYield name key world error value protocol childComponent
                                                  ^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{_:41898} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3791:49--3791:54
 3791 | scopedTransportParentYield name key world error value protocol childComponent
                                                        ^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{_:41901} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3791:55--3791:63
 3791 | scopedTransportParentYield name key world error value protocol childComponent
                                                              ^^^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{_:41904} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3791:64--3791:78
 3791 | scopedTransportParentYield name key world error value protocol childComponent
                                                                       ^^^^^^^^^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{_:41907} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3792:3--3792:9
 3792 |   nameEq parent source target related sourceYield =
          ^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{_:41910} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3792:10--3792:16
 3792 |   nameEq parent source target related sourceYield =
                 ^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{_:41913} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3792:17--3792:23
 3792 |   nameEq parent source target related sourceYield =
                        ^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{_:41916} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3792:24--3792:30
 3792 |   nameEq parent source target related sourceYield =
                               ^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{_:41919} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3792:31--3792:38
 3792 |   nameEq parent source target related sourceYield =
                                      ^^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{_:41922} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3792:39--3792:50
 3792 |   nameEq parent source target related sourceYield =
                                              ^^^^^^^^^^^
DGamma.CP5ConfluenceDeletionChainSpike.{_:41924} introduced at:
DGamma.CP5ConfluenceDeletionChainSpike:3791:1--3795:72
 3791 | scopedTransportParentYield name key world error value protocol childComponent
 3792 |   nameEq parent source target related sourceYield =
 3793 |     scopedSealParentYieldControl
 3794 |       (scopedLocateParentYieldControl name key world error value protocol
 3795 |         childComponent nameEq parent source target related sourceYield)
```

### Fresh-eyes note for wall 1

The failure happens while elaborating the *type*, before the intended
single-constructor body can help. A fresh model should avoid repeating these
signatures. Likely alternatives are a fully saturated record indexed by all
five universe parameters, or a target-yield result record whose constructor
owns the target lookup and which never mentions bare `FiberControlMaybeRelated`
in a top-level function type.

## Wall 2 — targetFiber `with` cleanup (3/3, removed, spelling closed)

After the lifecycle-view cleanup passed, the remaining nested
`with (targetFiber ... (registry state))` was rotated to a
`ScopedTargetFiberView` carrying the exact result equation. The attempted unit
was removed after attempt 3; the original nested `with` remains in the retained
source.

### Attempt 1/3

```text
Error: While processing constructor MkScopedTargetFiberView. Can't find an implementation for DecEq ?name.

DGamma.CP5ConfluenceDeletionChainSpike:15597:16--15597:40
 15593 |   (source : Registry name key value world error) -> Type where
 15594 |   MkScopedTargetFiberView :
 15595 |     (observed : Maybe (View name
 15596 |       (dependencies (componentDependencies (fiberComponent fiber))))) ->
 15597 |     (0 exact : targetFiber fiber source = observed) ->
                        ^^^^^^^^^^^^^^^^^^^^^^^^

Error: While processing right hand side of scopedTargetFiberView. Undefined name MkScopedTargetFiberView.

DGamma.CP5ConfluenceDeletionChainSpike:15605:3--15605:26
 15601 |   (fiber : Fiber name key value world error) ->
 15602 |   (source : Registry name key value world error) ->
 15603 |   ScopedTargetFiberView fiber source
 15604 | scopedTargetFiberView fiber source =
 15605 |   MkScopedTargetFiberView (targetFiber fiber source) Refl
           ^^^^^^^^^^^^^^^^^^^^^^^
Did you mean any of: ScopedTargetFiberView, or scopedTargetFiberView?

Error: While processing right hand side of beginFiberTagScopedPostFoldAtLifecycle. Undefined name MkScopedTargetFiberView.

DGamma.CP5ConfluenceDeletionChainSpike:15625:9--15625:32
 15621 |   retiredFlag table (Inactive Nothing) state afterState tag equation =
 15622 |     case scopedTargetFiberView
 15623 |       (MkFiber component parent retiredFlag table (Inactive Nothing))
 15624 |       (registry state) of
 15625 |         MkScopedTargetFiberView Nothing exact => case exact of
                 ^^^^^^^^^^^^^^^^^^^^^^^
Did you mean any of: ScopedTargetFiberView, or scopedTargetFiberView?
```

### Attempt 2/3

This attempt added the explicit `DecEq name` dictionary.

```text
Error: While processing constructor MkScopedTargetFiberView. Can't find an implementation for DecEq ?key.

DGamma.CP5ConfluenceDeletionChainSpike:15598:16--15598:50
 15594 |   (source : Registry name key value world error) -> Type where
 15595 |   MkScopedTargetFiberView :
 15596 |     (observed : Maybe (View name
 15597 |       (dependencies (componentDependencies (fiberComponent fiber))))) ->
 15598 |     (0 exact : targetFiber @{nameEq} fiber source = observed) ->
                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Error: While processing right hand side of scopedTargetFiberView. Undefined name MkScopedTargetFiberView.

DGamma.CP5ConfluenceDeletionChainSpike:15607:3--15607:26
 15603 |   (fiber : Fiber name key value world error) ->
 15604 |   (source : Registry name key value world error) ->
 15605 |   ScopedTargetFiberView nameEq fiber source
 15606 | scopedTargetFiberView nameEq fiber source =
 15607 |   MkScopedTargetFiberView (targetFiber @{nameEq} fiber source) Refl
           ^^^^^^^^^^^^^^^^^^^^^^^
Did you mean any of: ScopedTargetFiberView, or scopedTargetFiberView?

Error: While processing right hand side of beginFiberTagScopedPostFoldAtLifecycle. Undefined name MkScopedTargetFiberView.

DGamma.CP5ConfluenceDeletionChainSpike:15627:9--15627:32
 15623 |   retiredFlag table (Inactive Nothing) state afterState tag equation =
 15624 |     case scopedTargetFiberView nameEq
 15625 |       (MkFiber component parent retiredFlag table (Inactive Nothing))
 15626 |       (registry state) of
 15627 |         MkScopedTargetFiberView Nothing exact => case exact of
                 ^^^^^^^^^^^^^^^^^^^^^^^
Did you mean any of: ScopedTargetFiberView, or scopedTargetFiberView?
```

### Attempt 3/3

This attempt supplied both dictionaries explicitly. The producer view then
elaborated, but eliminating its exact equation did not refine the existential
`tag` in the successful branch.

```text
Error: While processing right hand side of beginFiberTagScopedPostFoldAtLifecycle. When unifying:
    LBeginTag = LBeginTag
and:
    tag = LBeginTag
Mismatch between: LBeginTag and tag.

DGamma.CP5ConfluenceDeletionChainSpike:15631:58--15631:62
 15627 |       (registry state) of
 15628 |         MkScopedTargetFiberView Nothing exact => case exact of
 15629 |           Refl => void (nothingNotJustScopedPostFold equation)
 15630 |         MkScopedTargetFiberView (Just view) exact => case exact of
 15631 |           Refl => case justInjective equation of Refl => Refl
                                                                  ^^^^
```

### Fresh-eyes note for wall 2

Do not repeat the result-only `ScopedTargetFiberView`. A promising different
shape would make the successful constructor own `tag = LBeginTag` directly,
produced by destructing the entire `beginFiberAction` result rather than only
`targetFiber`; alternatively expose a named begin-success result indexed by the
full `Maybe (RuleTag, SystemState)`.

## Unopened obligations after the stop

Per the two-wall ruling, no further proof edits were attempted:

- surviving-trace discipline retention in
  `ScopedSelectedClosedEpisodeFoldOutput` and
  `ScopedPostCloseSuffixFoldOutput` remains pending;
- child-retirement transport and combined discipline preservation remain
  pending;
- the stopped readiness-to-subsequence dependent converter remains pending;
- four copied `with` occurrences remain in the R161 copied seam (the nested
  `targetFiber`, selected lookup, generation-owned decision, and owner equality
  decision);
- O9 `enrichDeletionChainStepSpike`, O10
  `deleteClosingEpisodesCoreSpike`, and O11
  `assembleClosingFreeAccountingSpike` remain unopened in R162.

No source-discipline fallback, scoped-to-raw cast, `believe_me`, `assert_total`,
postulate, partiality marker, new proof hole, or production API change was
retained.

## Gate checks

All checks were run sequentially with no concurrent Idris process.

```text
Idris 2, version 0.8.0

DeletionChain direct check after deleting its TTC/TTM:
  3/3: Building DGamma.CP5ConfluenceDeletionChainSpike
  exit 0 each time

R11DeletionCertificateProjectionPositive after deleting its TTC/TTM:
  1/1: Building DGamma.R11DeletionCertificateProjectionPositive
  exit 0

R11DirectDeletionStepCloneNegative after deleting its TTC/TTM:
  compiler exit 1
  intended diagnostics present:
    cloneDeletionStepWithAlternateMap
    occurrences and alternate

seeded production package closure:
  dgamma.ipkg module census: 207/207
  idris2 --build dgamma.ipkg
  exit 0

src/DGamma/CP3.idr blob:
  2c697e532e83989de8591fa6a4378747c6a501c0

dgamma.ipkg blob:
  da0c007ee08c4648e459296eb6f0e72a40e2ac89

DeletionChain research blob at ratified proof commit 8f2725f:
  6fb1e962b7568a4c410e8b55219c28371929dc6b

LocalDiamond research blob:
  6ad84aad7a439b0c9ee57e22bf67b97f91833d60

production diff from 34b21c9 over src/ + dgamma.ipkg:
  empty (git diff --quiet exit 0)

LocalDiamond diff from R162 start d66b2ef:
  empty (git diff --quiet exit 0)

git diff --check:
  exit 0
```

The research hole census at the stop is 8:

```text
CanonicalSort 2 / CrossTrace 3 / DeletionChain 3 /
LocalDiamond 0 / RenamingComposition 0
```

The three DeletionChain holes remain exactly O9/O10/O11. No new holes were
introduced.

## Gate verdict

**SAFE TWO-WALL STOP at ratified proof boundary `8f2725f`.** The first copied
lifecycle `with` cleanup is checked and retained. Both authorized 3/3 walls are
fully removed and their spellings are closed. Producer-owned surviving-trace
discipline/bundle enrichment is not complete, so O9/O10/O11 were correctly not
opened. The next worker should use a different model family and different
certificate shapes, starting from the exact diagnostics above rather than
retrying either closed spelling.
