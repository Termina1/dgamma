# R200 owner FINAL gate — checked PARTIAL; reviewer decision required

Prepared 2026-09-09T15:00:12.659795+00:00 after D3
`9be579adb36d46e4eb118faeb4b2330a716709a9`. D4 is the artifact-only sealing commit following this file.
This document does NOT claim independent human reviewer acceptance.

## B —24/24 PASS1, not global coverage

The actual closing-free accepted scanner base has this CHECKED type:

```idris
0 o20ClosingFreeDiscardedEmpty :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  AlignedTransitions name key world error value nameEq keyEq left ->
  (bindings (registry leftFirst) = []) ->
  NoClosingEpisodes name key world error value nameEq keyEq left ->
  (leftDeletedGenerations registrations = [])
```

`o20AcceptedDiscardedBirthClassified` additionally produces the exact original
birth and a real later parent Unload from every accepted discarded membership.
`o20UnselectedVestigialStillPresent` produces target lookup presence at an
actual nonselecting DeletionChainStep, with accepted/native current tables
reconciled. R193/R195 eight-edge full vestigial fixture authenticates these
base and reverse-scanner results; the inherited first-selected fixture also
freshly rechecked (V127). No independent canonical capital is fabricated.

First missing lemma: **o20DeletionRetainedClosingBirth**. It must transport a
real deleted-birth classification through an actual nonselecting deletion in
`generationForward (deletionProducerGenerationRenaming
(deletionProducerCapital step))` coordinates, retaining a REAL later parent
Unload. Current control/presence preservation is NOT this historical output.
This lemma is neither defined nor claimed checked. A prospective lean route
is induction on the native deleted-birth classification, using the real
closing-free Unload contradiction at the end, rather than assuming a whole
new bilateral vestigial packet; the transport telescope still needs validation.

Requested `everyPresentVestigialSelected` in the ACTUAL
`closingFreeDeletionGenerations` (head selections plus backward-rebased tail)
remains OPEN. Supported-class R194 agreement and removed-class R198 absences
remain existing capital, not a new universal rebase. Present-unsupported cases
still lack both-side some-node coverage. No universal O20AllNameCut or D5
`o20SupportedBridgeFromOwnedCut`/ReplayedCanonicalEndpointBridge producer is
claimed. No scoped-to-raw cast, frozen deletion theorem or selector-body change.

## A —20/20 PASS1, residual elimination CLOSED, synchronization OPEN

`o20LocatedBlockEndRemainderEmpty` universally derives actual aligned block-end
emptiness from that block's final Active and actual no-later-lifecycle suffix.
The proof traverses own Insert/Retire/Remove and foreign actions. All THREE
actual R191 blocks instantiate it, including nonempty suffixes (V164).
`o20SelectedCanonicalRoleWords` removes both R199 remainders and proves PLAIN
lifecycle words under accepted selected-pair capital (V165).

`o20SupportedCanonicalInsertPositions` retains both authentic ORIGINAL scanned
Insert occurrences, exact mapped stamp and per-activation position equality
for originally-supported canonical births. Those are NOT physical canonical
positions. Their actual exchanged-trace attachment, physical Insert pairing,
real one-sided skip witnesses and whole orchestration-order histories are open.
`o20SynchronizeCanonicalHistoriesModulo` remains OPEN, not merely body-hidden.
R191/R193/R195 native/cut/boundary fixtures all appear in the full validation.

## C and D

C0/ineligible: both A and B remain producer-incomplete, so no convergence-body
attempt. D1 authorized comment correction; D2 docs/plan; D3 full archive/ledger
publication; D4 final clean gate. No re-budget or exhausted-statement retry.
44 declarations=42 proof functions+2 indexed families, all PASS1 and immediately
GUARDED COMMIT-committed.45 source receipts include the sole comment-only edit.
Every artifact commit also uses the authenticated latest native PASS; D3/D4
anchor to V166, with no intervening compiler invocation. Complete micro-unit
SHA/commit receipts: O6-R200-MICRO-UNITS.md and the archive/live verification.

## Required source and validation evidence

- Full final scope: ALL157 inherited R199+8 new=165 sources plus seeded
  package166 checks; seven exact diagnostic+symbol expected negatives;
  no inherited path exclusion. All166 expected outcomes PASS at14:53:22Z.
- Whole shift:212/212 expected outcomes, zero rejected invocations; no
  interruption, source mutation or resource stop. Evidence tests21+7 PASS.
- Source/log/receipt/plan/frozen/resource machine verification and all1086
  archive files authenticate. Machine authentication is NOT human review.
- Production diff vs34b21c9 EMPTY; CP3 blob2c697e532e83989de8591fa6a4378747c6a501c0.
  Census4=1/2/0/0/1, no new holes/escapes. All protected whole modules unchanged.
- Adjacent suffix1470 bytes SHA256
  2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf;
  statement1154 bytes SHA256
  3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf.
  O19 body1286 bytes SHA256
  cbd0954303c35141af0309e515bdb9e98e988e7c23be70b9764d8c1ce18fd396.
- LocalDiamond SHA2569f9216170853624cff30449696f2540da0ed48e0b42504533aa587cb70dfc037;
  DeletionChain SHA25691e8fd290cc4fedae9656ce5b4ae3ea0b38509f6e0250f51b4a7aa2aea09067b.
  Bridge3243 bytes SHA256ac5304c1a6a6e0cea988eac4b0dcdb5756fcf1b67ede7d0db6a4d723c73b695d,
  exactly the R192 A11 manifest. Other hashes in O6-R200-FROZEN-AUDIT.json.
- Comment-only P2 helper change: before
  ee4f73c2427bdca5b34e266710660c8a0c3daa9c6a5283f00c3c0dc59aa4152c;
  after550fa9472bdf9b1366d59e8417ee26821e4d61fd2a1b926ea40857c1124b9315.
  D1-COMMENT own-target PASS4.174s/4,253,664KiB; V122 fresh PASS4.164s.
  Exact non-doc identity: helper consumes actual result, produces reconciliation
  and absence; chain construction-owned result claim unchanged.
- One compiler in main at a time; no lock paths or lane-2 worktree access.
  LocalDiamond sampled50,540,832KiB/52GiB; UniqueOrdinal44,809,632KiB/48GiB;
  all others under48GiB.13 zero captures mean no live sample, not zero peak.
  153 overlap invocations/1468 timestamps only in O6-R200-RESOURCE-AUDIT.json;
  no foreign commands or compiler signals are logged/issued.
- 165 sources is not all274 inventory entries;111 remain NOT rechecked. Seeded
  package PASS46.974s/no Building lines is not a cold/207-fresh-module claim.
- Post-D3 live verification reports tracked tree clean, nothing staged, only
  permitted paper/ and review-o6-body-adversarial.md untracked. D4 changes only
  gate/documentation artifacts; a final read-only clean check follows its commit.

## Archive anchor and decision boundary

Archive SHA256 `e14a7c174edd9e086f1e92da4f7e4063e7191ecda17e411caafebf8391834d9f`; anchor
`63011ee17572018ce36b4a505d062135b5e9697c` deliberately precedes D3 and D4.
Its45 source receipts and2 earlier artifact receipts are not augmented with
future publication/gate receipts. Post-D3 live verification authenticates the
D3 receipt separately; the final live verification covers D4 likewise.

**Requested decision: accept this checked PARTIAL R200 milestone, subject to
independent reviewer findings, without claiming A/B/C theorem completion.**
Any next proof attempts require the next owner-granted budget; none is started
by this gate. Source status and next semantic work are in NOTES.md Status.
