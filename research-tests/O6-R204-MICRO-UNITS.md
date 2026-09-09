# R204 micro-unit ledger

Caps Unit0<=2, B<=14, A<=16, C<=6, D<=4. B14/15 invocations; A16/20 proof invocations (15 retained, A15 full-revert).29 retained new declarations + one body-only P1 source repair.35 A/B proof checks =30 PASS+5 failures; one PASS (A3-2) superseded by rstrip-only. Unit0a2 checks =1 PASS+1 failure. V0-CACHE1 authorized unchanged-source validation PASS. Pre-final total38 =32 PASS+6 failures. No cap extension.

## R203 review disposition

The R203 milestone is ratified by the supervisor AFTER these two repairs land. Both landed before B1: P1 `af2df90b`, P2 `c254d5a1`. This fulfilled repair condition is not a claim of A/B/D5/theorem closure.

| Unit | Attempt | Outcome | Source SHA256 | Guarded source commit |
|---|---:|---|---|---|
| U0a | 1 | FAIL (retained evidence) | `2e5d42b60c32c939cbd736a1844822a2d1d021cc372470902ff5de35a337347c` | `none` |
| U0a | 2 | PASS | `6946cbd30558b3013a418e0d3cb7ff85ef3698e3e7cd6555545079df6b596618` | `af2df90b1b5c870c6535b67dc62ee53d506bc387` |
| B1 | 1 | PASS | `fa86086f15bd8b653fdf1d36536e6feb6dd89ca64ec4dfc1358ea4bd9ae30eb9` | `057fef482ccf09e7437dea42d55c53f8462b774e` |
| B2 | 1 | PASS | `e0a1cbc12dc9f427f1199e166fb5b1cf997396d2b85cbd502fdf1d6849461f8d` | `21baa286528bf8a79fb81835d307434d53e01831` |
| B3 | 1 | PASS | `4536da0b175e4734a023ceaa3a306fca882e5671d38f38c349f84910aed87daa` | `1a4541d11c9187f4316e9b1dbd5dc97367511824` |
| B4 | 1 | FAIL (retained evidence) | `96a457b3487c05b124829e9459e5c22f20a16dd738c31571ae17bda8da6249e4` | `none` |
| B4 | 2 | PASS | `fff45956c505f2de2117b87b7ee7bd60d6f75bd6f603374a7f9e2c6dd27ce445` | `80809f4477c81d800796b713231f7d398b0bb87e` |
| B5 | 1 | PASS | `6e0b0ae3a1d250c7c1a7978a0d1510f647af9b413dd3823017d6d9034e9b7cea` | `7255d9240e2e86da5448e7eb3aa6980acb55517f` |
| B6 | 1 | PASS | `7b6824611ab39a9bb76861a534133cc24d6871b344fb79ae2729ea49e0c3fcb2` | `27fdc24566a02a4a31be387ed62422a2bd4e4370` |
| B7 | 1 | PASS | `f63e097b13be9cb8910012a554a3a6e6e3962c63747b0011feb906cb51f92fc2` | `b28049972ec026c4523734fa22e289c2e1702d64` |
| B8 | 1 | PASS | `1a595d3f00ed75ab3b21ef21dd14242c27c3c0f42c67bbcd14d7fa56569207d7` | `f5f5dd9c47db6d76f9ced7dde7bf0ae0ffd14495` |
| B9 | 1 | PASS | `5426587a3c6fba44da870df1a7dc936a6aa0b041609ab793084408b34fc70f54` | `42519bacaef50d7370c0c9e1fee95bf4fc73c856` |
| B10 | 1 | PASS | `15c970ef751fea2c11d5e3002acd15d1d2562bf5b9687ff4c8eacd66a17a0a0a` | `8f1c9506b3d35185d0349ecc95c6dbb8b7e595b0` |
| B11 | 1 | PASS | `11c08681d78e868a8c1179e1607c9972cda5abf7700a3a700bde103a7999d1fe` | `691d3c2d197bd8425ff2aba5ed7548bc3db90ed7` |
| B12 | 1 | PASS | `e510dea99a3e6697b2efbf2b9e93a562cd0ab7c7c60d7223d38cb53cccf5f79b` | `f1aad2a6eca988df4a14e183e0a8088369dba7ea` |
| B13 | 1 | PASS | `77e6702e8a192ed683c26f4dcac5e9f9dca33fac4ebbec12c9768192787a091d` | `d972a3e105c04f80991919a841ac3cfd56e2e6ce` |
| B14 | 1 | PASS | `2dd198856223b3201519122a6b56bf3fb7844894f881c62bc088fb842e314093` | `b1945d43a84af0b9090b12ff610ed1b18cc80292` |
| A1 | 1 | PASS | `74e233f50aa42270b91535faffa65a7515a5001f0d4bbd73ca38de6245f04cb8` | `0a2961cc590cbda57f614684a88b6351b461a0f0` |
| A2 | 1 | PASS | `42cfcbc80ff255c23be423e12dcda9449e46b5d1452372178db0395b1a8274df` | `d7daff323c910cc568b1d4ed6df6da5d6a9dbb84` |
| A3 | 1 | FAIL (retained evidence) | `f81e0abd22294c83db758e36dc411641e42328779f559e69810fc0066cc7d75b` | `none` |
| A3 | 2 | PASS (rstrip-only superseded) | `a4d6b5445c043a32dd958f1290e1ff3236f67dbb6a163b49653220038033aa5c` | `none` |
| A3 | 3 | PASS | `dbaa5c0bddb0856478b07f68dc2039de746fb3e5c2a96970f6492814c8965ca2` | `9d47d2a974c7e6608f71f34a85cdb64d852a872d` |
| A4 | 1 | PASS | `36734ed8c3aab543d1099a160e76587467bd4e882d521c6fb6e12912c83b4d5a` | `6c7c039677a82e60aee8f00ef63f74e5d4c0ea23` |
| A5 | 1 | PASS | `c030193086272fcfd3ff5865c38b7c3d15acdd5cb524c84232ac54eda458166d` | `f8aab32b677f39df9bf273c0072c5565c5e8a0e7` |
| A6 | 1 | PASS | `644ebd3528147a8516e24a6e2d33a58aecc4501fd62e5bc44e6c3a0d86352d52` | `cb2289d406be6040312513369befd22059b8e014` |
| A7 | 1 | PASS | `01a5ceaba4c2e78e49c3d11bd696c5459f5021abaa32e57e355a4990472f572a` | `a50b8d1b264fcecf78887f432936b6b0c05d1af9` |
| A8 | 1 | PASS | `3c928e581c65dabf7a15b49e0dc2ba9b6004a46d69efd4c4f9f579c13e482677` | `413092e5026fddfba8ffa1919c3b7fad083311e1` |
| A9 | 1 | PASS | `54b1196cabf00d8a7540419aae993f8560c2d35149f2ed976ccf3689ffa0d842` | `879ae52670b5a7ca90d80b97af50b1f921010f95` |
| A10 | 1 | PASS | `182de8834e478833eb0751a7ec6efb05ad712326289772f021b88879c10658c6` | `d4f72fe7dc74c98cf699689a5089b760a13842d4` |
| A11 | 1 | PASS | `f7a8d52842fc49d449e76602f33b54971f2d877540d4cfaefd63da6bb58b5da1` | `6b100142cb9c09f82d7539c840d0d48dff3b6070` |
| A12 | 1 | PASS | `f948cd9c2d80f2da360dd1eca622c456fa7707c5ad80910ba62843edb405eb2e` | `9e9f5ba2f075d96041a87119a31b15947d527b8b` |
| A13 | 1 | PASS | `1eac9052e41e51e7a98fe7889624728c82cd397edd135b53146419bf32f2db06` | `1a61f16f43370449c854265f45bc0388d3faf388` |
| A14 | 1 | PASS | `5967fa8438bee25461153e53b1379d1e6e7dc01995ebfddbaaa232d3a0acb183` | `d37e8d551545317101e2aa249d047d44d713447e` |
| A15 | 1 | FAIL (retained evidence) | `19bd68a5bd4110ee77d7d4e77a7f37821cdd1b4688471bd443de51cca716d3bc` | `none` |
| A15 | 2 | FAIL (retained evidence) | `79ac5229721943465d06a66a69c2f13c952b4d330fba998d5ecd0d22cb146c9c` | `none` |
| A15 | 3 | FAIL (retained evidence) | `c30b52aef98015b737964dd76229deb9a4f73bbd2913a50b3606caac0cd6a3d9` | `none` |
| V0 | CACHE | PASS (authorized cache validation) | `5967fa8438bee25461153e53b1379d1e6e7dc01995ebfddbaaa232d3a0acb183` | `none` |
| A16 | 1 | PASS | `8fda11ccd281eed876d83849734d79059c63e54dde9946182866699dacb71b87` | `3e6d8ff0f539ecb0425fc19b496995b4a97d6e67` |

## Failed attempts and receipts

- U0a-1: naked inlining loses the former filtered alias type, True vs isLifecycleAction metavariable. U0a-2 explicitly supervisor-authorized inline `the` annotations, same statement/type, single own Building, P1 required receipt.
- B4-1: private uniqueInsertionsAfterDeletionStep inaccessible; B4-2 uses exported uniqueInsertionsAfterDeletionDerivation on the actual singleton deletion.
- A3-1: parse error in generated proof text. A3-2 fresh PASS but guard rejected EOF blank line; A3-3 exact rstrip-only repair fresh PASS and guarded commit. Failure guards stopped following commands; no unreceipted source commit.
- A15-1/2: two-path literal native projection append equality stuck at End; A15-2 verified/reordered direct imports and used --show-implicits. A15-3 narrowed to LEFT-only and also stuck. STOP3/3, full byte-exact revert to d37e8d55; both statements EXHAUSTED. No fourth/renamed proof retry.
- V0-CACHE: supervisor expressly authorized separate unchanged-source validation of restored SHA5967fa84…; one own Building, PASS, before A16. No source timestamp manipulation; no A16 budget charge.

## Disposition by unit

- 0:2/2 units complete. Both required repairs guarded-committed; R203 A13 structural where rightHistory untouched.
- B:14/14 cap; actual-chain present-vestigial adapter/disappearance and current-present count/name rebase PROVED. O20AllNameCut full controls/absent-domain transport OPEN; D5 unattempted.
- A:16/16 cap;15 retained declarations; conditional original-event runtime histories PROVED. Canonical transport, predecessor cut, actual skips, whole-history fold and synchronization OPEN. A15 fully reverted; no borrowing from B/C/D.
- C:0/6, INELIGIBLE; body and statements unchanged, census4=1/2/0/0/1.
- D1: source freeze, repair hashes, compiler-free contracts, immutable ALL181+8+package plan, final-validation tools. D2–D4 reserved evidence publication, owner/reviewer gate and seal; no proof work.

Full declaration correspondence: O6-R204-DECLARATIONS.md. Raw snapshots/logs/receipts: O6-R204-COMPILER-EVIDENCE.tar.gz (pre-publication anchor; later artifact receipts follow).

## D2 — final validation complete, checked PARTIAL

**190/190 final expected outcomes PASS**: ALL181 inherited main sources +8 new
=189 source targets (182 positives,7 exact-diagnostic+symbol negatives), plus
seeded package. Zero path exclusions; every invalidated/planned import checked
in topological order. PlanSHA0ecb6cf829d07bc1a172eb5d0746fc6d1910e7ad8582f0390e559a6a540041ab.
Validation began21:39:30Z, completed 2026-09-09T22:21:11.007075+00:00; well before the shift
cutoffs. This is seeded, NOT cold; unvalidated source-pinned seeds are not
fresh-PASS claims. All9 changed Idris files have a final exact-source check.

All native evidence: **228 invocations =222 expected PASS +6 rejected
snapshots**. This includes35 A/B proof checks,2 P1 repair checks,1 authorized
unchanged-source V0-CACHE and190 final checks. A3-2 is a genuine PASS superseded
only by rstrip; A15 remains three failures, fully reverted.29 retained new
declarations +1 style-only source repair =30 guarded source commits.37
compiler-free adversarial tests PASS. Final independent machine authentication,
frozen audit and resource audit PASS; no new proof or macro closure follows
from these metadata checks. Author review is separate from independent human
review; owner/reviewer gate still pending at D2 publication.

RSS: maximum sampled RSS over command-matching idris2 processes (single-process compiler; not an aggregate process-tree total; not OS high-water).
LocalDiamond maximum 50,540,272KiB <52GiB;
other/UniqueOrdinal maximum 44,805,616KiB <48GiB.
No source mutation, resource stop, same-lane compiler overlap or unexpected
dependency Building. 123 invocations
observed cross-lane overlap, logged by UTC timestamps ONLY; no lane2 actions
or shared lock/window operations. Zero samples mean no live sample, not zero
actual peak. Final native compiler has exited; no staged files.

A/B remain PARTIAL at their caps, C **INELIGIBLE** and unattempted; unchanged
census **4=1/2/0/0/1**. Production/frozen hashes and bridge manifest remain
exact. B still needs full controls/absent-domain ALL-name rebase and actual-chain
D5. A still needs canonical-prefix activation-position transport, unconditional
predecessor cut, genuine skip integration, whole histories and synchronization.
No global zip/whole-word coverage or whole canonical history is claimed.

D2 publishes the anchored raw archive, per-module measurements, exact compiler
ledger, reviewed source/repair correspondence and machine reports. Its anchor
precedes publication/final-gate receipts; those future receipts are explicitly
not claimed inside that archive. The inventory has298 entries:187 rechecked
+2 auxiliary inherited source targets =189 direct sources;111 other inventory
entries remain NOT rechecked. R205 visibility companion is a future-gated
candidate ONLY; no current Idris visibility/type/body change.

## D3 — post-publication checks and gate readiness

D2 publication `ee37c24a` is followed by read-only independent, frozen and
archive verification: all PASS. Post-publication snapshots and U0b/D1/D2
artifact before/after hash receipts are now published separately from the
append-only raw archive. Archive anchor56d1269b intentionally excludes later
publication/gate receipts; no archive was rewritten. Source freeze3e6d8ff0,
190/190 final expected outcomes,29 new declarations, P1/P2 repairs, A/B partial,
A15 full revert and C ineligibility are unchanged. D1/D2/D3 are artifact units;
D4 alone remains reserved for the owner/reviewer disposition seal. No extra
native check, source edit, new proof or visibility companion was attempted.
The tracked tree was clean with only allowed paper/ and adversarial-review
untracked inputs at the post-publication audit; no own compiler or staged files.
