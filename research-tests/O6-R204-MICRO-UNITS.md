# R204 micro-unit ledger

Caps: Unit0 <=2, B<=14, A<=16, C<=6, D<=4. One new declaration per proof invocation; <=3 invocations per unit. No self-extension.

| Unit | Invocations | Status |
|---|---|---|
| 0a | U0a-1 FAIL; U0a-2 PASS | Body-only inline repair; retry explicitly supervisor-authorized; receipt P1 |
| 0b | compiler-free artifact | P2 exact measurement wording; numeric samples unchanged |

The R203 milestone is ratified by the supervisor AFTER these two repairs land.
Exact hashes, logs, statement comparison and guarded receipts: /tmp/dgamma-r204; final publication pending.
