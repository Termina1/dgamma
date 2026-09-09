# L2R5 B5 — observed-provider producer stopped at 3/3

B1–B4 retained. `RetirementProviderFrame` and executable `retirementProviderFrame` (85cd102d) produce actual source/replacement observations: child-retired, child-active, actor-retired, declared-intersection, typed resolver-before/after, resolver-changed, each with its own equation; lookup and own-child metadata are authenticated. **No unchanged-resolver equation is assumed.**

B4 76a0b126 is the NEW `ProviderHeadObservation` record: an explicit observed Bool and defining guard equation, plus both native provider-head equations to that common observed value. It is a **stated package only**, not an inhabited producer.

B5 attempted `providerHeadObservation` to produce that exact single-constructor package. It exhausted 3/3. The entire new producer was reverted to HEAD bytes; the prior B4 record remains. V2 freshly rechecks the restored module. No B5-4, B7 restatement, deletion-square relabeling or alternate-edge oracle is authorized.

1. B5-1 explicitly split the actual retirement Bool False/True and simultaneously supplied the observed guard. Direct native provider projections did not reduce to the exposed lifecycle/table expression.
2. B5-2 additionally rewrote the existing `fiberLifecycleObservation` at each concrete False/True flag. The retired-head field still failed: both displayed expressions were `if isActive lifecycle && Delay (isJust (lookupBinding wanted (table .ownedValues))) then Just actor else providerIn wanted rest`, but hidden dependent projection indices did not unify.
3. B5-3 fully instantiated the record constructor (all universes, equality instances, actor/key/component/parent/flag/table/lifecycle/rest), and matched the component constructor. The identical displayed retired-head constraint remained. This is the requested exact observed-value residue, not proof of false invariance.

Raw attempted statements and full diagnostics: `/tmp/dgamma-l2r5/B5-{1,2,3}.{source,log,json}`. They will remain immutable in the evidence archive. The stopped function is absent from retained sources. No unsafe escape hatch, partiality, `with`, inferred local view, nested producer or main-lane compiler action was used.

## Role coverage at stop

| Role | Status |
|---|---|
| ROOT / every-parent OInsert | Inherited L2R4 B13, original edge only, unchanged |
| Foreign ORetire | Inherited L2R4 B6, original edge only, unchanged |
| Foreign ORemove | Inherited L2R3 C14, original edge only, unchanged |
| LBegin original-edge replay after retirement | OPEN; native provider/target invariance producer stopped |
| LIter / LFinish after retirement | OPEN; same provider/target frame dependency, deletion square is not retirement |
| Other lifecycle tags/actions | OPEN, not silently omitted |
| Full single dispatcher | OPEN; orchestration-domain dispatcher remains the only assembly |
| Whole R191 ForeignReplay | OPEN; unchanged fold's single callback unavailable |

This does not affect the separate new A18 `checkedRetireAcrossExtensional` role: that is ORetire replay between extensionally equal states, not an LBegin/Advance retirement square.
