# Root verification of the frozen occupancy-conditioning addendum

All seven declarations O.01–O.07 and the three selected definitions are implemented and kernel checked. The root read the complete Model, Split, Counts, and Estimates implementations, compared their actual statements with `frozen_conditional_contract.md`, and compared all three independent implementation reports. No mathematical correction or added assumption was requested.

The constructed matrix equivalence splits the original columns into prefix and suffix arrays. Both arrays still have N row labels and the original restricted column counts. The expectation split is valid for every real-valued integrand. The prefix membership of each original label, and the equality of two complete words with that prefix, are proved locally before counting their collisions. Consequently the tail pair probability retains the original denominator N(N−1).

For sorted prefix occupancy Z, collision count C, internal-edge count E, and the exact original-population tail factor Q, the new results prove, for every natural q,

```
E[C * 1_{Z=q}] = choose(q,2) * Q * P(Z=q)
E[E * 1_{Z=q}] ≤ choose(q,2) * Q * P(Z=q).
```

Lean represents the indicators by if-expressions. Both sides use the same sorted occupancy. The proof fixes the entire prefix array, integrates over the independent suffix, then averages the occupancy indicator over prefix arrays. It does not assert independence among prefix columns after conditioning on occupancy. It never divides by an event probability. Impossible occupancies, null slices, q=0/1, and a zero tail factor are therefore included. The zero- and one-card population cases are explicitly discharged in the fixed-prefix collision theorem before a distinct-label formula is used.

The root's first implementation of O.06 encountered an elaboration timeout. Two agents independently investigated alternative decompositions. Both isolated the first final calculation step: elaborating `hsplit _` in a tactic block supplies the expected type before solving the integrand metavariable. This proof-only change removed repeated unfolding of occupancy cardinalities. The final file compiles at the default heartbeat limit, with no opacity change, theorem change, new helper declaration, or new assumption. Its final algebra uses explicit true and false indicator branches.

`verify_conditional.py` passed the exact seven-theorem/three-definition inventory, all three immutable contract hashes, the three permitted source hashes, the pre-code review hashes, and the hashes of all eleven parent implementation files. It compiled the addendum, saved every compiled signature, and audited logical dependencies. Only the permitted foundations `propext`, `Classical.choice`, and `Quot.sound` occur. The machine-readable evidence is `conditional_verification.json`, `conditional_signatures.log`, and `conditional_logical_dependencies.log`.

The project now contains 98 verified finite theorems: 33 original, 58 collision, and 7 occupancy-slice declarations. This completes the selected occupancy-only conditional internal-edge dependency in the source's edge-density proof. It does not establish the internal-information conditioning used for positional anti-concentration, arbitrary exploration preservation, stable profile estimates, or any missing spatial gain. The full original goal remains incomplete and active.
