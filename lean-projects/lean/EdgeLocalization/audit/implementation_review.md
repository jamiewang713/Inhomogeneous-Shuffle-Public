# Independent implementation review against frozen contract v1

Reviewed the five implementation modules against `frozen_contract.md`, after the independent mathematical audit and pre-freeze comparison. This review did not modify any Lean file.

**Result: PASS for D1–D8 and F01–F33.** The implemented statements match their frozen hypotheses and conclusions. No hidden probabilistic estimate, new distributional assumption, or contract drift was found.

| Module | Frozen statements | Review result |
|---|---|---|
| `FiniteLaw.lean` | F01–F13 | The law contains only nonnegative normalized real weights. Expectation and event probability are the frozen finite sums. All monotonicity, normalization, indicator, and cardinality identities have explicit proofs. |
| `Deck.lean` | F14–F21 | The edge range is exactly `Finset.range (N-1)`. Edges inject into occupied left endpoints and into increasing equal-row pairs. The injection proves that both positions lie below N. |
| `Density.lean` | F22–F25 | Squared marginal edge probabilities are bounded by expected edge counts, occupancy, or collision-pair counts using only the proved finite identities and deterministic inequalities. |
| `FirstColumn.lean` | F26–F28, F31–F32 | A canonical balanced column is constructed for every a,b. Endpoint counts are exactly a and a+b. Positive a supplies the nonzero denominator in the zero-slack calculation. The variance statement claims only a zero arithmetic numerator. |
| `EndpointObstruction.lean` | F29–F30, F33 | The endpoint event is certain under any normalized finite law on balanced columns; intersecting with S preserves P(S). The impossibility result uses exactly q<P(S). The finite enumeration is derived from the existing finite-function/subtype structure, not added as a hypothesis. |

Boundary cases checked: N=0 and N=1; empty edge and index ranges; empty prefixes; arbitrary row-list lengths; zero-probability events; zero weights; a=0 or b=0; and empty middle cylinders. `balanced_column_exists` proves the column subtype is nonempty even for a=b=0. A normalized law on an empty sample type cannot exist, which is consistent with D1 and introduces no hidden existence claim.

F12 explicitly proves equality of the two indicator presentations by membership cases, so differing decision instances do not alter the event semantics. Its inclusion hypothesis is exactly the frozen finite-index requirement. The real-valued cardinality casts in F22–F25 preserve the deterministic natural-number inequalities.

Registering that derived enumeration as a named `balancedColumnFintype` instance, proved by unfolding `BalancedColumn` and inferring the existing finite-function/subtype instances, is an implementation of D1/D7. It does not change a theorem's mathematical assumptions or introduce an axiom. This registration was independently approved when inline elaboration did not make the enumeration available to downstream probability notation.

The endpoint definitions are the frozen zero-based lexicographic rank counts. They do not assert an unproved equivalence to a separately implemented sorting algorithm. For source one-based intervals, both endpoints are shifted by one; their deterministic nature is unchanged.

The reviewed imports are mathlib or the reviewed project modules. A source scan found no `axiom`, `sorry`, `admit`, `unsafe`, or `native_decide`. All 33 named statements have proof terms; local facts in those proofs are proved, not postulated. This is a statement-and-proof review; the root agent's build and axiom audit provide the separate compiler record.

**Scope remains partial.** The fixed-column product probability law, conditional tail-collision product formula, exponent translation, and connection to an implemented sorting procedure are not implemented. Neither are the original stable-tree localization and cardinality estimates or the blocked asymptotic endpoint/large/small non-singleton statements. F23 proves the exact occupancy inequality underlying the terminal estimate; it does not itself formalize the source's asymptotic notation. F25 stops at expected collision-pair counts and does not silently assume the missing product formula.
