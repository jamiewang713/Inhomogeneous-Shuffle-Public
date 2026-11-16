# Independent assumptions audit: occupancy-conditioned internal edges

This is a new pre-freeze audit of the formerly optional O.D01–O.D02/O.01–O.07 inventory. It does not alter the source, either existing frozen contract, any prior review, or the proved core. No Lean implementation was written during this audit.

I reread the TeX's internal conditional edge calculation at lines 1515–1523 and its labelled-row conditioning discussion at 3032–3077 and 3140–3166. I also reread `2510.22783v1.pdf`, Lemma 4.14, printed p. 27, and `2103.05068v3.pdf`, Lemma 4.12, printed p. 24. The old optional statement inventory in `collision_contract_statements.md` section 7 supplies the exact proposed statements being audited here. A fresh final signature report must still be compared before the new separate freeze.

## Mathematical verdict

The proposed finite occupancy-conditioned estimate is true under the already constructed independent fixed-column matrix law. It needs no concentration, stable-block, good-column, positive-pile, positive-occupancy, or positive-slice-probability hypothesis.

Write Q_x for the number of rows with the fixed prefix x, C_x for its unordered full-word collision count, e_x for its internal adjacent-edge count after sorting, and

```
kappa_x = product_{j≥M} sum_a n_j(a)(n_j(a)−1)/(N(N−1)).
```

For every natural q, the correct exact identity and edge consequence are

```
E[C_x * 1_{Q_x=q}] = choose(q,2) * kappa_x * P(Q_x=q),
E[e_x * 1_{Q_x=q}] ≤ choose(q,2) * kappa_x * P(Q_x=q).
```

They use the core's total arithmetic convention and its explicit zero/single-row cases. For a positive-probability slice, division would give the usual conditional mean bound, stronger than the TeX's q² coefficient. No conditional probability at a null event is defined or needed by these displayed identities.

The source's independence is between columns, not rows. The fixed-count factor uses N(N−1), even when the occupied subset has q rows. Revealing Q_x=q only selects among possible prefix arrays; it does not make their columns independent after conditioning. Tail columns are unaffected because Q_x is a function of the prefix columns alone.

## Source fidelity and conditioning population

The TeX's proof begins with the internal-edge estimate conditioned on prefix occupancy. The older fixed-column paper likewise counts pre-sorted pairs and uses the same tail falling-factorial product. The 2021 paper supplies the analogous combinatorial argument, but its independent-row digit model must not be imported into the present construction.

The later TeX discussion of conditioning prescribed labelled symbols carefully changes the population and subtracts the revealed digit counts. That is a different operation. In the present result, only prefix columns are fixed when the tail is integrated. No tail symbol has been prescribed, so every tail column is still an assignment on all N labels with its original counts n_j. The selected subset is not itself a fresh fixed-count column population.

A concrete check is N=4, two columns, prefix digit 0 in the first column, and counts (2,2) in each column. Prefix occupancy is always 2. Conditional on any prefix array, the two selected labels match in the second column with probability

```
(2*1 + 2*1)/(4*3) = 1/3.
```

The restricted two-label tail counts are random; they are not fixed by the prefix array or its occupancy. Replacing the population by q=2 while retaining the original counts would even give an invalid probability 2. The original denominator is a substantive part of the theorem.

No part of this argument creates endpoint-location randomness. The edge-count inequality uses the permutation-invariant collision count. It does not prove a pointwise edge-probability bound, a recentered/global density equality, or a conditional exploration law.

## Definition audit

### O.D01: the two count arrays

`prefixCounts n hM` restricts the absolute coordinates to 0,…,M−1. `suffixCounts n hM` uses the coordinates M,…,K−1 in their original order. Its tail coordinate t maps to M+t, with the bound proved from t<K−M and M≤K.

The count vectors themselves are unchanged. Their sum identities are inherited by composition with the two explicit index inclusions. No new count hypothesis or normalization parameter is required. The corresponding laws are applications of the already proved `matrixLaw` constructor with the same population N.

The definitions must permit M=0 and M=K. They need no inhabitant of Fin k. Empty coordinate families are actual empty functions, and their product law is the existing one-point law.

### O.D02: the split equivalence

The forward equivalence must restrict the actual matrix sample to these two intervals. The inverse must glue exactly those entries back in their original order. For an absolute j, the inverse uses the prefix coordinate j when j<M and the suffix coordinate j−M otherwise. The resulting prefix/suffix count types are identified by the corresponding index equalities; these are transport proofs, not extra model data.

All inverse identities must be proved. The data type carries no assumed split-law property. The equivalence's population parameter N must be explicit or otherwise determined by an actual typed sample: n's count-array type alone does not determine N. This is the same signature issue resolved in the core freeze.

The local notation `glue(p,t)` is the proved equivalence's inverse, not an additional independently sampled matrix or a new probability law. W, Wpre, and Wtail remain the three actual `matrixLaw` values, and Z remains the defined sorted occupancy count.

## Every proposed lemma

| ID | Verdict | Required proof steps and hidden-case checks |
|---|---|---|
| O.01 `matrix_expectation_split` | Accepted for every real-valued function f. | Reindex the finite sum through the actual split equivalence and factor the actual weights. The core C.17 uniform-weight identity and cardinality of an equivalent product give another valid proof. Both approaches prove the factorization; neither assumes conditional independence. Finite sums need no integrability or nonnegativity hypothesis on f. Empty factors remain one-point laws. |
| O.02 `tailCollisionFactor_suffix` | Accepted as an algebraic coordinate identity. | Use the bijection t↦M+t between Fin(K−M) and the suffix index finset. The population N remains explicit and unchanged. M=K gives equality of empty products 1. Feasibility hn is unnecessary if the final signature treats this as a pure factor identity. |
| O.03 `prefix_occupancy_glue` | Accepted pointwise for every valid prefix array and tail array. | Prove actual prefix membership for each original label agrees with membership in the prefix array. Then use the existing list adapters and finite count definitions. Sorting is unnecessary in this statement; core C.30 later identifies sorted occupancy. No probability or positivity assumption is used. |
| O.04 `increasing_pairs_in_finset_card` | Accepted for every finite subset s of ℕ. | Order-enumerate s and transport increasing pairs from range(s.card), or give a direct finite bijection. A trusted order isomorphism from Fin(s.card) also covers s=∅. No nonempty or minimum-element premise is allowed. |
| O.05 `tail_expected_collisionPairs_given_prefix_array` | Accepted for every fixed prefix array p. | Its occupied original-label subset S is deterministic. Count its increasing pairs by O.04. For a pair in S, the prefix digits already agree, so full-row equality is equivalent to suffix-row equality. Apply the proved core two-row product formula to the suffix matrix with empty prefix, and O.02 to its factor. Core C.31 transports the full collision count through sorting. Empty/single-row cases must be settled before applying a theorem requiring distinct labels. |
| O.06 `matrix_collisionPairs_occupancy_slice` | Accepted for every q:ℕ with no additional premise. | Use O.01 and prefix measurability from O.03/C.30. Within a fixed prefix array the indicator is constant in the tail variable. Apply O.05 on its true branch, replace the fixed occupancy by q there, and use zero on its false branch. No division by slice probability occurs. |
| O.07 `matrix_internal_edges_occupancy_slice` | Accepted with exactly O.06's domain. | Apply the frozen pointwise edge-to-collision count bound on the true branch and equality to zero on the false branch. Expectation monotonicity and O.06 prove the result. No upper bound on q or its probability is needed. |

O.03's displayed conclusion is only a cardinality identity. **O.05 must not infer equality of the actual occupied subsets from that cardinality identity alone.** The required pointwise membership equivalence and the corresponding full-row/tail-row equality equivalence follow from core C.21/C.22 and the explicit glue coordinates. They must be proved as local steps inside the planned statements, or separately included as reviewed named statements before freeze. The seven-statement inventory can remain unchanged by keeping these elementary bridges local.

Likewise, the equality in O.05 concerns unordered collision pairs, not adjacent edges. A full word repeated r≥3 times contributes choose(r,2) pairs and r−1 graph edges. The final edge statement is therefore an inequality, as proposed.

## Explicit case audit

- **N=0:** all feasible columns are empty assignments. Prefix and tail spaces still exist. Occupancy and both counts are zero. The only occupancy slice with positive probability is q=0. The right side is zero through choose(0,2), irrespective of whether the tail factor is an empty product or an algebraic zero factor.
- **N=1:** no pair of distinct labels exists; collision and edge counts are zero for every sample. The possible occupancies are 0 and 1. The one-row occupancy remains meaningful, but no pair theorem cancels the zero denominator N(N−1).
- **q=0:** no selected labels exist, so no collision or internal edge exists on the slice.
- **q=1:** there is one selected label but no pair. This is not the same as an empty prefix block, and the proof must not set its occupancy to zero.
- **q>N:** the event is impossible because occupancy is a cardinality of a subset of the N labels. The universal slice identities remain valid without adding q≤N; on this event every indicator is zero.
- **A null slice:** both integrated sides vanish. The formula does not need a conditional distribution on that event and must not invoke division by its probability.
- **K=0:** M=0, both split matrix factors are empty families, every full row is [], and Q_x=N deterministically. The collision count is choose(N,2), the tail factor is 1, and the internal edge count is N−1 for N≥1. These satisfy the proposed formulas, including N=0/1 by natural subtraction.
- **M=0 with K>0:** the prefix array is the unique empty array and the selected subset is the entire deck. O.05 reduces to the core collision mean for the empty prefix. The only positive-probability occupancy slice has q=N.
- **M=K:** the suffix array is the unique empty array and its factor is 1. Every selected row equals the full word x. Its unordered collision count is exactly choose(Q_x,2); no random tail is required.
- **k=0:** if a column exists, feasibility forces N=0. A positive-length prefix with values in Fin 0 has no instance. When K=0, the empty word and empty array exist for any N. No default digit or nonempty alphabet should be added.
- **A zero selected prefix pile:** no original label can have the prefix, so Q_x=0 pointwise. The construction remains valid; legal-word positivity is unnecessary.
- **A selected prefix pile of size one:** Q_x≤1, so all collision and internal-edge slice quantities vanish. A one-row occupancy remains possible.
- **A deterministic full pile or Q_x=N:** the argument is unchanged. All tail assignments still use population N, with no required complementary population fraction.
- **A zero tail coincidence factor:** O.05 gives zero collision expectation. No inverse factor is used, so the zero case does not need exclusion.
- **Repeated full words/ties in sorting:** core C.31 is samplewise and permits every multiplicity. It preserves counts even though the sorting permutation depends on the tail.
- **Out-of-alphabet or overlong lists:** the selected prefix representation remains x:Fin M→Fin k with M≤K. Generic core count lemmas still exist for arbitrary lists, but these specific product formulas do not claim to encode an out-of-domain matrix prefix.

## Dependency order and freeze boundary

O.D01 and O.D02 come first. O.01 uses their actual split and the core's constructed laws. O.02 is an independent coordinate-product identity; O.03 is an independent deterministic prefix identity; O.04 is an independent finite-order counting fact. O.05 uses the split coordinates, core row/event/count theorems, O.02 and O.04. O.06 uses O.01, O.03, core sorting occupancy invariance, and O.05. O.07 uses O.06 and the existing deterministic edge-to-pair inequality.

The proposed core O.D01–O.D02/O.01–O.07 inventory is mathematically accepted, subject to comparison of the new exact signature report. It needs no extra probabilistic assumption or axiom. All existing source and frozen statements remain unchanged. This is a separate additive result proving the occupancy-conditioned internal collision/edge component; it does not establish arbitrary exploration preservation, a residual-population law after tail symbols are revealed, any endpoint atom estimate, or the printed spatial density bounds.

## Comparison with the final conditional statement report

I compared the complete `conditional_contract_statements.md` with this independent audit. **All three definitions and all seven exact theorem signatures/conclusions are accepted, with no remaining mathematical or finite-case issue.**

- `prefixCounts` and `suffixCounts` correctly omit N and hn: they only restrict the original array. Their coordinate maps preserve absolute time and the prescribed counts.
- `splitMatrix` correctly takes explicit N, has the actual coordinate restrictions as its forward map, and requires no feasibility assumption. Its inverse laws are proved constructor obligations. Obtaining local glue-coordinate identities from `apply_symm_apply` preserves the intended semantics without an assumed coordinate interface.
- O.01 uses the actual three constructed laws and arbitrary real f. Its count proofs are inherited from hn, and the uniform-weight/cardinality route proves the finite factorization. No extra law or generic named integration lemma is introduced.
- O.02 correctly has explicit N and no hn. It is the exact suffix-product identity for all natural count arrays, including empty tails.
- O.03 correctly omits hn and uses actual typed prefix and tail samples. Its deterministic occupancy conclusion is exactly the one audited above.
- O.04 has precisely the arbitrary finite subset of natural labels as its domain; it adds no nonempty-set premise.
- O.05 retains N in the tail law and its factors. Its explicit local proof plan now includes the original-label prefix-membership equivalence, full-row equality versus tail-row equality when both prefixes are fixed, and the collision-event characterization. It does not infer those facts from O.03's cardinality conclusion. It includes the N=0/1 branches before invoking a distinct-label theorem.
- O.06 and O.07 use the same sorted occupancy Z and the exact if-expression for the event indicator. They quantify over every natural q and do not assume a positive slice probability or q≤N. The equality is only for collision pairs; the adjacent-edge result remains an inequality.

The designated module allocation is acyclic and agrees with the seven-statement inventory. Keeping all coordinate, label-membership, weight, and case-count bridges as proved local steps preserves the agreed absence of additional named helpers. The final report correctly distinguishes prefix measurability, a fixed full prefix array, and an arbitrary exploration reveal. The existing contracts and implementations remain unchanged. This acceptance precedes the new freeze and authorizes no Lean code by itself.
