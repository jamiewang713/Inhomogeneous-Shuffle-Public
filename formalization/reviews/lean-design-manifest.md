# Independent per-declaration review of CONTRACT.candidate.md

Reviewer role: Lean statement and representation design. This review compares the candidate only with the three permitted mathematical sources, my independent design report, and trusted Lean/mathlib APIs. I have not read the other reviewers' reports. No Lean project code was written before this review.

Verdict: **approve all 74 IDs as mathematically sound and representable without extra hypotheses or project axioms**. The explicit zero-based endpoint convention resolves the source's shorter-prefix comparison error. No statement changes are required. The implementation should introduce the inherited vector linear-order instance explicitly with `inferInstanceAs` on its list subtype if typeclass inference does not unfold `List.Vector`; this is a representation detail with precisely the frozen ordinary lexicographic order.

The finite generic interval statements need `[Fintype α] [LinearOrder α]`, exactly the finite linearly ordered type in the standing conventions. Noncomputable/classical definitions, equality proof irrelevance, and the standard trusted choice principles are allowed by the stated use of trusted mathlib; they are not new project axioms. The graph constructor's symmetry/irreflexivity and the legal node constructor's legality are obligations, not hypotheses supplied by a user.

## Profiles and masses

| ID | Validity and Lean proof path |
|---|---|
| P01 | Approved. Unfold `countAt`; simplify the dependent `if` with `j<K`; proof irrelevance identifies the `Fin` arguments. |
| P02 | Approved. Unfold the same definition; `¬j<K` follows from `K≤j`. |
| P03 | Approved. A selected nonnegative summand is bounded by the whole finite sum; rewrite the pile-profile column sum. |
| P04 | Approved for all natural positions, including outside K. `Nat.cast_nonneg` and `div_nonneg`. |
| P05 | Approved for all positions. Inside K use P03 and positive denominator; outside K use P02 and zero division. |
| P06 | Approved. The real cast of N is positive, so `div_pos_iff_of_pos_right` and cast positivity give precisely positive natural count. |
| P07 | Approved. Rewrite as `(∑ a, (countAt j a : ℝ))/(N:ℝ)` using `Finset.sum_div`; P01 and the cast column sum reduce it to `N/N=1`. |
| P08 | Approved. If every natural count were zero their sum would be zero, contradicting N>0; equivalently use a positive finite-sum summand. |
| P09 | Approved. Fin 0 is empty, so its product is one. |
| P10 | Approved. Finite product of nonnegative coordinates, using P04. |
| P11 | Approved for every depth, including beyond K. Finite product bound by one uses P04/P05; no hidden bounded-depth condition is needed. |
| P12 | Approved with the stated m≤K. Finite product positivity iff all factors are positive, followed by P06; attach/remove the already supplied length bound. |
| P13 | Approved with m≤K. Transport vectors to finite functions by `Equiv.vectorEquivFin`, then the finite sum-of-products identity is the product of each column sum (P07). An induction adding the final digit is another genuine proof. |
| P14 | Approved at arbitrary depth. The last-coordinate decomposition of the product over Fin(m+1) gives the old product and final coordinate. Vector append uses exact underlying list append. |

## Words

| ID | Validity and Lean proof path |
|---|---|
| W01 | Approved. Trusted reflexivity of `List.IsPrefix`. |
| W02 | Approved. `List.IsPrefix.trans`. |
| W03 | Approved. `List.IsPrefix.length_le` and vector length proofs. |
| W04 | Approved. `List.IsPrefix.eq_of_length`, followed by subtype extensionality. |
| W05 | Approved. `List.nil_prefix`. |
| W06 | Approved. `List.take_prefix`. |
| W07 | Approved. `List.prefix_iff_eq_take`, reversing equality as needed; vector extensionality and fixed lengths. |
| W08 | Approved even for differing depths. Trusted `List.prefix_or_prefix_of_prefix`. |
| W09 | Approved on all variable-length lists. Induct on requested take depth and list constructors. Nil cases are immediate; nonempty cases follow `List.cons_le_cons_iff`, preserving a strict leading comparison or reducing equal heads to the induction hypothesis. Monotonicity is non-strict, correctly. |
| W10 | Approved even for variable-length lists. Apply W09 with depth `x.length` to `a≤b≤c`. The two outer truncated lists equal x by `prefix_iff_eq_take`; antisymmetry gives `b.take x.length=x`, hence the required prefix. No length assumption on b is needed. |
| W11 | Approved. Truncation has smaller depth and `List.getElem_take` preserves every selected coordinate. The nonnegative-index zero extension creates no extra assumptions. |
| W12 | Approved. Zero≤K and the universal property over Fin 0. |
| W13 | Approved with exactly the three RHS conjuncts. Append depth is m+1; first m positions are unchanged and the last selected count is `countAt m a`. Both directions use the same coordinate split, so this introduces no convenience hypothesis. |
| W14 | Approved. Choose one P08-positive symbol per remaining column; define a full vector by the original coordinates when j<m and chosen positive symbols otherwise. Coordinatewise extensionality establishes that truncation is x, then W07 gives prefix. Can alternatively induct on remaining depth using W13. |

## Prefix tree and cylinders

| ID | Validity and Lean proof path |
|---|---|
| T01 | Approved. Apply W01 to the underlying node word. |
| T02 | Approved. Apply W02 to the underlying words. |
| T03 | Approved. Mutual list prefixes imply equal lists and hence equal lengths; dependent sigma extensionality plus proof irrelevance gives equality of legal nodes. No arbitrary tree-order axioms are assumed. |
| T04 | Approved. W05. |
| T05 | Approved. Parent is truncation at depth−1, so W06. |
| T06 | Approved by the parent's actual truncated-word construction. Holds at root too, since natural subtraction gives zero. |
| T07 | Approved. T06 and the arithmetic fact d−1<d for d>0. |
| T08 | Approved. Use P08 in column depth x, append that symbol, and prove legality with W13. Its depth is exactly one larger and its list extends x. |
| T09 | Approved. W14 supplies a full legal word and its cylinder membership. |
| T10 | Approved. W02 composes x≤prefix y with y≤prefix the full word. |
| T11 | Approved. Forward: a common cylinder element gives W08. Reverse: T09 for the longer prefix gives an element in both via T10. Legality is already part of Node P. |
| T12 | Approved. Intersection membership gives comparability by T11, and either orientation contradicts antichain distinctness. |
| T13 | Approved. Cover gives existence; two candidate members are comparable by W08, then antichain gives equality. The explicit cover assumption is necessary and correctly present. |
| T14 | Approved. Forward: truncate the full word at depth x+1, legal by W11, then identify its shorter prefix with x. Reverse: prefix transitivity. No choice of empirical row is involved. |
| T15 | Approved. `Fin(K+1)` is finite, every vector word is finite via `Mathlib.Data.Fintype.Vector`, a dependent sum of finite types is finite, and any subtype is finite. A noncomputable `Fintype.ofFinite` is valid if a decidable legality instance is not installed. |

## Matrices and ranks

| ID | Validity and Lean proof path |
|---|---|
| M01 | Approved. For each j, the finite dependent sum `Σ a : Fin k, Fin(n(j,a))` has cardinality N. A trusted finite-cardinality equivalence with Fin N assigns each row a symbol; each symbol's fiber has the prescribed cardinality. Independent constructions per column define one full row vector per label. Thus no feasibility input is missing. |
| M02 | Approved. The row index itself belongs to the relevant column-symbol fiber, so its cardinality and thus n(j,a) are positive. |
| M03 | Approved. A permutation of row indices bijects every column-symbol fiber. Defining the reindexed matrix requires this proof as its count field. |
| M04 | Approved. `Tuple.monotone_sort`. |
| M05 | Approved. Sorted rows are original rows at an actual permutation index; apply M02. |
| M06 | Approved. The same index permutation bijects the two filtered universal finsets for any row predicate, with classical decidability. |
| M07 | Approved. W09 composed with M04 gives a monotone tuple of depth-truncated lists. Use `Tuple.lt_card_lt_iff_apply_lt_of_monotone` and `Tuple.lt_card_le_iff_apply_le_of_monotone`; the pair of rank inequalities is equivalent to equality with x.list, then `prefix_iff_eq_take`. |
| M08 | Approved. M07 identifies the finite rank set with a bounded natural half-open interval; M09 bounds ensure the intersection with Fin N loses no points. Card is U−L, including U=L. |
| M09 | Approved. Nonnegativity is natural. The strict-comparison fiber is included in the weak-comparison fiber; the latter is included in Finset.univ with card N. |
| M10 | Approved. Either W10 after M04, or simply M07 and order transitivity. |
| M11 | Approved. Prefix transitivity applied to each sorted row. |
| M12 | Approved. A rank in both sets would give a common full extension, hence W08-comparability. |

## Shuffle graphs

| ID | Validity and Lean proof path |
|---|---|
| G01 | Approved. Definitional adjacency characterization; graph constructor must prove symmetry and looplessness from neighboring natural ranks. |
| G02 | Approved. Drop the equal-row conjunct of G01. |
| G03 | Approved. G01 yields identical row words, so all prefix predicates agree. |
| G04 | Approved. M04 sandwiches the middle row between equal outer rows; antisymmetry gives equality. |
| G05 | Approved. Reachability-to-equality follows by induction over a graph walk. Conversely assume equal rows, orient i≤j, and induct through the consecutive finite indices from i to j. G04 gives equal rows along that path; G01 supplies each edge. Reflectivity handles i=j and graph symmetry handles the reverse orientation. |
| G06 | Approved. Definitional block graph on the original vertex set, retaining edges with both endpoints in rankSet. Symmetry and looplessness descend from shuffleGraph. |
| G07 | Approved. Definitional graph infimum/intersection; no independence assumption belongs to shared adjacency. |

## Lexicographic intervals

| ID | Validity and Lean proof path |
|---|---|
| I01 | Approved. Finite sum of nonnegative weights. |
| I02 | Approved. Add the nonnegative endpoint weight. |
| I03 | Approved. The weights below or equal to a form a sub-sum of the total. Distinctly split `<a` and `{a}` to identify that sub-sum with right(w,a), then compare with sum=1. |
| I04 | Approved. If a<b, every index ≤a lies strictly below b. Compare their nonnegative finite sums, identifying the first with right(w,a). |
| I05 | Approved. Linear-order trichotomy and I04 make the respective half-open intervals separated. Equality of a terminal endpoint with the next initial endpoint causes no overlap. |
| I06 | Approved. `Ico l r=∅` iff r≤l; here r=l+w(a), and nonnegative w(a) makes this equivalent to zero. |
| I07 | Approved without sign assumptions. Ring/additive cancellation. |
| I08 | Approved. One inclusion uses I01/I03. For t∈[0,1), choose the least index whose cumulative right endpoint exceeds t (exists since the maximal cumulative right is the total 1), giving left≤t<right. Alternatively use finite induction after sorting all α. Zero weights create empty intervals but no gaps. Finite α cannot be empty under sum=1. |
| I09 | Approved. I06, P10 and P12: zero mass iff not positive iff not legal, with m≤K. |
| I10 | Approved at every depth, including m>K. Apply I05 using P10; normalization is not needed for disjointness. |
| I11 | Approved with m≤K. I08 plus P10/P13. |
| I12 | Approved. `a<y≤t` gives a<t and `t≤z<b` gives t<b. The additional membership hypotheses are harmless but match the exact frozen statement. |

## Remaining scope boundary

All selected conclusions are basic finite combinatorics. This contract intentionally excludes graph-law identities, expectation identities, concentration, estimates, asymptotic limit claims, and the stronger `2Kk` cylinder decomposition of a lexicographic interval. No omitted result may be represented by a placeholder declaration. The definitions `H_x` are harmless deterministic sets but no cardinality or integer-rounding theorem for them is among these 74 IDs.
