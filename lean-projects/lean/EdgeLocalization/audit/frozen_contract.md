# Frozen finite contract v1

This is a strict subset of exact consequences of the three permitted sources. It does not replace the false asymptotic statements with conditional versions. No project Lean code had been authored at the time of this freeze. The original fluctuation definition and all source assumptions stay unchanged in the source audit. The original anti-concentration theorem, large-block density theorem, and small non-singleton theorem are blocked by independent counterexamples.

## Exact definitions to be used

D1. A finite law on a type Ω with a Fintype instance consists of weights w : Ω → ℝ, w(ω) ≥ 0, and Σω w(ω)=1. These fields define a probability distribution; they contain no concentration or edge estimate. Expectation E_w f = Σω w(ω) f(ω). Event probability P_w A = E_w 1_A. Every finite shuffle-matrix law can be represented by such weights; constructing its uniform/product instance remains outside this finite contract. Uniformity is not required by the statements below. Event predicates are decidable using local classical instances where necessary.

D2. A finite deck is represented by N : ℕ and rows : ℕ → List ℕ, with only positions i<N inspected. Natural digits and arbitrary lists give a more general domain than the source's fixed alphabet and length. All results in this contract hold for every such deck, hence for the sorted fixed-length source deck. No claim of sorting, fixed counts, or independence is stored in this representation.

D3. For prefix x, occupied(N,rows,x) = {i∈{0,…,N−1}: x is a list prefix of rows(i)}. These zero-based positions correspond to source positions i+1.

D4. internalEdges(N,rows,x) = {i∈Finset.range (N−1): rows(i)=rows(i+1) and x is a prefix of rows(i)}. Natural subtraction gives the empty edge range for N=0 or N=1. allEdges is the same set for the empty prefix. collisionPairs(N,rows,x) = {(i,j)∈{0,…,N−1}²: i<j, rows(i)=rows(j), and x prefixes rows(i)}.

D5. For random rows R:Ω→ℕ→List ℕ, edgeProbability(i)=P_w(i∈internalEdges(N,R(ω),x)); edgeDensity=Σ_{i<N−1} edgeProbability(i)^2. edgeCount and occupancyCount are the cardinalities of the two corresponding finite sets.

D6. A fixed first column is c:Fin N→Fin 3. leftCount(c) = #{i:c(i)<1}, middleCount(c)=#{i:c(i)=1}, rightCount(c)=#{i:c(i)>1}. zero-based lower endpoint for prefix (1) is leftCount, upper endpoint leftCount+middleCount. These are count definitions of lexicographic endpoints for a one-digit prefix; no endpoint concentration is assumed.

D7. BalancedColumn(a,b) is the subtype of c:Fin(2*a+b)→Fin 3 with leftCount=a, middleCount=b, rightCount=a. It records only deterministic pile counts. Its canonical inhabitant has digit 0 for i<a, digit 1 for a≤i<a+b, digit 2 otherwise.

D8. The a=b reveal's complementary sampling fraction is 1−d/n. For first-column middle prefix, d=n=N−middleCount. Its exact variance numerator is n1*m*(n−n1)*(n−m). These are only arithmetic expressions, not a defined hypergeometric probability law.

## Complete planned named statements

F01 expectation_nonneg: for every finite law w and f≥0 pointwise, E_w f≥0.
F02 expectation_mono: for every finite law w and f≤g pointwise, E_w f≤E_w g.
F03 expectation_const: E_w(const c)=c, for every real c.
F04 probability_nonneg: 0≤P_w A for every event A.
F05 probability_le_one: P_w A≤1 for every event A.
F06 probability_true: P_w(universal event)=1.
F07 probability_false: P_w(empty event)=0.
F08 probability_congr: pointwise logically equivalent events have equal probabilities.
F09 probability_sq_le: (P_w A)^2≤P_w A.
F10 probability_of_forall: if A(ω) for every ω, then P_w A=1.
F11 probability_event_of_constant: for a type α with decidable equality, X:Ω→α and j:α, if X(ω)=j for every ω, then P_w(X=j and A)=P_w A, for every event A. (j in any type with decidable equality.)
F12 sum_probabilities_eq_expected_card: for any type α with decidable equality, s:Finset α, and H:Ω→Finset α satisfying H(ω)⊆s for every ω, Σ_{i∈s}P_w(i∈H)=E_w(#H).
F13 sum_sq_probabilities_le_expected_card: same domain and inclusion as F12, with squares on the left and ≤ on the right. Inclusion is the finite indexing requirement, not a probabilistic estimate.
F14 internalEdges_subset_occupied: every internal edge's left endpoint belongs to occupied.
F15 internalEdges_subset_range: internalEdges⊆Finset.range (N−1).
F16 internalEdges_card_le_occupancy: #internalEdges≤#occupied, all N including 0 and 1.
F17 internalEdges_zero: internalEdges(0,rows,x)=∅.
F18 internalEdges_one: internalEdges(1,rows,x)=∅.
F19 equal_rows_prefix_transfer: rows(i)=rows(j) and x prefixes rows(i) imply x prefixes rows(j).
F20 localize_internal_edge: i∈allEdges and i∈occupied imply i∈internalEdges; also the reverse implication. (Exact per-edge prefix localization, not the unsupported stable cardinality/probability claim.)
F21 internalEdges_card_le_collisionPairs: #internalEdges≤#collisionPairs, via i↦(i,i+1), all N.
F22 internal_density_le_expected_edges: edgeDensity≤E_w(edgeCount).
F23 internal_density_le_expected_occupancy: edgeDensity≤E_w(occupancyCount), all prefixes. In particular it is the exact terminal singleton estimate, stronger than its small-mean proof and independent of endpoint anti-concentration.
F24 internal_expected_edges_le_expected_collisionPairs: E_w(edgeCount)≤E_w(#collisionPairs).
F25 internal_density_le_expected_collisionPairs: edgeDensity≤E_w(#collisionPairs).
F26 balanced_column_exists: for all a,b∈ℕ, BalancedColumn(a,b) is inhabited by the canonical three-interval assignment, including N=0.
F27 balanced_left_endpoint: for every c:BalancedColumn(a,b), lowerEndpoint(c)=a.
F28 balanced_right_endpoint: for every c:BalancedColumn(a,b), upperEndpoint(c)=a+b.
F29 balanced_endpoint_atom: for every finite law on BalancedColumn(a,b), P(lowerEndpoint=a)=1 and P(upperEndpoint=a+b)=1.
F30 balanced_endpoint_good_event: for every such law and event S, P(lowerEndpoint=a and S)=P(S), and the same for the upper endpoint.
F31 positive_side_mass_no_sampling_slack: for every a,b∈ℕ with a>0 and every c:BalancedColumn(a,b), leftCount(c)=a>0 and rightCount(c)=a>0, while 1−(2*a:ℝ)/(2*a:ℝ)=0.
F32 full_sample_variance_numerator_zero: for all n,n1∈ℕ, n1*n*(n−n1)*(n−n)=0. No nonzero variance is inferred from positive side masses.
F33 no_atom_bound_below_good_mass: for every balanced law w, event S, and q∈ℝ with q<P_w S, the inequality P_w(lowerEndpoint=a and S)≤q is false (and likewise for upperEndpoint).

All mathematical assumptions above are explicit. This freeze does not authorize introducing declarations claiming the asymptotic localization, block-cardinality, anti-concentration, or large/small density conclusions. Any extra local proof steps must be proved inside these statements with the same assumptions; no additional assumed lemma or probability estimate is permitted. The matrix-law product collision factor, exact exponent translation, and stable-tree proof remain separately unimplemented obligations, not hypotheses smuggled into this contract.
