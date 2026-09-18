# Independent reconstruction of ambient-relative edge estimates

This is a pre-code reconstruction using the three permitted mathematical sources, existing proved project modules, and trusted mathlib finite-set and list-order facts. It changes no source or frozen artifact and contains no Lean implementation.

## Source convention and the exact coordinate map

The TeX fixes lexicographically sorted rows and adjacent equal-row edges at lines 389–393 and 449–473. Lines 490–517 fix a deterministic ambient prefix w and state that endpoints and edge locations are recentered at its left endpoint. The shared-edge first-moment identity at lines 1837–1841 uses the sum of the squared probabilities at the individual edge locations. The older homogeneous paper defines, on PDF page 16 (text extraction lines 871–878), the one-based first position as `iota(w)=#{i:s_i<w}+1`; its right endpoint counts rows strictly before the prefix or carrying that prefix. The fixed-column paper gives the same convention in equation (2.13), PDF page 11 (text extraction lines 621–627). Thus the zero-based cut immediately before the ambient cylinder is exactly

`L_w = #{i in range N : rows i < w}`.

The TeX's active lower proof also writes this left cut as a strict lexicographic count at lines 2951–2954. Its displayed right-endpoint `<=w` notation there should not be imported as the literal standard list comparison for a shorter prefix: a proper extension is greater than that prefix. The present proposal uses only the unambiguous strict left-cut definition and does not add or alter a right-endpoint definition.

The project already represents source edge `(m,m+1)` by the zero-based index `j=m-1`. Subtracting the zero-based ambient cut L gives relative index `j-L`. Consequently the proposed forward map from relative to absolute indices is exactly `i |-> i+L`, with no extra one. If relative vertices are instead displayed with one-based labels, this same relative index represents the edge `(i+1,i+2)`. That fixed labeling difference is harmless; it must not be confused with a random translation.

An empty ambient cylinder has a well-defined insertion cut L even though it has no first occupied row. When w is a prefix of x, an empty ambient cylinder has no internal x-edge. The cut convention therefore continues to make sense without a nonempty-cylinder hypothesis. For the root w=[] the strict-below set is empty and L=0.

## Three proposed definitions

For natural N and s, `rows : Nat -> List Nat`, and a list prefix x, define

`relativeInternalEdges N rows x s = (range (N-1)).filter (fun i => i+s in internalEdges N rows x)`.

For an existing finite law q on a finite outcome type Omega, a row map R, and any `shift : Omega -> Nat`, define

`relativeEdgeDensity q N R x shift = sum_{i in range(N-1)} P_q(i in relativeInternalEdges N (R omega) x (shift omega))^2`.

Finally define

`ambientLeft N rows w = ((range N).filter (fun i => rows i < w)).card`,

using exactly the same lexicographic `List Nat` order as the existing sort. In actual source applications take `shift omega = ambientLeft N (sortedRows n omega) (prefixWord w)`.

The generic shift may depend on the entire sample, including all internal rows and continuations. It is a deterministic function of that sample, not a separately independent random variable. Its two-copy version is evaluated separately at the first and second independent samples.

## Independent finite proof inventory

The following inventory records every mathematical step needed for the proposed transfer. Exact public names and any choice to keep immediate wrappers local remain subject to the independent statement report and comparison before freeze.

1. **Relative support.** For every N, rows, x, and s, `relativeInternalEdges ...` is a subset of `range(N-1)`. This is the first component of filter membership.

2. **Relative cardinality at most absolute cardinality.** With the same unrestricted arguments, its cardinality is at most `edgeCount N rows x`. Send i to i+s. Membership supplies the target edge and natural addition cancellation proves injectivity. No shift bound, sorting, prefix legality, or N≥2 premise is needed.

3. **Actual ambient cut precedes each child edge.** For an actual matrix n and outcome omega, arbitrary list words w and x with `w <+: x`, and an index j in `internalEdges N (sortedRows n omega) x`, prove `ambientLeft N (sortedRows n omega) w <= j`. No count-sum, legal-prefix, or list-length hypothesis is required for this deterministic statement. Internal membership gives x as a prefix of row j, so prefix transitivity gives w as a prefix of row j and hence `w <= row j` in lexicographic order. If an index i with `row i < w` satisfied j<=i, the existing sorting-monotonicity theorem would give `w <= row j <= row i`, a contradiction. Therefore the strict-below filter is a subset of `range j`, and its cardinality is at most j.

   The local prefix-to-lex-order fact follows by writing the larger list as the prefix appended to a suffix. An empty suffix gives equality; a nonempty suffix gives a strict lexicographic extension. Trusted `List.IsPrefix.le` provides this fact for the core list order; if the mathlib order instance requires a conversion, a local proof using `List.Lex.append_left` and the empty/nonempty suffix cases gives the identical result. No additional named helper or order hypothesis is necessary. Natural index bounds for sorting are obtained from the original edge membership and below-filter membership.

4. **Actual recentering preserves every child edge count.** For the same actual matrix/outcome and list relation `w <+: x`, prove

   `card(relativeInternalEdges N rows x (ambientLeft N rows w)) = edgeCount N rows x`.

   The upper bound is step 2. For the reverse direction, send each absolute edge j to `j-L`. Step 3 proves L<=j, so `(j-L)+L=j`; the original bound j<N-1 gives `j-L<N-1`, and hence this is a relative edge. Cancellation or adding L proves injectivity. This is a proved containment and bijection, not an assumed endpoint interface. Empty edge sets require no selected index. Arbitrary shifts need only the inequality in step 2; equality is asserted here specifically for the computed ambient cut and an actual prefix relation.

5. **Density at most expected absolute edges.** For arbitrary finite q, N, R, x, and sample-dependent shift, use the existing finite-law squared-probability sum bound on the relative sets. It gives relative density at most expected relative cardinality. Step 2 and expectation monotonicity bound this by `E_q edgeCount N (R omega) x`. This wrapper is useful but may instead remain local inside step 7.

6. **Density at most squared expected absolute edges.** For the same arguments, every relative membership probability is nonnegative. The trusted inequality `sum p_i^2 <= (sum p_i)^2` applies on the fixed support. Existing F12 identifies the sum as expected relative cardinality. Step 2 bounds that expectation by the expected absolute edge count; both expectations are nonnegative because they average natural cardinalities. Squaring therefore preserves the comparison. This proof does not compare relative and absolute densities.

7. **Density at most expected occupancy.** Compose step 5 with the existing pointwise `edgeCount<=occupancyCount` and expectation monotonicity. The occupancy is that of x in the full original deck, with the original population N.

8. **Exact independently recentered overlap.** For arbitrary q, N, R, x, and shift,

   `relativeEdgeDensity q N R x shift = E_{q.prod q} card(H(z.1) inter H(z.2))`,

   where `H(omega)=relativeInternalEdges N (R omega) x (shift omega)`. Apply the already proved finite-set intersection expectation formula on `range(N-1)`, using step 1 for both copies and `p*p=p^2`. Each event in one coordinate is measurable on the finite sample space regardless of how its shift depends on that sample. The constructed product law supplies the independence of the two full samples. No custom independence premise, common random shift, or diagonal coupling is used.

9. **Actual matrix fourth-power bound for arbitrary shifts.** For the existing feasible matrix law, hM:M<=K, x:Fin M->Fin k, and any `shift : FixedMatrix N n -> Nat`, prove relative density at most `prefixMean^4 * tailCollisionFactor^2 / 4`. Step 6 bounds density by squared expected absolute edges. The previously proved actual-matrix expected-edge estimate bounds that expectation by `prefixMean^2 * tailCollisionFactor / 2`. Nonnegativity follows from expected nonnegative counts, or from the proved nonnegative tail factor, so the square comparison is valid. Ring algebra gives the exact coefficient 1/4. This is valid for all N, including N=0 and N=1, and requires no new legality hypothesis.

10. **Actual matrix mean bound for arbitrary shifts.** Under the same feasible matrix data and arbitrary shift, step 7 and the proved exact expected occupancy formula give relative density at most `prefixMean`. Again there is no N≥2, legal-prefix, or shift-independence premise.

11–12. **Actual relative-overlap wrappers.** If named overlap inequalities are desired, step 8 converts steps 9 and 10 respectively into bounds for the expected intersection of two independently shifted actual-matrix internal-edge sets. These are immediate exact corollaries with the same parameters and shifts; no new probabilistic lemma is required.

13. **Ambient-relative exact exponent bound.** Use precisely the frozen X.09 data: feasible n, A<=M<=K, deterministic w and x with pointwise prefix extension, arbitrary real b, N≥2, and source legality of x. Set the shift to the computed ambientLeft for w. Step 9 and the already proved exact mean identity and square-tail comparison give

   `D_rel <= N^(4*(L+epsilon_w)+2*E)/4`.

   Here L, epsilon_w, and E retain the existing frozen definitions. The fixed-count tail factor can be zero; only its nonnegativity and the proved upper bound by N^E are used. Positive means and base conditions are derived from the existing lemmas. In particular no density-invariance rewrite from X.09 is available or needed.

14–15. **Both ambient-relative small-size consequences.** Append the exact branch premise `L<2*delta` with arbitrary real delta. Positive-base exponent monotonicity then gives, respectively,

   `D_rel <= N^(2*E+8*delta+4*epsilon_w)/4`,

   `D_rel <= N^(2*L+2*E+4*delta+4*epsilon_w)/4`.

   These are local consequences of `4*L<=8*delta` and `4*L<=2*L+4*delta`; they use no sign on epsilon_w and do not replace the branch condition by one involving L+epsilon_w. The singleton-shaped inequality is valid for every legal prefix satisfying the numerical cutoff, without a stable-singleton predicate.

16. **Ambient-relative size exponent bound.** Step 10 and the existing exact mean identity give `D_rel<=N^(L+epsilon_w)` on the same X.09 data, with no small-size premise.

17. **Ambient-relative terminal specialization.** Specialize step 16 to M=K, with the frozen full-length legality and ambient extension data. The existing tail exponent lemma supplies E=0 separately for this case. No small-mean premise is required, and the error remains epsilon_w with coefficient one.

The named-overlap wrappers and step 5 can be kept as explicit useful interfaces or eliminated by local composition; neither choice affects the mathematical assumptions. Every selected declaration must be included in the exact statement inventory before implementation. A vector-prefix adapter for step 3 or 4 is also an immediate local proof using `List.prefix_iff_getElem`, the existing prefix-word length identity, and the pointwise extension relation; it does not require a new theorem unless the final inventory chooses to expose one.

## All-size and shift cases

- For N=0 or N=1, `range(N-1)` is empty, so every relative set, relative density, and shared-relative-edge count is zero for every shift. The generic and finite matrix statements include these cases. Only exponent conversion retains its already frozen N≥2 domain.
- A shift zero returns precisely the absolute internal-edge set. A shift at least N-1 produces no relative edge. Intermediate shifts may discard absolute edges before the shift; this is why the arbitrary-shift statement is an inequality.
- For the computed ambient cut and w prefix x, step 3 rules out all such discarded child edges. Empty ambient or child cylinders, terminal prefixes, and ambient=child remain included. The case w=[] has cut zero and the original whole-deck coordinates.
- Defining the relative set by the additive membership test avoids the noninjectivity of truncated natural subtraction on indices before the shift. Subtraction appears only in the inverse proof after its required lower bound has been proved.
- The fixed support remains `range(N-1)` even when ambient occupancy is random. Larger indices have zero membership probability; no random support is needed in finite sums or the two-copy intersection formula.
- No prefix selection is adaptive in the source exponent corollaries. The shift may depend on the sample, but w, x, and n remain deterministic inputs to the same original-N law. Selecting a random ambient prefix or conditioning an exploration law would be a further obligation.

## Limits and dependency verdict

Preservation of an edge cardinality in each sample does not preserve squared edge-location density. For example, a two-outcome sorted-row law may place the same child edge at two different absolute locations while its computed ambient cut recenters both to zero; the sum of squared probabilities then increases. Conversely a generic random shift can spread an absolute edge over different relative positions. Neither density equality nor an ordering between the two densities is used here.

The dependency chain is relative support and injection -> finite-law density inequalities -> existing actual-matrix expected counts -> exact finite mean/tail bounds -> existing exponent identities and monotonicity. The source-fidelity branch uses the already constructed lexicographic sorting -> ambient cut lower bound -> exact child-edge count preservation. The overlap branch uses the existing fully constructed two-copy product law and finite intersection identity. These branches need no concentration, anti-concentration, profile asymptotics, or new axiom.

This transfer removes the previously explicit absolute-versus-relative-coordinate limitation for the finite mean/tail and source-exponent bounds, once the reviewed statements are proved. It does not establish the stronger printed minus-cF density estimate, per-edge stable localization, endpoint concentration, or the upper first-moment aggregation. At the whole-deck root the shift is zero, so recentering cannot resolve the already identified root-level obstruction to those stronger spatial statements.

## Final-signature comparison and acceptance

After completing the independent reconstruction above, I read the complete `relative_contract_statements.md` and `relative_contract_assumptions.md`. I compared every definition body R.D01–R.D03 and every ordered parameter list and conclusion R.01–R.18 with the permitted sources and the mathematical routes above. **I accept the selected three definitions and eighteen exact theorem signatures with no remaining pre-freeze correction.** No Lean code was written in this review and no prior frozen artifact was edited.

R.D01 uses the correct additive coordinate map on the fixed natural edge range; R.D02 takes the sum of the squared probabilities for these actual shifted sets with an unrestricted sample-dependent shift; R.D03 is precisely the strict lexicographic left cut with the source offset established above. There is no second law, random support, density-invariance assertion, or hidden subtraction convention.

R.01–R.05 are valid on their full generic domains. Support and the translation injection require no sorting. The zero-shift edge identity follows from the existing absolute support, the ambient-left size bound follows from filter cardinality, and the root cut vanishes because the empty list is least. R.06 and R.07 use exactly the actual constructed sorted matrix and arbitrary lists with their ordinary prefix relation. The sorting and containment needed for the inverse are proved as described above; omitting feasibility, legality, length bounds, and population positivity is valid. Impossible edge-membership cases at N=0 or N=1 do not lead to an invalid finite index.

R.08–R.11 preserve all finite laws and arbitrary per-sample shifts. The square comparison uses derived nonnegative expectations; the occupancy bound uses the already proved edge-to-occupancy injection; zero-shift density equality uses R.02; the two-copy overlap evaluates the shift separately at each independently sampled outcome. These statements impose no independence between a graph and its own shift and do not identify independently recentered overlap with absolute overlap.

R.12 and R.13 retain the full all-N feasible-matrix domain and arbitrary shift, with no legality or positivity premise. Their conclusions have the exact existing mean and tail factors and coefficient 1/4. They follow through the expected absolute counts, never through a comparison of the two densities. R.14–R.17 use the unchanged frozen X.09–X.12 vector domain and the explicit computed ambient-left function. They retain `4*(L+epsilon)+2*E`, the two source cutoffs `L<2*delta`, the signed errors with coefficient four, the mean exponent `L+epsilon`, and every denominator exactly. R.18 has the frozen full-length X.14 domain and is the literal terminal specialization; X.13 remains the already proved E=0 statement.

The selected eighteen-item layout is a complete pre-freeze decomposition of the independent route above. It omits the separate density-at-most-expected-absolute-edges wrapper and the two duplicate actual-overlap inequalities, all of which remain local compositions of the selected generic results. It exposes four useful direct checks instead: zero-shift edge equality, ambient-left at most deck size, empty-word cut zero, and zero-shift density equality. Every added check is proved directly from definitions and trusted finite/list-order facts, with no new hypothesis or helper declaration. The generic overlap identity already turns both actual matrix bounds into the required independently recentered overlap bounds by rewriting.

I accept the exact four-module plan: Relative.Model for three definitions, Relative.Deck for R.01–R.07, Relative.Density for R.08–R.13, and Relative.Estimates for R.14–R.18. The source-fidelity branch and the probability branch are acyclic and require no additional named lemma or instance. The valid whole-ambient interpretation is supplied by R.06–R.07 together with the existing pointwise vector-prefix relation, not by an assumed endpoint interface. No concentration, profile limit, conditional exploration, adaptive-prefix, or minus-cF spatial estimate is inferred by this acceptance.
