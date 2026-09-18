# Independent adversarial review: time and digit profiles

This review was prepared independently from the three authorized mathematical sources. It uses the unified article and the derived text of `2103.05068v3.pdf` and `2510.22783v1.pdf`; no other agent's report was read. It is a pre-freeze review, not a proof certificate. No Lean code or additional axiom is proposed here.

## Principal findings

1. The finite arithmetic of the numerical first-moment lemma is sound. With the precise finite hypotheses below, a common error bound `ε` gives an error at most `14 ε`. Consequently `ε ≤ η/28` gives a residual margin `η/2`, provided the stability error is also at most `ε`.
2. The source's time profile is an arbitrary family of probability measures. The measurability needed to interpret its time integrals is unstated. A kernel or explicit integrability is necessary for measure-theoretic theorems; it cannot be silently supplied by Lean's totalized integral.
3. The initial and detailed ambient definitions differ. The detailed definition starts at the exact length `M_w` and is the sound one. Replacing that by `floor(r log N)` can create an order-one exponent error, even when the lengths differ by one.
4. The source's definition of a full digit profile records exceptional locations but not exceptional digit values. This does not determine `Q_x`. The homogeneous paper's Definition 4.7 does record `(time, digit)` pairs. Preserve the unified definition if desired, but do not prove false profile-invariance claims about `Q_x` or exact `c_L` from it.
5. Most seriously, the unified `c_F` includes the first column, whose pile counts are deterministic. It is a valid finite side-mass functional, but it is not always a fluctuation exponent. The article's later anti-concentration statement has a concrete counterexample. The assigned deterministic layer can preserve this definition; it must not claim to certify that probabilistic interpretation.

## Source locations and comparison

The relevant unified definitions are `eq:probability-simplex`, `eq:one-column-costs`, `eq:profile-costs`, `eq:integrated-profile-costs`, `def:almost-time-profile-like-cuts`, `def:chi-regular-partitions`, `def:ambient-block-size-exponent`, `def:boundary-pairs-stable-blocks`, `def:space-time-digit-profile`, and `def:numerical-first-moment-margin`. The principal claims audited are `lem:ub-regular-partition-interval-blocking`, `lem:ub-profile-estimates`, and `lem:ub-numerical-lemma`.

In `2510.22783v1.pdf`, the corresponding material is the simplex decomposition (2.1), scale hierarchy (2.9), Definition 4.3 and the `c_F` formulas of Section 4.1, Definition 4.7, Lemma 4.8, and Lemma 4.16. Definition 4.7 explicitly includes exceptional `(t,x[t])` pairs. The maxima defining left and right fluctuations in Section 4.1 start at `i=2`, excluding the first deterministic column. In `2103.05068v3.pdf`, Section 4.1.2 defines zero-total entropy as zero, Proposition 4.2 gives the multinomial entropy estimate, and the proof of Lemma 4.9 uses the finite relative-entropy inequality. That older paper assumes all fixed pile probabilities positive; this must not be imported as an assumption for the present closed simplex.

## Exact counterexamples and non-counterexamples

### Missing time measurability

Let `V ⊂ [0,T]` be non-Lebesgue-measurable. Let `e₀` be a simplex vertex and `u` the uniform vector. Set `μ_t = δ_{e₀}` on `V` and `μ_t = δ_u` elsewhere. Every `μ_t` is a probability measure as required literally by the setup, but `a(t)` is zero on `V` and `log k` off `V`. It is not measurable. Likewise a cell separating `e₀` and `u` has a nonmeasurable time-dependent mass.

The source's integrals have no ordinary integrable interpretation in this example. A finite partition theorem can use integrable cell-mass functions. The complete cost-integral layer needs an appropriate measurable kernel or explicit measurable/integrable cost functions. These are well-definedness requirements, but they must be stated and approved before freezing, not silently added afterward.

### An ambient index discrepancy is not a negligible digit cost

Suppose `M_w = floor(r log N)+1`, and the extra ambient-prefix digit lies in a pile of size one. Then its normalized logarithmic cost is

`log(N/1)/log N = 1`.

The initial formula that starts at `floor(r log N)` counts this digit again, while the detailed formula that starts at `M_w` does not. The discrepancy is one, not a quantity tending to zero. An `O(1)` length error only yields `o(1)` cost on uniformly positive pile probabilities; such positivity is unavailable for arbitrary legal digits.

The detailed formula from `def:ambient-block-size-exponent` is sound. An exact finite model should set the discrete birth time to `M_w/log N`. An asymptotic ambient time `r` should be accompanied by the explicit discrepancy `|M_w/log N-r|`. The bounded maximal-pile cost can absorb this time discrepancy, whereas an individual legal-digit logarithmic cost cannot.

### Exceptional locations do not determine exceptional cost

For `k=3`, consider a column with probabilities

`(1-χ-1/N, χ, 1/N)`,

where `χ` is a small positive rational and `N` is a large multiple of its denominator, so all pile sizes are integers. A regular cell can have both its second and third representative coordinates at most `2χ`. A word using digit 1 at a given exceptional location and a word using digit 2 there have the same good counts and exceptional location set. Their contributions to `Q_x` are respectively `log(1/χ)/log N` and `1`.

Repeating this over exceptional locations preserves the same declared coarse profile while making `Q_x` differ substantially. The elementary digit estimates are still true for each word. What fails is any assertion that the unified profile data determine `Q_x` or exact `c_L`. There is no uniform small bound on `Q_x` solely from `R_x ≤ α_χ`: legal probabilities may be `1/N`. The correct counting refinement, present in the homogeneous paper, separately records the exceptional digit labels.

### Deterministic first-column mass is not fluctuation

Take `k=3`, `N=3^(2m)`, deterministic equal piles in every column, and the whole deck as ambient block. Choose `χ<1/3`. The unified left and right boundary prefixes can both be `y=z=(1)`, with genuine crossings at the first column. Both first-column side-piece masses are exactly `N/3`. The unified definition therefore gives

`c_F = (1/2) log_N(N/3) = 1/2 - 1/(4m)`.

For every continuation `x=(1,0,...,0)`, the left endpoint of its lexicographic block is deterministically `N/3+1`: there are exactly `N/3` rows with first digit zero, and within first digit one there is no lexicographic word below the all-zero suffix. The source's interval convention preserves this endpoint even when the block is empty.

For any fixed sufficiently small stability threshold `δ>0`, choose the first length `ℓ` such that

`c_L(x)-c_F = 1/2+(1-2ℓ)/(4m) < δ`.

This is a nonterminal, admissible stable block for a sufficiently long sequence. Every digit is good, `c_L(x)` is approximately `1/2+δ`, and `c_F` is approximately `1/2`. Nevertheless its left endpoint has point mass one. Thus the claimed later endpoint anti-concentration bound of order `N^(-c_F+O(δ)+o(1))` is false. Equal piles and a long enough time satisfy the numerical margin; this counterexample is not eliminated by that margin.

The finite definition of `c_F`, its continuation invariance, and the side-mass comparison with `c_L` remain true. The implication from expected side mass to actual variance or anti-concentration does not. `2510.22783v1.pdf` excludes the first column in its corresponding boundary and fluctuation definitions.

### Terminal scaled time is not the macroscopic endpoint

If `K=floor(T log N)`, then a terminal word has time `K/log N`, not exactly `T`. The numerical proof's sentence “then ... `s=T`” is generally false. The true bound is

`0 ≤ T-K/log N < 1/log N`.

Since `a(p)≤log k` and `ψ_p(2)≤log k`, all needed integrated-cost endpoint corrections are at most `log k/log N`. This is an explicit correction, not an extra model hypothesis.

## Safe finite statements and exact hypotheses

### Simplex and one-column costs

The closed simplex should include zero coordinates. `k≥2` supplies a nonempty digit type. From nonnegative coordinates summing to one, derive `p_l≤1`, positivity of the maximum, and `p_max≥1/k`. For `θ≥1`, the finite power sum is positive; for the relevant ranges the costs satisfy

`0≤a(p)≤log k`,

`0≤ψ_p(θ)≤(θ-1)log k`.

These are sound on the closed simplex. No hypothesis that all coordinates are positive is justified or needed. Expressions involving an individual logarithm should either restrict to positive coordinates or use a declared zero-contribution convention. Lean's `Real.log 0=0` alone is not a proof that the original expression was meaningful.

The tilted probability and entropy identities are sound with zero-supported terms omitted and `θ≥1`; positive tilted weight implies positive original coordinate. They require a support argument when formalized.

### Time cells

A positive number of strictly increasing cells requires `T>0`. If `T=0` is admitted, use the empty time-cell family and the fact that there are no shuffle columns. Choose half-open cells, with the final right endpoint included, exactly as the source does. Their disjointness, union, and uniqueness of membership are finite order facts.

Require `N≥2` before dividing by `log N`. Use an explicit finite column type or an explicit range `1≤j≤K`; the set in the displayed almost-like definition relies on this contextual restriction.

### Regular partitions

The following implications are sound directly from the definition:

- Good representative digit: actual probability `>χ`, with logarithmic replacement error at most `Cχ`.
- Exceptional representative digit: actual probability at most `3χ`, exactly. No `o(1)` is required for deterministic normalized cuts.
- Representative replacement for `a` and `ψ` is uniformly bounded by `Cχ` on the indicated parameter interval.

The partition should store its constant `C` explicitly. A theorem claiming vanishing error as `χ→0` needs a construction with `C` independent of `χ` (it may depend on fixed `k`). An existential constant separately chosen at every `χ` would not justify such a claim.

A Borel partition with representatives and coordinate mesh at most `χ²` is sufficient when `0<χ<1/k`: good representatives have actual mass greater than `χ`; exceptional masses are at most `2χ+χ²≤3χ`; the log error on good coordinates is bounded by the coordinate error divided by `χ`. Compactness/finite quantization gives existence. The source's representative condition forces nonempty cells; remove empty cells rather than select a point from them.

### Almost-like cuts and interval blocking

The source uses closed grid intervals. Adjacent closed intervals may count an endpoint column twice. One may convert each to the desired half-open form at a cost of at most `1/log N`; simply treating the original grid intervals as disjoint is wrong.

For fixed `ρ>0`, let `G=ceil(T/ρ)` count grid blocks. A safe target for any interval `(a,b]⊂[0,T]` and one cell is an explicit bound such as

`4ρ + φT + (2G+4)/log N`.

This generous bound follows by removing at most two boundary blocks, summing the grid discrepancies, and accounting for shared endpoints. The exact constants may be tightened. For closed arbitrary intervals add an endpoint error if needed.

The measure contribution on discarded pieces is bounded by their length because every cell mass lies in `[0,1]`. Finite weighted summation must retain the number of partition cells or the sum of absolute representative weights. It is invalid to claim a constant uniform over arbitrary partition cardinality. The source hierarchy fixes the partition before `ρ,φ,N`, so an explicit partition-dependent factor is legitimate.

No time continuity assumption is needed: interval masses are integrated exactly. The time mesh parameter `Δ` is dispensable for the basic aggregate entropy/cost comparison because spatial representative weights do not depend on the time-cell index. One can sum time-cell counts first without multiplying the blocking error by the number of time cells.

### Ambient exponents and fluctuation quantities

For a legal word, all selected actual masses are positive. Thus each actual logarithmic cost is nonnegative, `c_L` is nonincreasing along extension, the parent increment is exact, and a split at an exact prefix length is exact. With an exact finite birth exponent, the expected-size identification is an equality; with an asymptotic birth exponent it carries precisely the stated birth-exponent error.

`c_E≤0` and `c_E=0` for a terminal prefix are sound. It depends only on length and the future columns.

For `c_F`, an empty side index set has maximum zero and logarithmic value minus infinity. This must be represented by an extended type, or the real-valued theorem must explicitly require positive left and right maxima. Terminal pairs may have zero maxima and must not enter a real-valued arithmetic lemma. Nonterminal genuine crossings guarantee positive side masses and the finite estimate

`c_F ≥ (1/2) log_N(expected prefix mass) + log χ/(2 log N)`.

The side pieces sum over all legal later digits; those probabilities sum to one. This proves continuation invariance. It does not prove a variance lower bound.

### Digit counts and entropy

For a word between exact prefix lengths `M_v≤M_x`, the nonnegative normalized good counts and exceptional count satisfy

`sum_{q,i,l} c_l^(q,i) + R_x = (M_x-M_v)/log N`.

`S_x,Q_x,R_x,H_x≥0` are sound. An empty cell contributes zero entropy. A positive good count has a representative probability greater than `2χ`, furnishing the support condition for relative entropy.

Let `Gcost_x` be the normalized sum of actual good-digit costs. Then

`|Gcost_x-S_x| ≤ Cχ · (# good positions)/log N`,

and hence

`|c_L(x)-(c_L(v)-S_x-Q_x)| ≤ Cχ · (M_x-M_v)/log N`.

These are uniform finite inequalities. There is no asymptotic remainder to introduce in this finite splitting step.

The Gibbs inequality gives, for every `θ∈[3,4]`,

`H_x ≤ θS_x - sum_{q,i} c_tot^(q,i) ψ_rep_i(θ)`.

This is sound even though only good coordinates have counts: compare with the full tilted law, using zero count on the other coordinates. The missing exceptional positions cost at most `3 log k · R_x` in replacing the last sum by all-column representative costs. Thus `R_x≤α_χ` yields an explicit entropy loss `3 log k · α_χ`, without any bound on `Q_x`.

The parent-crossing estimate requires a bounded last *good* cost. Adding a good final digit changes `S_x` by at most `log(1/(2χ))/log N`; adding an exceptional digit changes it by zero. Do not use `O(1/log N)` with a constant independent of `χ`. The source fixes `χ` before `N`, so the explicit bound tends to zero in the intended order.

## Numerical algebra with explicit errors

Write `L=c_L(x)`, `V=c_L(v)`, `F=c_F(x)=c_F(v)`, `E=c_E(x)`, `H=H_x`, `S=S_x`, `Q=Q_x`, `β=β_(r,b)(s)`, `B=B_θ(s,u)`, and `D=B_2(u,T)`. All are real; this excludes the terminal minus-infinity case from these two branches. Let `θ∈[3,4]` and all named error bounds be nonnegative.

Assume

`L≤V-S-Q+e_L`, `V≤β+e_V`, `F≥V/2-e_F`, `Q≥0`,

`H≤θS-B+e_H`, `E≤-D+e_E`.

For the large branch also assume `L-F≤δ`. Then direct algebra gives

`4L-F+2E+H ≤ ((θ+3)/2)β-B-2D`

` + θe_L + ((θ+3)/2)e_V + (θ-3)e_F + (4-θ)δ + e_H + 2e_E`.

The signs `θ≥0`, `3-θ≤0`, and `4-θ≥0` are essential and are exactly supplied by `[3,4]`. In particular this argument uses an upper error bound on `L`; the full absolute error is more than necessary.

For the small nonsingleton branch replace the stability inequality by the parent-derived bound `S≤V-F+e_S`. Then

`-F+2E+H ≤ ((θ-1)/2)β-B-2D`

` + ((θ-1)/2)e_V + (θ+1)e_F + θe_S + e_H + 2e_E`.

If all listed errors and `δ` are at most `ε`, each complete error is at most `14ε` (large: at most `13.5ε`; small: at most `13.5ε`). Thus `ε≤η/28` and the corresponding infimum margin at most `-η` yield an upper bound of `-η/2`.

For a singleton, simply use `L≤β+e_V` and `E≤-B_2(s,T)+e_E`, yielding the singleton margin plus `e_V+e_E`. A terminal singleton needs the bounded endpoint correction described above.

For terminal-fallback exclusion, `L≤-η+e_T` and `F≥L/2-e_F` imply

`L-F≤-η/2+e_T/2+e_F`.

If this is strictly less than the positive stopping threshold, fallback is impossible. The argument is sound with these explicit inequalities.

Taking an infimum does not require silently postulating a minimizer. A near-minimizer with explicit tolerance is enough, or the common lower bound supplied by the already-proved target inequality permits a greatest-lower-bound argument. Continuity and compactness may prove attainment separately; they must not be assumed without proof. The infimum's parameter set `[3,4]` is nonempty.

## Quantifier and dependency requirements

All eventual conclusions must expose their order: fixed `k,T,η` and other macroscopic parameters; choose `χ` and its partition with a uniform regularity constant; then choose errors such as `ρ,φ` small relative to the fixed partition; finally choose one `N₀` so the finite inequalities hold for every `N≥N₀`, every allowed cut sequence, and every retained profile under consideration. Pointwise eventual bounds separately depending on each profile do not justify the numerical first-moment proposition.

The randomized extension needs a deterministic estimate uniform over all realized cut sequences on the good event. Pointwise convergence for each fixed deterministic sequence does not by itself allow averaging a triangular array. This uniformity belongs to the eventual deterministic theorem and must remain visible in the dependency map.

## Formalization status by proposed claim

| Claim family | Status | Mathematical character |
|---|---|---|
| Simplex coordinate bounds, maximum, positive power sum | Sound | Finite algebra/order |
| Cost bounds and logarithmic monotonicity | Sound with stated domains | Finite real analysis |
| Time-cell partition and unique membership | Sound with endpoint/empty-horizon convention | Finite order |
| Regular-cell good/exceptional consequences | Sound with explicit `C,χ` | Finite real analysis |
| Uniform regular partition existence | Sound construction route; prove it, do not assume mesh constants | Compactness/Borel analysis |
| Grid-to-arbitrary-interval blocking | Sound with explicit endpoint and cardinality errors, integrable cell masses | Finite counting plus integration |
| Exact ambient exponent splits and monotonicity | Sound using `M_w` and legal digits | Finite sums/logarithms |
| Expected-size identification | Sound under the specified shuffle law; not a bare definition | Finite probability |
| `c_E` sign and terminal value | Sound | Finite sums |
| `c_F` side-mass definition/invariance/empty convention | Sound | Finite weighted cylinders |
| `c_F` lower bound from boundary crossings | Sound as an expected-side-mass inequality | Finite probability/logarithms |
| `c_F` as actual variance/anti-concentration scale | False as currently stated | Probabilistic blocker |
| Good counts plus exceptional counts sum to length | Sound | Finite counting |
| `S,Q,R,H` definitions/nonnegativity | Sound with support and zero conventions | Finite analysis |
| `Q` determined by unified coarse profile | False | Finite counterexample |
| Exact profile cost replacement | Sound with explicit uniform error | Finite sums |
| Weighted entropy/Gibbs bound | Sound on good-count support | Finite convex analysis |
| Entropy and tail passage to macroscopic integrals | Needs the unstated measurability condition to be resolved | Measure theory |
| Parent-crossing bound | Sound with explicit `log(1/(2χ))/log N` | Finite order/algebra |
| Numerical margin definitions and finite numerical lemma | Sound with real-valued branch and explicit errors | Real order/algebra |
| Uniform asymptotic numerical corollary | Sound once its uniform finite inputs are proved | Quantified analysis |
| Full first moment and random-pile mixing extension | Not certified by this layer; depends on the false/unproved probabilistic inputs above | Probability |
