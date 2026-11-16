# Proof structure and dependency inventory

This document records the proof in the three authorized sources. An arrow means
a mathematical dependency, not an already checked Lean import. The original
sources are unchanged. The commented-out lower-bound overview at TeX lines
2564–2785 is historical material, not a second active proof.

## Whole proof

1. **Common model.** Deterministic integer column counts, their normalized
   simplex points, independent uniform fixed-count columns, legal words and
   prefix cylinders, lexicographic intervals, and the shuffle graph. One-row
   probabilities factor over columns; rows within a column are not independent.
2. **Macroscopic data.** One-column maximum cost `a`, power-sum cost `ψ`, tilted
   cost `I` and entropy `H`; the time profile; interval costs `A`, `B`, `J`;
   regular simplex partitions; almost-like cell counts; local good columns.
3. **Upper bound.** Graph representation → truncated second moment + sparse
   graph factorial bound. The needed shared-edge exponential moment comes from
   directional exploration + conditional first moment + conditional preservation
   + a Portenko argument. The unconditional first moment is obtained by:
   boundary crossings → admissible boundary pairs → stable prefix partition →
   profile estimates and bad-profile reduction → endpoint localization and
   edge-density estimates → numerical margin inequalities → summation over
   retained classes. Recursive first-moment margins permit this argument in
   accessible ambient blocks. Global buffered margins imply recursive margins;
   monotonicity gives the upper critical time. The one-column inequality
   `ψ_p(θ) ≥ (θ−1)a_p` reduces four margins to `Λ₀, Λ₁`.
4. **Lower bound, largest prefix.** Maximum-pile cost replacement → expected
   size of the word following maximal piles → successive hypergeometric thinning
   → a long increasing run after component sorting → an event rare under the
   uniform permutation.
5. **Lower bound, cold spots.** Positive `Λ₁` with small `Λ₀` → entropy
   inequalities and a buffered witness `(s,u,θ)` → truncated tilted prefix and
   tail types → relative cold-set geometry. Relative endpoint concentration and
   two good bridge columns localize collision-likely strings. Fixed-column and
   conditional factorial moments → occupancy and covariance bounds → many
   distinct cold edges. The translate-scan ascent test and component comparison
   separate the shuffle law from uniform. The two branches give the active
   buffered reduced lower theorem.
6. **Random pile sizes.** For the upper bound, condition on typical cuts and
   use uniformity of the deterministic bound; total variation is convex under
   mixing. For the lower bound, averaging conditional total-variation lower
   bounds alone is insufficient. The historical sketch and the homogeneous
   paper use a union of deterministic tests, a bound
   `(N+1)^(kK) = exp(O((log N)^2))` on integer cut sequences, and uniformly
   stretched-exponential false-positive bounds. The active lower theorem in
   this TeX is deterministic; a random-cut lower extension still needs that
   uniform testing argument stated and proved.

## Assigned part

| Input | Estimate | Consumers |
|---|---|---|
| χ-regular cell definition, cell membership | Representative costs; good digit mass >χ; exceptional mass ≤3χ | All profile estimates; tilted lower-bound types |
| Grid cell-count discrepancy, endpoint counting, finite additivity | Arbitrary interval blocking | Tail `c_E`; maximum cost; entropy correction; lower-bound types |
| Legal selected digits, good/exceptional split, representative error | Exact `c_L` decomposition and controlled error | Numerical large/small-block exponents |
| Power-sum representative costs, interval replacement | Tail `c_E≈−B₂` | Edge-density/numerical/terminal estimates |
| Selected digit ≤ maximum digit, maximum-cost replacement | `c_L(v)≤b−A(r,s)+error` | Numerical lemma; accessible exponents; largest-prefix lower bound |
| Genuine left/right crossings, product prefix masses | Side mass ≥χ·prefix mass; fluctuation comparison | Stable stopping; numerical lemma; endpoint arguments |
| Parent stopping inequality, nonnegative exceptional cost, bounded good last digit | Parent-crossing upper bound for `S_x` | Small non-singleton numerical exponent |
| Finite KL inequality, representative tilted weights | Cell entropy upper bound | Entropy of all good-digit types |
| Bounded `ψ`, number of exceptional positions, interval replacement | Entropy loss after exceptional removal | `H_x≤θS_x−Bθ+error` |
| Finite word probabilities, small boundary piles, weighted subset tail | Admissibility truncation | Retained boundary decomposition; discarded-edge mass |
| Exceptional mass ≤3χ, weighted subset tail | Exceptional-profile truncation | Retained first moment |
| Sparse pattern count, boundary encoding, bounded integer count arrays | Number of retained profile classes | First-moment class union bound; conditioning bookkeeping |

## Necessary prior formal definitions

No checked project definition was present at initial inventory. Other work is
creating tooling in this shared workspace; none of its mathematical outputs
was imported or presumed proved in the finite core. A later inventory of the
newly available definitions is in `PROJECT_INTERFACES.md`. The required
interfaces are:

- A fixed-count shuffle model with column independence, a row-marginal product
  formula, prefix-cylinder sets, and the expectation/cardinality identity.
- A finite simplex including zero coordinates; power-sum cost and tilted laws
  restricted to positive support; entropy using the `0 log 0 = 0` convention.
- Legal prefixes and extension/restriction, actual prefix lengths, ambient
  prefixes, boundary stopping families, left/right side cylinders, stable
  stopping, and graph edge cardinalities.
- A time-profile representation for which the displayed time integrals are
  defined and additive; regular partitions; grid and arbitrary interval counts.
- Explicit asymptotic quantifiers, with χ and its finite partition fixed before
  the final limit in N. A bound `o_χ(1)` is not an `o_N(1)` bound.

These are dependencies, not axioms to add. A deterministic finite-sum module
can establish useful estimates before stochastic and analytic interfaces exist.

## Source audit relevant to freezing

- TeX 322–327 and 500–507 use different lower summation indices for `c_L`.
  The detailed definition uses the actual ambient length `M_w`. Merely knowing
  `M_w/log N=r+o(1)` does not justify shifting sums of unbounded digit costs.
- The ambient length is asymptotic, so exact assertions `r≤s` or `s=T` at a
  terminal word require endpoint-error bookkeeping. They cannot be silently
  converted into equalities in Lean.
- TeX 722–724 records exceptional positions only. Homogeneous Definition 4.7,
  PDF page 23, records positions **and digit values**. Thus the later claim that
  a coarse class has size `N^(H_x+o_N(1))` misses a possible factor
  `k^|Q_x|`. Keep the literal coarse profile; if needed, introduce a separately
  named labelled refinement and prove its relation to the coarse profile.
- The unweighted high-exception count asserted at TeX 1103–1105 is false.
  A weighted binomial/generating-function bound proves the required small mass
  without that assertion. Expected interval mass includes the factor N.
- Time measurability of `μ_t` is not stated. The user has been asked whether a
  measurable probability kernel is the intended interpretation, before any
  analytic assumptions are frozen.
- The assigned fluctuation comparison is a product-mass comparison. It does not
  by itself justify the later anti-concentration theorem. In particular the new
  definition includes the first, fixed-count column; a one-digit prefix can
  have deterministic endpoints and a positive defined fluctuation exponent.

The map records proposed dependencies, not a certification of the whole sketch.
