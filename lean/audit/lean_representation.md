# Independent Lean probability representation review

Status: review and proposed interfaces only; no Lean implementation or frozen statement is contained in this report. The root agent must compare the independent reports before freezing. Mathematical sources read: `time_inhomogeneous_riffle_shuffle_unified_article.tex`, `2103.05068v3.pdf`, and `2510.22783v1.pdf`, including text extracted directly from those PDFs. Trusted implementation infrastructure inspected: the mathlib v4.19.0 checkout at `formalization/.tooling/mathlib`. No other mathematical project document was read.

## Recommendation

Use a finite mass function for the analytic hypergeometric core, a uniform finite-subset model to establish its sampling interpretation, and finite supported fibres for conditioning. Bridge these to mathlib `PMF` and its associated measure. Do not begin with regular conditional kernels or arbitrary sigma algebras: every fixed-column shuffle in the supplied sources has a finite sample space, and a reveal map records all required information exactly.

The paper's upper section uses `Hyp(successes, population, draws)` while the lower labelled-thinning section uses `Hyp(population, successes, draws)`. Use named parameter fields and never positional notation with three anonymous naturals. The upper prose also omits independence between the two uniformly chosen sets; the old fixed-column paper explicitly includes independence. A fixed marked set intersected with one uniform random subset avoids this ambiguity entirely.

## Exact finite core to freeze

Use parameters consisting of natural numbers `population`, `marked`, and `draws`, with validity proofs `marked ≤ population` and `draws ≤ population`. These are the definition of a feasible finite population experiment, not assumptions inserted to make a proof easier.

For brevity write these parameters as `N`, `K`, and `m`. The finite outcome type is `Fin (m + 1)`. For an outcome whose value is `q`, its real probability is

`choose K q * choose (N - K) (m - q) / choose N m`,

where the binomial coefficients are first natural numbers and then cast to the reals. Since `q ≤ m`, natural subtraction is legitimate. The validity assumptions give `choose N m > 0`. Values outside the true support automatically have weight zero. On `ℕ`, the same formula needs an explicit guard `q ≤ m`; otherwise natural truncated subtraction incorrectly gives positive weights when `q > m`.

The following proposed exact statements individually pass this representation review:

1. **Normalization:** the sum of these weights over `Fin (m + 1)` is one, and each weight is nonnegative.
2. **Expectation:** the finite weighted sum of `q` is `(K : ℝ) * m / N`, for every valid parameter, including `N = 0`.
3. **Second factorial moment:** the weighted sum of `q * (q - 1)` is `K * (K - 1) * m * (m - 1) / (N * (N - 1))`, with all differences inside natural-number factors before casting. This identity is total and zero in every degenerate case; the real expression for `q * (q - 1)` agrees on natural outcomes.
4. **Variance:** the weighted centered square is `K * m * (N - K) * (N - m) / (N^2 * (N - 1))`, with natural differences before casting. For `N ≤ 1` both sides are zero. For `N ≥ 2` this is exactly the displayed variance in the sketch.
5. **Zero-variance characterization:** variance is zero exactly when `K = 0`, `m = 0`, `K = N`, or `m = N`. These alternatives include both `N = 0` and `N = 1`.
6. **Concentration:** there exists an absolute positive real `c` such that for every valid parameter and every real `t ≥ 0`, the finite probability of `abs (q - mean) ≥ t` is at most `2 * exp (-c * min (t^2 / (mean + t)) t)`. At `mean = t = 0`, use Lean's total real division explicitly: the ratio is zero and the bound is `1 ≤ 2`. For positive `t` and zero mean the tail event has probability zero. No positive-mean hypothesis is necessary or permissible.
7. **Point-mass anti-concentration:** there exists an absolute positive real `C` such that, for every valid parameter with `0 < variance` and every natural `q`, the mass at `q` is at most `C / sqrt variance`. For `q > m` the mass is zero. Keep the positive-variance condition: the theorem is false with a finite inverse-standard-deviation expression interpreted as zero at zero variance. Degenerate laws are dealt with by the separate exact statements above.

These are proposed statements, not proved statements. In particular a definition must not bundle the concentration or anti-concentration bounds as fields of a purported hypergeometric model.

The normalization proof is Vandermonde. Expectation and factorial second moment are shifted Vandermonde identities, after moving one or two marked distinguished labels outside the choice. Variance follows from the second factorial moment plus the first moment minus its square, separating `N = 0`, `N = 1`, and `N ≥ 2` before division cancellation.

## Sampling semantics

For a population finset `V` and `m ≤ V.card`, use `PMF.uniformOfFinset (V.powersetCard m) ...`; its outcomes are finsets. Fix marked `A ⊆ V` and map an outcome `S` to `(A ∩ S).card`. The desired bridge states that its law is the mass function above with `N = V.card` and `K = A.card`. Counting each fibre uses the bijection

`S ↔ (S ∩ A, S \ A)`

between draws with intersection size `q` and independent *combinatorial choices* of `q` marked and `m - q` unmarked labels. This proof should precede any use of the formulas for actual shuffle counts.

A uniform pair of independent subsets yields the same law by conditioning on the marked subset, but that construction adds a layer of randomness and is unnecessary for the assigned core.

Empty populations are supported: `V.powersetCard 0 = {∅}` is nonempty even if `V = ∅`. Do not construct a uniform measure on `Fin N`; that would wrongly require `N > 0`. Construct a uniform measure on the space of legal subsets instead.

## Conditioning representation

Let `p : PMF Ω`, with finite `Ω`, and let `Z : Ω → Γ` be a finite reveal map. For a realized value `z`, the supported-fibre witness is

`∃ ω, Z ω = z ∧ ω ∈ p.support`.

Exactly this witness gives `p.filter {ω | Z ω = z} ...`. Compose with the random count `Y : Ω → ℕ` using `PMF.map`. A conditional-hypergeometric law is an equality between that mapped filtered PMF and the previously defined hypergeometric PMF at parameters determined by `z`. Quantify only over supported fibres. Null fibres have no normalized probability law; do not state pointwise probability identities there.

A convenient alternative interface avoids explicit conditional PMFs. Give the reveal marginal `pZ : PMF Γ` and a probability kernel `κ : Γ → PMF ℕ` satisfying the exact factorization

`law (Z,Y) = pZ.bind (fun z => (κ z).map (fun y => (z,y)))`.

On supported `z`, prove `κ z = hypergeom (parameters z)`. On unsupported values `κ` may be assigned any total value; no conclusion depends on it. This formulation is especially convenient for averaging conditional concentration and for random-pile mixtures.

Each of the following planned conditional lemmas needs its own proof, not a new hypothesis on the final shuffle model:

1. **Residual fixed-column uniformity:** condition a uniform fixed-count column on prescribed symbols on a fixed row set `R`. For every supported/admissible prescription, the remaining assignment is uniform with counts `n_l - r_l` and population size `N - |R|`. All inequalities making the natural subtractions legal are derived from admissibility.
2. **Column independence after factorized prescriptions:** independence survives because the conditioning event is the product of one event per column. Arbitrary exploration information need not factorize and does not automatically preserve independence.
3. **Single-column conditional count:** after revealing all other columns and a fixed row subset in the remaining column, the count on a disjoint unrevealed test set has law `Hyp(N - |R|, residual-marked, |A|)`. The test set must be measurable from the reveal and disjoint from `R`.
4. **Successive thinning:** for a deterministic target word, past survivor set `S` and an independent next uniform pile of size `m`, the next survivor count has law `Hyp(N, |S|, m)`. The population is the full labelled population `N`, not `|S|`.
5. **Conditional moment and tail transfer:** apply already proved law formulas on each supported fibre and sum over the reveal marginal. If thresholds depend on the reveal, they become deterministic on each fibre.
6. **Coarsening for endpoint masses:** if coarse information `U` is a function of finer reveal `Z` and an endpoint equals `a(Z) + Y`, integrate the finer conditional point-mass bound to obtain the coarse one. Measurability of the shift and the factorization `U = g ∘ Z` must be proved from the endpoint construction.

The event used to restrict an endpoint probability need not itself be measurable from the finer reveal if it is contained in a parameter-good event `Z ∈ G`. On a good fibre use the full conditional point-mass bound; restricting an event only decreases its probability. On a bad fibre the restricted event must be empty. This is the precise finite replacement for the sketch's informal sentence about realizations inside its good event.

## Full fixed-column space and random piles

A column with sizes `n : Fin k → ℕ` is the finite subtype of functions `Fin N → Fin k` having exactly `n l` occurrences of each digit, with `∑ l, n l = N`. Its probability is uniform on this subtype. A whole matrix is a finite product of these column spaces, with product law. Zero piles are allowed and a word using a zero pile has count exactly zero. If `N = 0`, there is one empty column assignment; there is no need to exclude it. Existence of the legal column space follows from the count sum, not a separately imposed nonemptiness assumption.

For random piles, the finite space of legal count arrays has an arbitrary PMF. Bind that PMF to the already defined conditional fixed-column law. The deterministic estimates transfer by averaging on the typical-pile event. No independence among random pile sizes should be added; the source permits a random sequence whose realized deterministic data satisfy the typical-event hypotheses.

## Non-exhaustion and ambient transfer: blocked as stated

The non-exhaustion claim in the ambient transfer lemma cannot be made true through a different probability representation. Its issue is mathematical. The original fixed-column proof (`2510.22783v1.pdf`, Lemma 4.5, pp. 20–22) uses reveal columns `u,v ≥ 2` and retains the full population `N`. Its first-digit block has size `N' ≤ (1 - χ)N`. The unused rows outside that block supply a strictly positive complementary sampling fraction.

The time-inhomogeneous sketch restricts the whole experiment to ambient population `B_w` and permits the fluctuation columns to equal `M_w + 1`. In its case `a = b = M_w + 1`, there is no preceding tail-prefix restriction. After the crossing-digit positions have been revealed,

`d2 = N_w - n_(x[a])^(a)`.

Thus the sample equals the complete residual population and the claimed second complementary fraction is exactly zero. Positive left and right pile sizes do not prevent this. Conditional `Y3` is then deterministic. Both boundary crossings can be genuine and nonterminal. Consequently the current proposed ambient non-exhaustion and anti-concentration statements must not be frozen as proved targets without first resolving this counterexample.

The following *arithmetic implication* is valid and useful but is not a replacement for proving non-exhaustion from the source hypotheses: if a valid hypergeometric parameter has mean at least `u > 0`, marked-complement fraction at least `a > 0`, and sample-complement fraction at least `b > 0`, its variance is at least `u*a*b`. These inequalities imply `N ≥ 2`, and the finite-population factor `N/(N-1)` is at least one. It is legitimate to freeze this as a standalone algebraic lemma; it is illegitimate to add its premises to the ambient theorem just to bypass the missing argument.

Similarly, a valid finite union-bound transfer lemma can be proved from actual one-step concentration laws. It does not establish the sketch's missing uniform control over conditional means. Counts with small means have only absolute upper bounds, not two-sided multiplicative comparisons; ratios must never be formed before verifying a strictly positive denominator.

## Verified mathlib v4.19.0 support

The following names and signatures were inspected directly:

- `Nat.add_choose_eq (m n k)`: Vandermonde over `Finset.antidiagonal k` in `Data/Nat/Choose/Vandermonde.lean`.
- `Nat.choose_mul (hkn : k ≤ n) (hsk : s ≤ k)`: `n.choose k * k.choose s = n.choose s * (n-s).choose (k-s)` in `Data/Nat/Choose/Basic.lean`.
- `Nat.succ_mul_choose_eq`, `Nat.choose_mul_succ_eq`, and `Nat.descFactorial_eq_factorial_mul_choose`, same file.
- `Finset.mem_powersetCard`, `Finset.card_powersetCard`, `Finset.powersetCard_nonempty`, and `Finset.powersetCard_nonempty_of_le` in `Data/Finset/Powerset.lean`.
- `PMF.uniformOfFinset`, `PMF.uniformOfFinset_apply`, `PMF.support_uniformOfFinset`, `PMF.toMeasure_uniformOfFinset_apply`, and `PMF.uniformOfFintype` in `Probability/Distributions/Uniform.lean`.
- `PMF.ofFintype`, `PMF.ofFinset`, `PMF.normalize`, `PMF.filter`, `PMF.filter_apply`, `PMF.support_filter`, `PMF.map`, `PMF.map_comp`, and `PMF.bind_map` in `Probability/ProbabilityMassFunction/Constructions.lean`.
- `PMF.bind`, `PMF.bind_apply`, `PMF.bind_bind`, and `PMF.bindOnSupport` in `Probability/ProbabilityMassFunction/Monad.lean`.
- `PMF.integral_eq_sum` in `Probability/ProbabilityMassFunction/Integrals.lean` converts a finite PMF expectation to its weighted finite sum.
- `ProbabilityTheory.variance_eq_integral` and `ProbabilityTheory.variance_def'` in `Probability/Variance.lean`. The latter requires `MemLp X 2 μ`; this is available automatically after proving boundedness on the finite sample space, but should be proved rather than inserted as a distributional assumption.

No hypergeometric probability distribution or without-replacement concentration comparison was found in the inspected mathlib `Probability` directory. `Analysis/SpecialFunctions/OrdinaryHypergeometric.lean` is about a special function and is unrelated to the probability law. The existing Hoeffding/Azuma material in `Probability/Moments/SubGaussian.lean` assumes sub-Gaussian moment bounds and independence or conditional sub-Gaussian bounds; it cannot be applied by declaring the within-column selection indicators independent. Generic Chernoff bounds are in `Probability/Moments/Basic.lean`, but the required hypergeometric exponential-moment estimate remains a project theorem to prove.

## Proof workload and alternatives

Expectation and variance are well matched to the finite binomial-coefficient law. Conditional subset uniformity is a finite bijection/counting proof. Conditional averaging and finite union bounds then involve finite sums only.

Concentration still requires an actual without-replacement comparison or a direct hypergeometric argument. Upper factorial-moment expansions are accessible from the moment identities; the lower tail cannot be justified by comparing alternating coefficients termwise. A finite convex-order comparison, or a direct mass-ratio proof, must be proved. The supplied lower-tail proof's Hoeffding comparison is not presently a verified imported mathlib theorem.

Point-mass anti-concentration still requires a real proof. The source's mass-ratio/Stirling route is one possibility. An alternative is an elementary universal bound for discrete log-concave laws followed by log-concavity of the hypergeometric mass function; that auxiliary theorem would itself require proof. A third route complements marked and sampled sets to reduce both fractions to at most one half, compares variance to the reduced mean, and uses local ratios near the mode. None of these should appear as an extra assumed structure field.

Before implementing either difficult analytic theorem, all proposed auxiliary statements must receive the same independent review and freezing process. If an auxiliary theorem is discovered to be false or to require stronger premises, stop and report that fact; do not amend the already frozen target silently.
