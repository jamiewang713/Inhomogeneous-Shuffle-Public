# LB-02 independent mathematical review, v1

Date: 2026-10-01. Scope: source and mathematical argument review before LB-02 dependent proof implementation. This report is the only file edited by this reviewer. No Lean proof, build, or axiom closure is certified here.

## Verdict and evidence boundary

The inspected LB-02 mathematical targets are valid on their frozen domains. I found no counterexample requiring a contract change. The all-positive-parameter transform, backward affine recursion, constants in all three tails, residual-law statement, polynomial all-prefix union bound, and uniform asymptotic quantifier order are mathematically sound. Their proof obligations remain substantive: neither a target `def ... : Prop` nor the LB-00 readiness receipt proves them.

I independently read the assigned prompt; manuscript lines 2975–3139, including `lem:successive-thinning-tail`, `cor:iterated-hypergeom`, and `prop:largest-prefix`; the exact bodies of `Contracts/v1/ModelThinning.lean`, `AdditionalFinite.lean`, and `AssemblyInputs.lean`; `Shared/Model.lean`, `Statistics.lean`, and relevant Empirical/Geometry definitions; canonical `TimeProfile` fixed-count definitions; the old hypergeometric concentration source; and the relevant old fixed-column and residual-sampling theorem statements and proof structure. I also read LB-00's readiness receipt and `OWNERSHIP.json` to distinguish frozen definitions from missing proofs. The old files were inspected as source, not imported or rebuilt with a new toolchain.

The manuscript SHA-256 is `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`, matching the prompt and LB-00 receipt. Other inspected file hashes are recorded below.

## Checked mathematical argument

### One-step transform for every s > 0

Fix integers `M > 0`, `0 ≤ x ≤ M`, and `0 ≤ m ≤ M`, a fixed marked set A of cardinality x, and a uniform m-element subset P of M labels. Put `V = |A ∩ P|` and `q = m/M`. Then

`E[s^V] ≤ (1-q+q*s)^x` for every `s > 0`.

The manuscript's symmetric-mean proof is correct. Sampling x distinct positions from m entries equal to s and M-m entries equal to 1 gives the transform. Averaging a largest and a smallest entry does not decrease the elementary symmetric polynomial: after isolating the two entries, it has the form `A*a*b + B*(a+b) + C` with nonnegative coefficients. The sum of squared deviations decreases by `(a-b)^2/2`, while its old value is at most `M*(a-b)^2`. Therefore the stated geometric contraction `1-1/(2M)` is valid. It implies coordinatewise convergence to the arithmetic mean; continuity supplies the limiting polynomial inequality. Cases x=0 and x=1 are equalities. The M=1 case is also harmless because the only list already is constant.

A more practical Lean route avoids this convergence argument. For `s ≥ 1`, put `u=s-1 ≥ 0` and use

`E[choose(V,r)] = choose(x,r) * (m)_r/(M)_r`,

`(m)_r/(M)_r ≤ (m/M)^r`,

and the finite binomial expansion of `(1+u)^V`. The coefficient signs are nonnegative. This is exactly the structure of the old private `expect_one_add_pow_le` proof. For `0 < s ≤ 1`, apply that positive-parameter result to `W=x-V`, whose law is `Hyp(M,x,M-m)`, at `1/s ≥ 1`, and multiply by `s^x`. The resulting base is exactly

`s * (1 + (1-q)*(1/s-1)) = 1-q+q*s`.

This proof requires either a proved sample-complement law or the old swapped/complement hypergeometric identities. The old public `Shuffle.HypergeomParams.expect_pow_le` has the extra premise `s ≤ 1`; it is not an all-s result. The old all-real exponential comparison and positive-u helper are private. Their source can guide an owned compatibility port; referring to an inaccessible/private stronger declaration or changing the old frozen source is not a substitute.

The frozen `HypergeometricTransform` uses A equal to the first x labels and generates P from the first m positions of a uniform permutation. To use it for a random previous intersection in thinning, one must additionally prove that the same estimate holds for every fixed A of cardinality x. A label-permutation equivalence carrying A to the first x labels, together with uniform-permutation invariance, discharges that requirement. Merely knowing the first-x-label theorem does not yet discharge the arbitrary-A step.

### Backward affine recursion

Let independent uniform fixed-size subsets be `P_1,...,P_d`, let `X_j=|P_1∩...∩P_j|`, and set `X_0=M`. Given the first j-1 subsets, the next intersection has law `Hyp(M,X_{j-1},m_j)`. This is an assertion about independent columns, not independent rows.

Starting with `z_d=s`, define `z_{j-1}=1-q_j+q_j*z_j`. Since `0 ≤ q_j ≤ 1` and `z_j>0`, each new base is strictly positive, including q_j=0 and q_j=1. The exact identity

`z_{j-1}-1 = q_j*(z_j-1)`

gives `z_0=1-Q+Q*s`, where `Q=∏q_j`. At each backward step, finite conditional expectation and the one-step transform imply

`E[z_j^X_j] ≤ E[z_{j-1}^X_{j-1}]`.

This works on both sides of s=1: there is no comparison of bases that would require an increasing-in-s assumption. After d steps, `X_0=M` yields the claimed power bound. The second comparison follows from `1+v ≤ exp(v)` with `v=Q*(s-1)` and positivity of `1-Q+Q*s`.

An implementation may express this as an induction eliminating the last uniform permutation and a finite sum over earlier permutations. That is the exact finite conditional argument and avoids sigma-algebra machinery. It still must prove the one-step conditional/uniform law for the eliminated coordinate.

Boundary checks: d=0 gives `X=M`, `Q=1`, and the first comparison is equality; any q_j=0 gives `X=0` and `Q=0`; q_j=1 retains the current set. No strict positivity of q_j, Q, or mu is required. The explicit M>0 hypothesis is retained.

### Exact tail constants

Let `mu=M*Q ≥ 0`. Substituting `s=exp(z)` into the all-s comparison gives

`E exp(z*(X-mu)) ≤ exp(mu*(exp(z)-1-z))`.

For `|z| ≤ 1`, the exponent is at most `mu*z^2`. The old source uses the applicable mathlib estimate `Real.abs_exp_sub_one_sub_id_le`; this can be ported into a generic finite-PMF tail lemma after checking the local API.

For t>0, set `h=t/(2*(mu+t))`. Then `0<h≤1/2`, and

`mu*h^2-h*t ≤ (mu+t)*h^2-h*t = -t^2/(4*(mu+t))`.

Markov at z=h and z=-h, followed by a two-event union bound, proves the exact frozen Bernstein bound. The old public concentration theorem includes a minimum, but its private proof already obtains this stronger denominator form before weakening it. A direct port of that step is preferable; alternatively `t^2/(mu+t)≤t` removes the minimum when mu≥0 and t>0.

At s=1/2, `E[2^(-X)]≤exp(-mu/2)`. On `X≤mu/2`, the random variable is at least `exp(-(log 2)*mu/2)`, giving

`P(X≤mu/2)≤exp(-((1-log 2)/2)*mu)`.

Here `log 2 < 1`, so the frozen `chernoffConstant=(1-log 2)/2` is strictly positive. On the integer event `X<2`, one has X≤1 and therefore `2^(-X)≥1/2`; Markov gives exactly `2*exp(-mu/2)`. The integrality is necessary for the threshold 1/2 step. All formulas remain valid at mu=0 without division by mu. In that case the intersection is deterministically zero, the half-mean bound has right side 1, and the small-count bound has right side 2.

### Residual prescription law

The frozen assumptions are adequate: `b<N`, injectivity of the b prescribed labels, and strictly positive probability of the joint prescription event. Strict positivity supplies a genuine sample in that event because the sample space is finite. In that sample, every requested digit count is at most its original count. Injectivity ensures that each column loses exactly b labels; consequently

`sum_a (cuts.count j a - usedCount r j a) = N-b`.

Thus the natural-number subtractions in the residual `Cuts` are exact, not truncated artifacts. The prescribed event is a product of one-column events. On each column its fiber is in bijection with assignments on the unused labels with these residual counts, via restriction and gluing. Uniformity on the original finite product space therefore gives uniformity on the prescription fiber, and the fiber is itself the product of residual column assignment spaces. This proves residual independence and the frozen point-probability statement for every bijective enumeration e of the unused labels. The statement's injectivity and image condition on e suffice to make it such an enumeration.

Existing useful source is `Shuffle.Histogram.prescriptionFiberEquiv`, `conditional_residual_point`, `conditional_residual_law`, and `Shuffle.conditional_fixedMatrix_residual_law` in `lean/Shuffle/FixedColumns.lean`. The final theorem already conditions a product on a rectangle and allows an empty coordinate set. `ResidualSampling.lean` also has exact sample and intersection-law statements. These are representation/provenance inputs, not yet a checked bridge into the frozen PMF and `Fin (N-b)` definitions.

The conditional tail specialization must use the remaining count and the residual mean. For a prefix w of length d, define

`X_res(w) = C(w) - #{prescribed rows whose prefix is w}`,

`mu_res(w) = (N-b) * ∏_{j<d} ((cuts.count j w_j - usedCount r j w_j)/(N-b))`.

The count identity holds on the conditioning event. Transfer each tail through the proved residual law with this mean. The original total count is the residual count plus the deterministic number of prescribed matches. It does not have the unshifted residual tails.

Concrete diagnostic: with N=2, one column having one target digit, and one prescribed row carrying that target digit, the residual target count and residual mean are zero. Reusing the old mean 1 would incorrectly assert `1=P(X_res≤1/2)≤exp(-c_Ch)<1`. This is not a counterexample to the frozen statement, which correctly changes the parameters.

Finite residual tail constants are uniform even when b varies up to N-1. A residual asymptotic conclusion additionally requires a growing residual population and the corresponding residual depth bound `K≤T*log(N-b)`. One cannot get an error tending to zero uniformly over arbitrary b<N merely from N→infinity. The frozen unconditional `PrefixFailureUniform` does not make that false claim.

### Concrete prefixes and simultaneous event

For a deterministic prefix w of length d, each column's target-digit fiber is a uniform fixed-size subset of the N labels and these fibers are independent across columns. Two proof obligations implement this sentence: (i) under a uniform fixed-histogram column, a chosen digit fiber is uniform among subsets of the required cardinality; (ii) coordinatewise maps of a uniform finite product preserve the product law. The first follows from a transitive label-permutation action or constant-size fibers of the map; the second is a finite product sum identity. Neither implies that rows are independent.

The `List.take` equality in frozen `prefixCount` must be related to the conjunction of the first d coordinate equalities. Then `prefixMean=N*prefixMass` is exactly N times the product of the selected proportions, and the law agrees with successive thinning. Sorting does not change the count; no graph or physical-law bridge is needed for this count identity. The empty prefix has count N and mass 1; any zero-mass prefix has count zero for every valid sample, because a required digit has zero column count.

Set `A=N^epsilon`, `u=sqrt(mu)`, `t=A*(u+1)`. Under N≥2 and epsilon>0, A≥1 and t>0. Since u≥0 and u^2=mu,

`2*A*(u+1)^2 - u^2 - A*(u+1) = (2*A-1)*u^2 + 3*A*u + A ≥ 0`,

which proves `t^2/(mu+t)≥A/2` and therefore the required per-prefix failure bound `2*exp(-A/8)`. A strict failure `t<|C-mu|` is contained in the non-strict tail used in `PrefixTails`.

The number of prefixes of lengths 0 through K is `sum_{d=0}^K k^d≤(K+1)*k^K` for k≥1. Union bound over this entire finite sigma type proves the frozen `prefixFailure`. It explicitly includes empty and zero-mass prefixes and uses no ancestor-family assumption. `AllPrefixConcentration` does not assume k≥1, so handle k=0: if K>0 and N≥2, no `Cuts 0 N K` exists because its per-column empty sum would equal N; if K=0, there is only the empty prefix and failure is zero. For k=1 the ordinary count estimate remains valid.

### Uniform convergence with quantified thresholds

The frozen order is exactly: for fixed k≥2, T>0, epsilon>0, and delta>0, choose N0; then for every N≥N0 and every natural K satisfying `K≤T*log N`, the same error is at most delta. There are no cuts, words, or prescriptions in the error function, so no threshold may depend on them. k, T, and epsilon are fixed before N grows.

For N≥2,

`k^K ≤ N^(T*log k)` and `K+1 ≤ (T+1)*N`,

using log N≤N. Thus, with `a=T*log k+1`,

`prefixFailure ≤ 2*(T+1)*N^a*exp(-N^epsilon/8)`.

A fully elementary explicit-threshold proof is available: choose a positive integer r with `epsilon*r>a`, put `d=epsilon*r-a>0`, and use `exp(x)≥x^r/r!` for x≥0. For x=N^epsilon/8 this gives

`prefixFailure ≤ C*N^(-d)`, where `C=2*(T+1)*8^r*r!`.

Choose a natural N0 at least 2 and at least `(C/delta)^(1/d)`. Then every permitted N and K satisfies the desired bound. This avoids needing a sophisticated asymptotic filter theorem, while existing rpow-times-exponential limit APIs may also be used. No claim is made that these exact helper names already exist in the current mathlib.

### Maximal word and scope of the largest-prefix proposition

The frozen inventory additionally assigns LB-02 `MaximalMeanIdentity` in `AssemblyInputs.lean`. Under k≥2 and N≥2, choose the smallest maximizing digit in each column. This choice is deterministic and satisfies `IsCanonicalMaxWord`. Each maximum proportion is positive because the column proportions sum to 1. The product is the mass of this word and hence its mean equals `maximalMean`.

At the full horizon K/log N, every column fraction equals 1 at the upper endpoint and 0 at the lower endpoint. Therefore

`A(0,horizon) = sum_j[-log(pileMax_j)]/log N`.

Using positivity of each maximum, the logarithm of the product and real-power identities gives

`N * product_j pileMax_j = N^(beta(horizon))`.

K=0 yields the empty word, beta=1, and mean N. No good-column or profile regularity hypothesis belongs in this argument.

To fulfill the prompt's explicit maximal-word tail export, prove a lane-owned corollary: for this deterministic word and any natural m with `(m:Real)≤mu_*/2`,

`P(wordCount<m)≤exp(-c_Ch*mu_*)`,

and equivalently `1-exp(-c_Ch*mu_*)≤P(m≤wordCount)`.

This follows from the full-prefix half-mean tail by event inclusion. The subsequent permutation run and TV statements use LB-01's law bridge and belong to LB-10. They must not be claimed from the count estimate alone. The frozen `FiniteLargestWordTV` is assigned to LB-10, consistently with this division.

## Recommended proof order and completion ledger

1. Establish finite PMF expectation/probability monotonicity, uniform-equivalence, product-sum, Markov, and finite union-bound lemmas using concrete definitions.
2. Port or prove the finite hypergeometric factorial-moment argument and complement bridge; discharge the frozen permutation-sampling `HypergeometricTransform` and its arbitrary-fixed-set corollary.
3. Prove the exact finite coordinate-conditioning step and backward affine recursion; export `successiveThinning` without an assumed transform premise.
4. Derive generic finite natural-count tails from the proved transform, retaining exact frozen constants and mu=0.
5. Prove the target-digit-fiber and prefix-count law bridges; export `prefixTails` for the actual `fixedCountPMF`.
6. Prove the prescription-fiber bijection/PMF law and residual count identity; export `residualLaw` and actual conditional transform/tail specializations.
7. Prove the all-prefix cardinality and union-bound estimate; export `allPrefixConcentration` and the quantified convergence `prefixFailureUniform`.
8. Construct the canonical maximum word, prove both exact mean identities, export `maximalMeanIdentity`, and supply the maximal-word tail corollary for LB-10.

All seven frozen LB-02 exports remain proof obligations at the time of this source review: `successiveThinning`, `prefixTails`, `allPrefixConcentration`, `prefixFailureUniform`, `residualLaw`, `hypergeometricTransform`, and `maximalMeanIdentity`. Conditional residual tails and the maximal-word tail are additional prompt-required consequences to record in the final lane export ledger even though they are not separate entries in `OWNERSHIP.json`. No additive contract change is mathematically required to prove them in the lane namespace.

The two genuinely different one-step proof routes are (a) finite factorial moments plus complementation, and (b) the manuscript's symmetric-mean smoothing and convergence proof. Route (a) has already-written source covering most analytic/combinatorial calculations and is recommended for implementation. The law bridges, residual specialization, simultaneous union bound, and uniform convergence cannot be omitted whichever route is chosen.

## Inspected hashes

| File | SHA-256 |
| --- | --- |
| `Contracts/v1/ModelThinning.lean` | `bdb0c4c3af301658c9798d191b3dfef1ac34d9df02fb988b1c10214d6b039288` |
| `Contracts/v1/AdditionalFinite.lean` | `b94a1cb35d7204e4e6f0c8dbb277ebc471ec16307a38d2351ef290de6da20869` |
| `Contracts/v1/AssemblyInputs.lean` | `fd005b12cc24ebab117cf08b244d28cef07c31ce02a4d429625a7e92c1e874ea` |
| `RiffleLowerV2/Shared/Statistics.lean` | `dd57ff2f4bbac3e26176809ee15081b58510b041e6dee418f65d31d4fc26fb69` |
| `RiffleLowerV2/Shared/Model.lean` | `cceadf1b4a5be2f412fe15a9b52b7b7f3c67bfa6d19270955f7c338f01e90930` |
| workspace `lean/Shuffle/HypergeometricConcentration.lean` | `156d6e9aa774c2e3498975acfb64d9622dfc6d923cfcd96db5a866c4592e5a14` |
