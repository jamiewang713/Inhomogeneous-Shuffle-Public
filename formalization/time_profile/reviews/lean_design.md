# Independent Lean representation report

Status: proposal for comparison before freezing. This is not Lean code, and none of the statements below has yet been represented as an axiom or placeholder theorem.

I read the unified article and the extracted text of the two authorized PDFs. In 2510.22783v1, the relevant comparison is Sections 2.1 and 4.2, Definitions 4.3 and 4.7, Lemma 4.8, and Lemma 4.16. In 2103.05068v3, the relevant comparison is Sections 4.1.2–4.1.3 and Lemma 4.15. Trusted library inspection was restricted to mathlib.

## Non-negotiable semantic choices

1. Zero pile probabilities remain allowed. The simplex is not its relative interior.
2. The finite depth is K = floor(T log N). In particular t_K = K/log N is generally not T.
3. Use the later, exact ambient-prefix definition: the sum defining c_L starts at M_w, not floor(r log N).
4. The exact finite ambient birth time is τ_w = M_w/log N. A macroscopic r need not equal τ_w; any use of r incurs an explicit error.
5. c_F takes values in WithBot ℝ. Its value is bottom when one side has zero mass, including an empty maximizing set. It is not Real.log 0 = 0.
6. Numerical inequalities involving a real F apply only after both side maxima are proved positive and F is the finite value of c_F. Terminal pairs with bottom c_F use the singleton estimate, which does not mention F.
7. The source profile contains good-digit counts and exceptional positions only. It does not determine exceptional digit values or Q_x. Keep Q_x as a per-word quantity and do not prove that it is constant on such a profile class.
8. The source says only that μ_t is a family of probability measures. Measurability in t is missing. A probability kernel would add a substantive assumption and must not be silently introduced.

## Recommended foundational representation

Use `Simplex k := stdSimplex ℝ (Fin k)`, viewed as a subtype. The existing mathlib definition is exactly nonnegative coordinates plus sum one; it has the expected compact topology. The theorem `mem_Icc_of_mem_stdSimplex` supplies coordinate bounds, and `isCompact_stdSimplex` supplies compactness.

The finite setup has k,N,K natural numbers with k≥2 and N≥2. Put L=log(N)>0. A pile sequence has entries n(j,ℓ) in ℕ with sum_ℓ n(j,ℓ)=N. It produces p(j,ℓ)=n(j,ℓ)/N in the simplex. Use zero-based Lean column indices j∈Fin K and define physical shuffle time as (j+1)/L. This indexing shift is representational only, and must be stated once at the module boundary.

A word of length M≤K can be a function Fin M→Fin k with its bound M≤K. A legal word additionally requires p(j,x(j))>0. A prefix relation is equality on all earlier coordinates. This is preferable to depending on List indexing defaults, because all logarithms that appear in a legal word then have explicit positivity proofs. All combinatorial lemmas below can equivalently use a fixed complete digit function Fin K→Fin k and two integer cut positions; neither encoding adds a mathematical hypothesis.

A finite Borel partition is represented by a finite type I, a measurable cell assignment `classify : Simplex k → I`, and representatives `rep : I → Simplex k` satisfying classify(rep i)=i. Its cells are fibers. This is equivalent to a finite partition with nonempty cells and chosen representatives and avoids repeatedly carrying disjointness/cover proofs. Empty cells in an input partition can be removed; no probability or approximation statement changes.

For χ>0 and C≥0, regularity is precisely the following, for classify(p)=classify(p')=i:

- For all θ∈[2,4], |ψ_p(θ)−ψ_p'(θ)|≤Cχ.
- |a_p−a_p'|≤Cχ.
- If rep(i)_ℓ>2χ then p_ℓ>χ and |log(1/p_ℓ)−log(1/rep(i)_ℓ)|≤Cχ.
- If rep(i)_ℓ≤2χ then p_ℓ≤3χ.

The constant C is explicit data, replacing the unnamed source constant. Regularity is a definition, not a substitute for proving regular partition existence.

A time mesh has R cells and boundary times t_0<...<t_R, with t_0=0 and t_R=T. Define J_q=[t_q,t_{q+1}) except for the last cell J_{R−1}=[t_{R−1},T]. Record width≤Δ as a predicate. For T=0, use a separate degenerate mesh/empty-column branch; do not demand R>0 and strict endpoints when T=0. For T>0, the ordinary nonempty mesh is sufficient.

For an arbitrary family μ_t of probability measures, the source almost-like predicate can be defined literally, with a closed grid interval I=[a,min(a+ρ,T)], a∈ρℤ, 0≤a<min(a+ρ,T)≤T:

|count{j : (j+1)/L∈I and classify(p_j)=i}/L − ∫_I μ_t(D_i)dt| ≤ φ length(I)+1/L.

This definition by itself does not supply time measurability. The actual integral approximation theorems must be kept separate until that issue is resolved. The source uses closed grid intervals, whereas its blocking proof uses half-open ones; the conversion costs at most 1/L per endpoint and must be proved explicitly.

## Exact one-column functions and zero conventions

Define maximum pile mass as the finite maximum of coordinates, a(p)=log(1/p_max), Z(p,θ)=sum_ℓ p_ℓ^θ, and ψ(p,θ)=−log Z(p,θ). Only θ≥1 is used. Since the simplex has positive total mass, Z>0 even at boundary points.

For cost functions of a single digit, ordinary real log may be used as a total function, provided every positive-count/selected-digit theorem proves that the relevant coordinate is positive. In particular, zero-count summands in S_x and H_x are zero. Entropy can be written sum c_ℓ log(c_tot/c_ℓ), with the summand expressly set to zero at c_ℓ=0. This equals the source definition. Do not appeal to logarithmic identities at zero coordinates.

For extended logarithmic exponents define logN₀(z)=bottom if z=0, and log(z)/L otherwise, on nonnegative z. Then c_F is the minimum of the two values of logN₀(sqrt(sideMaximum)). No arithmetic such as bottom−bottom is needed in the finite comparison lemmas.

## Exact finite ambient model

For a legal ambient word w define its deterministic expected mass by

m(w)=N product_{j<M_w} p_j(w_j)>0.

This is a finite product. Its identification with an expected random cardinality is a separate probabilistic bridge; it must not be smuggled in by naming a real parameter an expectation.

For any real b and legal extension x, define

c_L(b,w,x)=b−L⁻¹ sum_{M_w≤j<M_x} log(1/p_j(x_j)),

c_E(x)=−L⁻¹ sum_{M_x≤j<K} ψ(p_j,2).

Write b_exact=log(m(w))/L. A macroscopic ambient approximation is recorded by actual finite bounds |b_exact−b|≤e_b and |τ_w−r|≤e_r. Neither b≥0 nor b_exact≥0 should be imposed: rare legal prefixes can have negative size exponent.

The deterministic left side mass at relative split j is

m(w) product_{M_w≤h<j} p_h(x_h) sum_{ℓ<x_j}p_j(ℓ),

and the right side mass has ℓ>x_j. The suffix after j does not occur in this formula, because the sum over its full legal continuation space is one. Thus maxima over M_w≤j<M_v depend only on the boundary prefix v=y∨z. This gives exactly the finite version of the source c_F definition once the expected-count identity is supplied. The definition includes the first column after w, even when that column's count is deterministic; this report does not claim any anti-concentration theorem from this c_F.

If genuine left and right crossings each have side mass at least χ in their crossing columns, then both side maxima are positive and

F ≥ c_L(b,w,x)/2 − (e_b+log(1/χ)/L)/2.

This is the explicit replacement for the source fluctuation comparison. Its finite proof is multiplication of nonnegative numbers, prefix-product monotonicity, and monotonicity of log and square root. There is no concentration assumption.

## Exact digit quantities

Fix legal prefixes w≤v≤x, with M_v≤M_x. Put s=M_v/L and u=M_x/L. For positions M_v≤j<M_x, assign the unique time cell q(j) and simplex cell i(j). Good means rep(i(j))_{x_j}>2χ. Exceptional means its negation.

Let n(q,i,ℓ) be the natural number of good positions with this triple, c(q,i,ℓ)=n(q,i,ℓ)/L, c_tot(q,i)=sum_ℓ c(q,i,ℓ), and E_x the exceptional position set. Define

S=sum c(q,i,ℓ) log(1/rep(i)_ℓ),

Q=L⁻¹ sum_{j∈E_x} log(1/p_j(x_j)),

R=|E_x|/L,

H=sum_{q,i} sum_{ℓ:c(q,i,ℓ)>0} c(q,i,ℓ) log(c_tot(q,i)/c(q,i,ℓ)).

No digit values are added to the profile equivalence relation. The same-profile conclusions are only S_x=S_x', H_x=H_x', and R_x=R_x'; Q_x=Q_x' is not asserted.

The replacement bound has no floor or asymptotic term:

|c_L(x)−(c_L(v)−S−Q)| ≤ Cχ G/L ≤ Cχ(u−s),

where G is the number of good positions. For each θ∈[3,4] the exact entropy inequality is

H ≤ θS − sum_{q,i}c_tot(q,i)ψ(rep(i),θ).

The exceptional contribution to the corresponding full-position representative ψ sum is between zero and 4 log(k) R. This coarse uniform constant is enough and avoids importing sharp Rényi bounds.

## Fully explicit numerical core

All quantities in this subsection are real. Let θ∈[3,4], let e_L,e_F,e_β,e_H,e_E,e_S,δ be nonnegative, and use β,B_θ,B_2 for supplied cost values. These are internal finite algebraic lemmas; the profile module must later discharge their assumptions.

Large core assumptions:

- L_x≤L_v−S−Q+e_L;
- Q≥0;
- L_x−F≤δ;
- F≥L_v/2−e_F;
- L_v≤β+e_β;
- H≤θS−B_θ+e_H;
- E≤−B_2+e_E.

Conclusion:

4L_x−F+2E+H ≤ ((θ+3)/2)β−B_θ−2B_2
 +4e_L+e_F+(7/2)e_β+δ+e_H+2e_E.

The proof uses θ(L_x+S)+(4−θ)L_x−F. It needs no lower bound on L_x. This avoids any extra “large block” convenience hypothesis.

Small core replaces the first three assumptions by S≤L_v−F+e_S, keeping the final four assumptions. Its conclusion is

−F+2E+H ≤ ((θ−1)/2)β−B_θ−2B_2
 +(3/2)e_β+5e_F+4e_S+e_H+2e_E.

Singleton core: L_v≤β+e_β and E≤−B_2+e_E imply

L_v+E≤β−B_2+e_β+e_E.

Define E_large and E_small to be the displayed total errors. If source numerical margins are at most −η and the appropriate total error is at most η/2, the desired exponent is at most −η/2, hence also at most −η/4 for η>0. There is no need to hide further errors in an o(1).

The source uses an infimum over θ∈[3,4]. An equivalent finite interface, once the cost function is known bounded below, is: for every ε>0 there is θ∈[3,4] with numerical cost≤−η+ε. This is a near-minimizer, not an attained-minimum hypothesis. If using this interface before its equivalence with source FM is proved, name it `NearNumericalMargin` and explicitly mark the bridge as outstanding. Do not silently change source FM into an existence-of-minimizer condition.

For terminal fallback exclusion, the precise finite condition is: if L_x≤−η+e_T, F≥L_x/2−e_F, e_T+2e_F≤η, and δ>0, then L_x−F<δ. This applies without identifying t_K with T.

## Proposed exhaustive theorem catalog

Each row lists a principal theorem, its full mathematical content, and dependencies. Straightforward subtype projections and coercion rewrites are not separate mathematical lemmas. If a helper has additional mathematical content, its statement must be added to the frozen catalog before implementation.

| ID | Exact statement to freeze | Dependencies/type |
|---|---|---|
| F01 simplex_coordinates | For p in Simplex k and every ℓ, 0≤p_ℓ≤1. | stdSimplex; finite |
| F02 simplex_positive_coordinate | For p in Simplex k, some coordinate is positive; for k≥1, p_max≥1/k>0. | F01, sum=1; finite |
| F03 cuts_to_simplex | For N>0 and natural pile counts summing to N, p_ℓ=n_ℓ/N belongs to Simplex k; p_ℓ>0 iff n_ℓ>0. | F01; finite |
| F04 logarithmic_scale | N≥2 implies L>0. For T≥0, K=floor(TL), 0≤T−K/L<1/L. | floor/log mathlib; analytic |
| F05 one_column_bounds | For k≥2, θ∈[2,4], 0≤a(p)≤log k and 0≤ψ(p,θ)≤4 log k. | F01–F02, rpow/log; analytic |
| F06 time_cell_partition | For a strict mesh with positive cell count, every t∈[0,T] belongs to exactly one J_q. In particular every sample time (j+1)/L≤T does. | strict monotonicity; finite/order |
| F07 regular_good | χ>0 and χ-regularity with constant C imply every good selected digit has actual p>χ, representative p>0, and logarithmic error≤Cχ. | regularity definition; finite/analytic |
| F08 regular_exceptional | Under the same definition, every exceptional selected digit has actual p≤3χ. | regularity definition; finite |
| F09 regular_partition_exists | For k≥2 and 0<χ<1/k, there exist a finite Borel partition and representatives satisfying all source regularity conditions with the fixed constant C=1. | compact simplex, joint continuity of ψ, positivity on good coordinates; topology/analytic |
| D01 legal_word_weight | Legal word product is positive and at most one; extension products decrease. | F01, F03; finite |
| D02 ambient_cost_split | For w≤v≤x legal, c_L(w,x)=c_L(w,v)−L⁻¹ sum_{M_v≤j<M_x}log(1/p_j(x_j)). | finite sum splitting |
| D03 ambient_cost_monotone | Under the same hypotheses c_L(w,x)≤c_L(w,v). | D02, F01; analytic |
| D04 ambient_exact_exponent | log(m(x))/L=c_L(b,w,x)+(b_exact−b). | D01, product-log identity; analytic |
| D05 tail_exponent | c_E≤0, and c_E=0 when M_x=K. | F05, empty sum |
| D06 profile_counts | Every c,c_tot,R is nonnegative; sum_{q,i}c_tot+R=(M_x−M_v)/L. | F06, finite fiber counting |
| D07 profile_nonnegative | S≥0, Q≥0, H≥0. | F01, F07, D06, selected-coordinate positivity |
| D08 profile_cost_replacement | Absolute error bound Cχ G/L stated above. | F07, D02, finite sum reindexing |
| D09 parent_good_cost_increment | If x extends its parent by one digit, S_x−S_parent is zero for an exceptional last digit; for a good last digit it lies in [0,log(1/χ)/L], assuming 0<χ<1/k. | F07, sum splitting |
| D10 parent_crossing_cost | If parent is at/after v and c_L(parent)−F≥δ≥0, then S_x≤c_L(v)−F+Cχ(M_parent−M_v)/L+log(1/χ)/L. | D07–D09 |
| D11 finite_entropy_bound | For every θ∈[3,4], H≤θS−sum c_tot ψ(rep,θ). | finite Gibbs inequality, F07 |
| D12 exceptional_psi_error | The full-position representative ψ sum minus the good-position sum belongs to [0,4 log(k) R]. | F05, D06 |
| D13 same_profile_S_H_R | Equal good counts and equal exceptional position sets imply equal S,H,R, for fixed partition and scale. No conclusion about Q. | definitions |
| B01 side_mass_suffix_independent | For j<M_v≤M_x and x extending v, the side-mass finite products for x and v agree. | prefix equality; finite |
| B02 fluctuation_continuation | c_F(w,x;y,z)=c_F(w,v;y,z), with WithBot semantics. | B01, finite maxima |
| B03 fluctuation_bottom | c_F=bottom iff at least one side maximum is zero; empty side sets give zero. | definition, nonnegative maxima |
| B04 fluctuation_lower_bound | Genuine left/right crossings of mass≥χ>0 imply finite c_F and F≥c_L(x)/2−(e_b+log(1/χ)/L)/2 when |b_exact−b|≤e_b. | D01, D04, B01, log/sqrt monotonicity |
| N01 large_numerical_core | Exactly the seven assumptions and explicit large conclusion above. | real ordered-field algebra |
| N02 small_numerical_core | Exactly the small assumptions and explicit small conclusion above. | real ordered-field algebra |
| N03 singleton_numerical_core | Exactly the two upper bounds and explicit singleton conclusion above. | linear arithmetic |
| N04 near_infimum | For nonempty range of cost on [3,4] bounded below, sInf(range)≤−η iff every ε>0 admits θ∈[3,4] with cost(θ)≤−η+ε. | conditional completeness of ℝ |
| N05 large_margin | If the N01 hypotheses hold for every θ∈[3,4], the corresponding NearNumericalMargin holds, η>0, and E_large≤η/2, then 4L_x−F+2E+H≤−η/2. | N01, N04/order limit |
| N06 small_margin | Analogous N02 statement with E_small≤η/2. | N02, N04/order limit |
| N07 singleton_margin | If β−B_2≤−η and e_β+e_E≤η/2, then L_v+E≤−η/2. | N03 |
| N08 no_terminal_fallback | Exact terminal inequality stated above. | linear arithmetic |

The following are required for the complete time-profile layer but should not be silently claimed from the finite catalog. They need a resolved measurable-profile contract and a separate freeze comparison:

| ID | Intended finite statement | Required unresolved/extra work |
|---|---|---|
| M01 grid_endpoint_conversion | Closed and half-open empirical counts differ by at most 1/L per changed endpoint; time integrals agree at endpoints for measurable bounded cell mass functions. | integral singleton-null facts; no asymptotic notation |
| M02 interval_blocking | For 0≤a≤b≤T and each cell, normalized count on (a,b] differs from its integrated mass by at most φT+4ρ+(2 ceil(T/ρ)+8)/L. | measurable cell mass, closed-grid AlmostLike, explicit floor/endpoint count proof |
| M03 bounded_cost_quadrature | If f is bounded by M and regular-cell oscillation≤ω, the difference between empirical f cost and integrated μ_t f on (a,b] is at most 2Tω + (#cells)M[φT+4ρ+(2 ceil(T/ρ)+8)/L]. | M02 and measurable integral decomposition; bound is intentionally coarse and explicit |
| M04 tail_cost_profile | |c_E(x)+B_2(u,T)| bounded by M03 with f=ψ_2 plus terminal interval length contribution≤4 log(k)/L where needed. | M03, F04–F05 |
| M05 maximal_cost_profile | c_L(v)≤β(r,s)+M03(a)+log(k)e_r. | M03 and |τ_w−r|≤e_r |
| M06 entropy_cost_profile | H≤θS−B_θ(s,u)+M03(ψ_θ)+4 log(k)R, uniformly in θ∈[3,4]. | D11–D12, M03 |
| M07 source_numerical_margin | Combine M04–M06, B04, and parent/first-crossing bounds to discharge N05–N08 uniformly. | no new hypotheses; errors must be substituted explicitly |
| M08 parameter_selection | For fixed k,T,η and finitely many regular cells, choose χ, then other parameters, then N so the explicit error budgets are≤η/2; quantify every choice. | uniform constants, regular partition complexity and order of choices |

M02's bound needs checked arithmetic before freeze; it is a proposed safe explicit envelope, not a proved theorem. In particular the #cells factor in M03 prevents treating a bound depending on χ as a uniform constant while sending χ to zero. Choose the parameters in the source nested order.

## Proof implementation notes

For finite entropy, it is simpler to derive Gibbs' inequality from `Real.log_le_sub_one_of_pos` on the support of the empirical distribution than to instantiate the general measure-theoretic KL divergence library. Normalize by c_tot only in its positive branch; use the zero branch separately. The tilted reference weights p_ℓ^θ/Z are positive wherever c_ℓ>0 by good-digit support. This gives the exact source inequality with no full-support assumption.

A constructive regular partition is possible using a coordinate grid of diameter ε. Take ε≤χ² and then small enough for the uniformly continuous functions a(p) and ψ(p,θ), jointly on Simplex k×[2,4]. Such a grid gives |p_ℓ−rep_ℓ|≤ε. Good coordinates then stay above χ; the logarithm is Lipschitz on [χ,1]. Empty grid cells are removed and a representative is chosen from each remaining cell. If an entirely explicit grid is preferred, ε=χ²/(4k⁵) suffices using |p^θ−q^θ|≤4|p−q|, Z≥k⁻⁴, and the derivative bound for log. This gives C=1. These analytic estimates must be proved, not packaged as new assumptions.

The existence statement must use a fixed C (C=1 is available). The weaker quantifier pattern “for every χ there exists some finite C” would not ensure Cχ tends to zero and is insufficient for the later parameter selection.

No regular partition is needed for the purely algebraic numerical cores; no stochastic independence is needed for the digit count algebra. Probability enters only when finite product masses are identified with expected random counts and later when concentration/anti-concentration is applied. Measure theory first enters the Borel partition and μ integrals, not the count partition identities.

The report therefore recommends freezing and implementing the complete finite catalog first, including regular partition existence if its proof is accepted during comparison, while visibly retaining M01–M08 as unresolved integral obligations until the source's time measurability is settled.
