# Independent mathematical reconstruction

## Scope and status

Read only `time_inhomogeneous_riffle_shuffle_unified_article.tex`, `2103.05068v3.pdf`, and `2510.22783v1.pdf` (the PDFs through fresh exact text extractions containing explicit `=== PDF PAGE n ===` markers). No project Lean source, prior report, alternative manuscript, or external mathematical reference was read. No Lean code or manuscript was modified.

The user has not supplied a theorem name or a Lean declaration. Consequently there is no justified identification of **the** blocked theorem. There is, however, an exact mathematical obstruction in the active manuscript: `lem:block-bd`, lines 4951–4977, is false as stated. Its downstream concentration result can be reconstructed without that false lemma; this does not turn the false general statement into a provable theorem.

Lines 2562–2785 are inside `\begin{comment}` / `\end{comment}`. The earlier largest-prefix/cold-spot overview and `thm:lower-bound-blueprint`, including its random-cut paragraph, are inactive. The active lower-bound treatment begins at line 2788. The active upper random-cut result is `cor:random-time-profile-upper-bound`, lines 1999–2011. The active final theorem is only the **buffered** deterministic reduced lower bound, not a separately stated full random-cut cutoff theorem.

## Proof structure and dependencies

### Base definitions

1. `eq:probability-simplex` (91): alphabet size k≥2 and simplex D_k.
2. Fixed pile counts and independent uniform fixed-count columns (95–115, 386–400, 2915–3015) define the shuffle law, row words, lexicographic order, prefix cylinders, counts, intervals, and shuffle path graph.
3. `eq:one-column-costs` (127), tilted laws/costs/entropy (135–147), `eq:profile-costs` (150), and `eq:integrated-profile-costs` (163) define a, ψ, I, H and A, B_θ, J_θ.
4. `eq:global-beta` and the four margins (178–205), thresholds (210, 215), and `def:first-moment-margin` / its repeated numerical version (332 / 750) depend only on those analytic quantities.
5. `def:almost-time-profile-like-cuts` (250), `def:randomized-time-profile-like-cuts` (266), `def:chi-regular-partitions` (277), and `def:good-columns` (306) are approximation/local nondegeneracy hypotheses; the parameter order at 471–488 holds χ and the finite partitions fixed before N→∞.
6. Ambient blocks/exponents (`def:ambient-block-size-exponent`, 491), boundary/stable blocks (`def:boundary-pairs-stable-blocks`, 522), space-time profiles (`def:space-time-digit-profile`, 700), and accessible ambient blocks / RFM (`def:recursive-first-moment-margin`, 367) feed the upper first-moment and exploration arguments.
7. Lower prefix masses λ_w, intervals J_w, ranks L_w/U_w and counts C(w) (2934–2961), labelled survivor sets and conditional residual counts (2977–3066), cold-witness functionals (3430–3496), truncated types and relative cold sets (`def:collision-likely-prefixes`, 3848), bridge/tail data (4004–4078), and full collision events (`def:full-collision-likely-strings`, 4081) feed the active lower branch.

### Upper bound graph

The following arrows are mathematical dependencies, including ones described in prose rather than explicit cross-references.

- Fixed-column shuffle model → `lem:ub-graph-representation` (402).
- Graph representation + finite-density Cauchy–Schwarz → `lem:ub-truncated-chi-square` (410).
- Finite path components + local sparsity → `lem:ub-sparse-factorial` (429).
- Boundary/stable-block definitions → `lem:ub-stable-partition` (788) → `lem:ub-global-boundary-decomposition` (828).
- Regular partition + almost-like cuts → `lem:ub-regular-partition-interval-blocking` (857) → `lem:ub-profile-estimates` (898).
- Boundary/profile truncation + those profile estimates → `lem:ub-bad-profile-reduction` (1039).
- Exact fixed-column sampling → `lem:ub-hypergeometric-estimates` (1121) → `lem:ub-ambient-conditioning-transfer` (1154) → `lem:ub-ambient-concentration-anti-concentration` (1202).
- Global decomposition + stable partition + bad-profile reduction + ambient concentration → `lem:ub-per-edge-stable-localization` (1436).
- Conditional pair-collision counts + ambient concentration/anti-concentration → `lem:ub-edge-density-bounds` (1486).
- Terminal prefix count bounds → `lem:ub-terminal-singleton-bound` (1640).
- FM + profile estimates/entropy + the stable first-crossing conditions → `lem:ub-numerical-lemma` (1662).
- Bad-profile reduction + stable localization + density/terminal bounds + numerical lemma + entropy/class counts → `prop:ub-first-moment` (1817).
- Exact exploration conditioning + hypergeometric estimates → `lem:ub-conditional-preservation` (1923).
- Conditional preservation + block decomposition + first moment for each large accessible block + direct small-block bound + RFM → `lem:ub-conditional-first-moment` (1931).
- Precise directional exploration + conditional first moment → `lem:ub-portenko-exponential-moment` (1949) → `lem:ub-shared-edge-exponential-moment` (1961).
- Prefix concentration + directional conditional collision bounds → `lem:ub-regularity-sparsity` (1974).
- Graph representation + truncated chi-square + sparse factorial + regularity/sparsity + shared-edge exponential moment → `thm:deterministic-upper-bound` (377), completed at 1985.
- Uniform deterministic upper bound + typical random cuts → `cor:random-time-profile-upper-bound` (1999).
- Global negative buffered margins + accessible-exponent bound + regular/local hypotheses → `lem:buffered-pointwise-upper-bound` (2029), which invokes the deterministic theorem through RFM.
- One-column signs/additivity → `lem:upper-margin-monotonicity` (2159). This and buffered pointwise convergence → `cor:full-margin-critical-upper-bound` (2291).
- Simplex maximum-coordinate inequality → `lem:basic-one-column-inequality` (2349) → `thm:dominance-reduction` (2397) → `cor:buffered-consequence` (2471) and equality of thresholds (2512).
- Threshold equality + the four-margin critical result → `thm:upper-critical-reduced` (235; proof at 2515–2551).

The late upper exploration statements remain proof sketches: “accessible”, the precise exploration sigma-fields and directional sets, the exact regular event, and uniform finite-N conditional bounds are not completely specified in a way that directly freezes into Lean. In particular, `lem:ub-conditional-preservation` cannot be justified solely by saying conditioning fixes finitely many rows: the exploration has to be defined and its actual conditioning events accounted for. The homogeneous fixed-cut paper devotes substantial work to this: 2510.22783v1, Lemmas 5.4–5.13, PDF pp.35–50; its key combinatorial conditional-law construction is Lemma 5.7, p.42, not merely a generic hypergeometric observation.

### Active lower-bound graph

- Labelled survivors + uniform independent selected subsets → exact hypergeometric transition (3013).
- One-step Laplace-transform inequality + deterministic backward recursion → `lem:successive-thinning-tail` (3018).
- One-step concentration + iterated error propagation + that lower-tail lemma → `cor:iterated-hypergeom` (3169).
- Maximal-digit word + profile/Riemann estimates + iterated thinning + graph representation + factorial rarity of long increasing runs → `prop:largest-prefix` (3377).
- One-column entropy/collision calculus → `lem:entropy-ineq` (3498).
- All-tail good-shuffle condition + finite regular-cell estimates → `lem:bridge-window` (3540).
- Λ₁ witness + entropy inequalities + bridge window → `lem:cold-witness` (3583).
- Truncated tilted types + Stirling + representative replacements → `lem:type-estimates` (3885).
- Type estimates + witness slack + finite integer interval/boundary counts → `lem:cold-geometry` (3928).
- Same type count on remaining tail → `lem:tail-types` (4095).
- Lexicographic side-piece decomposition + iterated thinning + Cauchy–Schwarz → `lem:uniform-endpoint-theorem` (4123) → `lem:endpoint-control` (4226).
- Two good bridge columns + maximal digits on other bridge columns + witness gap → `lem:bridge-buffers` (4242).
- Endpoint control + bridge buffers + iterated thinning + deterministic lexical squeezing → `lem:localization` (4282).
- Counting prescribed distinct labelled rows in independent fixed-count columns → `lem:fixed-column-factorial` (4340) → `lem:conditional-factorial` (4400).
- Factorial/binomial inversion + quantitative truncation control → `lem:central-window` (4454).
- Unconditional/conditional factorial estimates + rare/central/large mean case split + thinning lower tail → `lem:two-category-poisson` (4536).
- Two-category bound + prefix/tail type estimates + bridge costs + witness slack → `lem:occupancy` (4738) → `lem:cold-collision-count` (4832).
- Cold collision count + localization + injectivity of distinct full words' edge contributions → `lem:many-edges` (4866).
- Independent relative order on disjoint position pairs + Hoeffding + N+1 translations → `lem:uniform-ascent` (4899).
- The manuscript's claimed route is `lem:block-bd` (4951, FALSE) → `lem:permutation-bd` (4979) → `lem:lalley-comparison` (5026).
- Component comparison + uniform scan + graph representation → `lem:lalley` (5115).
- Witness + cold geometry + many edges + Lalley test → `prop:cold-lower` (5167).
- Largest-prefix lower bound versus cold lower bound, split at κ₀ → `thm:buffered-reduced-lower-bound` (2812), completed at 5197.

The false node lies entirely in the final ascent-test part of the active cold lower branch. It does not invalidate the elementary margin-dominance proof or the largest-prefix branch. It also does not by itself establish that the final cutoff statement is false: the needed narrower concentration result has independent proofs below.

### Random pile extension

The active upper extension is sound as an abstract reduction once the deterministic theorem has a **uniform** finite-N error: if good cut realizations have probability 1−ε_N and conditional TV is at most δ_N uniformly there, mixture convexity gives TV≤ε_N+δ_N.

A lower extension cannot be obtained just by averaging individual TV distances. One needs a single test on permutations. The permitted 2510.22783v1 paper supplies the right construction: Lemmas 6.5–6.6, PDF p.53. For each good deterministic sequence n, build its ascent test A_n; use A=∪_n A_n. There are at most (N+1)^(kK)=exp(O((log N)^2)) possible fixed-count sequences when K=O(log N). With a uniform lower bound |H_n|≥N^a and uniform δ>0, the null probability per test is exp(−N^c), so the union still has null probability o(1). Under random cuts, a uniform conditional success probability gives mixture success 1−o(1). The translate scan introduces only an additional N+1 factor.

The inactive overview asserts this reduction at 2747. The active lower treatment proves only a deterministic buffered theorem, so an active random lower theorem and its uniform quantifiers remain an explicit dependency rather than an already proved active result.

## Exact false statement: block value-set bounded differences

`lem:block-bd`, 4951–4964, permits an empty reservoir. Take N=2, m=2, prescribed sizes |V₁|=|V₂|=1, |V₀|=0, and choose the uniform partition of {1,2}. Define

f(V₁,V₂)=10 if V₁={1}, and f=0 otherwise.

Take L₁=L₂=1. For either j, when the other block is fixed, there is only one legal V_j: the hypothesis that changing V_j while adjusting only the reservoir changes f by at most L_j is therefore satisfied, even with L_j=0. But E f=5 and

P(|f−E f|≥5)=1,

whereas the displayed conclusion with positive L_j gives

2 exp(−2·25/(1+1))=2 exp(−25)<1.

This avoids every division-by-zero issue. It is a finite exact counterexample, not an API issue.

The proof's failed implication is at 4971–4976: compensating for a changed currently exposed block generally changes the conditional distribution of other relevant blocks. Coordinate oscillation conditional on their being fixed does not control the Doob increment. Grouping all unexposed values as a temporary “reservoir” is not licensed by the stated hypothesis about the final reservoir V₀.

Therefore no theorem with exactly these frozen assumptions and conclusion can be proved in consistent Lean without an additional assumption, a changed conclusion, or bypassing this node. A bypass proves a different theorem, and must be explicit.

## Reconstruction of the needed component concentration: two different routes

Both routes prove the narrower `lem:permutation-bd` with its existing hypotheses, independently of `lem:block-bd`.

### Direct finite permutation/cardinality route

First prove this finite lemma. Let A₁,…,A_j be disjoint sets of positions in [N]. For a uniform permutation π, the induced relative-order permutations on A₁,…,A_j are independent, each uniform. If |A_i|=a_i and particular relative-order permutations are fixed, exactly

N! / ∏_i a_i!

full permutations realize them. Indeed, select disjoint value sets for the A_i and a reservoir, assign the selected values in the specified local order, and order the reservoir arbitrarily. Divide by N! to get probability ∏_i(1/a_i!). This gives a wholly finite cardinality proof of independence.

Now order the components C₁,…,C_q of path graph G from left to right. Every edge of E(H) internal to a G-component is a deterministic ascent after sorting. Each remaining edge joins C_j to C_{j+1}; its ascent indicator is

B_j = 1{every original value in C_j is smaller than every original value in C_{j+1}}.

B_j depends only on the relative order of values in C_j∪C_{j+1}. Split these boundary indices j into even and odd classes. Within either class, the involved unions of components are disjoint. The finite lemma gives mutual independence within each class. The Bernoulli means need not be 1/2; they are 1 / choose(|C_j|+|C_{j+1}|, |C_j|).

There are at most |E(H)|≤|H|≤M retained boundary edges. Hoeffding in each class and a union bound give an absolute c₀>0 with

P(|X−E X|≥t) ≤ min(1,4 exp(−c₀ t²/M)).

This is ≤2 exp(−(c₀/2)t²/M): when t²/M≤2 log(2)/c₀ the RHS is ≥1; above this threshold the exponential comparison is direct. Thus the manuscript's concentration conclusion holds for a smaller absolute constant c. The boundary-size assumption is not even needed for this concentration step; it is used in the expectation comparison below.

Lean advantage: the essential new independence theorem can be formulated entirely for `Equiv.Perm (Fin N)` with finite uniform probability, finite supports, finite cardinalities and induced orders. No conditional sampling of disjoint value sets is necessary.

### Abstract independent-coordinate route

Let U₁,…,U_N be independent continuous uniform [0,1] variables. Almost surely they are distinct; their rank permutation is uniform on S_N. Sorting π within G-components preserves exactly the same comparison outcomes as sorting the U-values within those components.

Group the independent U-values by G-component. These groups are independent random objects. Changing all values within one component leaves internal ascent indicators equal to 1 and changes at most the two comparison indicators at its path boundaries. Only components touching retained boundary edges affect X; there are at most 2M of them. Independent bounded differences with coordinate oscillation at most 2 yields

P(|X−E X|≥t) ≤2 exp(−t²/(4M)).

This uses a stronger correctly formulated helper about independent coordinates, not the false helper about a random partition. It introduces no additional assumption about G, H, or the uniform permutation; it proves an alternative representation of that same law. The tradeoff is an infinite-product/atomless-rank formalization rather than finite cardinality counting.

No Lean implementation or successful test is claimed for either route.

## Repair of the deterministic ascent expectation step

For neighboring **whole** G-components of sizes a,b≥1, the boundary ascent probability is

p(a,b)=1/choose(a+b,a).

The inequality

1/2−p(a,b) ≤ ((a−1)+(b−1))/6

is true: for a+b≥5 the RHS≥1/2; cases a+b=2,3,4 are direct checks. Summing charges each component's internal-edge count at most twice. Internal edges each contribute an excess 1/2, leaving excess at least one sixth of their count.

The manuscript at 5050–5054 incorrectly says ignoring O(|∂H|) **clipped component intersections** costs O(|∂H|) in total ascent contribution. A clipped intersection can contain arbitrarily many edges. A valid repair keeps all its internal edges (deterministic ascents) and discards only comparison edges incident to such clipped pieces. There are O(|∂H|) such boundary comparison edges, each losing at most 1/2 against the baseline. All remaining pairs are whole G-components and satisfy the displayed charge inequality. Hence

E X ≥ |E(H)|/2 + r/6 − C|∂H|,

with r=|E(G)∩E(H)|, exactly the estimate needed. Combine with either concentration route to reconstruct the active Lalley test while preserving its stated assumptions.

## Other specific unsupported steps

1. **Incorrect factorial Bonferroni coefficient.** At 4571–4576 (and again in the mixed rare-word regime around 4680–4693), the proof uses `(X)_2/2 − (X)_3/6 ≤ 1{X≥2}`. At X=3, the LHS is 2 and the RHS is 1. Correct coefficient 1/3 gives a valid lower bound and preserves the intended asymptotic estimates. This is a proof-line error, not a demonstrated false conclusion of `lem:two-category-poisson`.
2. **Fixed regular-cell errors cannot become o_N(1).** `lem:type-estimates` (3885–3925) and `lem:tail-types` (4095–4120) assert exact truncated representative-cost exponents plus o(1). The allowed replacement in `lem:ub-regular-partition-interval-blocking` (857–895) is O(χ) per logarithmic unit, and χ is fixed before N→∞ at 471–488. Multiplying O(log N) columns yields an O(χ) exponent, not automatically o_N(1). One must decide before freezing whether J^χ uses exact column costs, or keep explicit mesh errors, or prescribe a diagonal vanishing mesh with all uniformity justified.
3. **Central-window truncation requires a weighted-tail estimate.** In `lem:central-window`, the factorial identity at 4490–4495 holds only on X+Y≤R_N, whereas the moment bounds are unconditional. Small probability of the complementary tail (4523–4529) alone does not bound the large truncated factorial polynomial there. Its expectation needs a separate bound using the R_N-th factorial moment. Such a bound appears possible, but is absent. Also the asserted error at 4500–4509 includes `(1+μ)(1+ν)=O((log N)^2)`, which the stated little-o condition does not by itself absorb. The application has polynomial slack and can likely meet a corrected quantitative estimate; the isolated stated lemma has not been rigorously established by this proof.
4. **Undefined finite exploration input.** The upper conditional preservation/first-moment/Portenko sketches (1923–1972) need precise state spaces, events, and sigma-fields. RFM names “accessible” blocks by reference to an exploration not fully defined in the manuscript; this is a missing formal dependency rather than a mathlib search problem.

## Reconstructed finite thinning bridge

The exact finite transition itself is well-founded: an independent uniform m_t-subset of M labelled rows, intersected with a fixed survivor set of size x, has hypergeometric count Hyp(M,x,m_t). Conditioning a bounded collection of labelled rows on admissible prescribed digits subtracts their per-column requested counts and leaves independent uniform residual columns. This is a counting statement and must use the residual m_{t,C}, not the original counts.

For q_t=m_t/M and 0<s≤1 the necessary one-step bound is

E[s^Hyp(M,x,m_t)] ≤(1−q_t+q_t s)^x.

Given that bound, define z_m=1/2 and z_{t−1}=1−q_t+q_t z_t. Conditional expectation and induction yield E[z_m^{X_m}]≤z_0^M, with 1−z_0=(∏q_t)/2. Markov then gives

P(X_m≤μ/2)≤2^{μ/2}(1−μ/(2M))^M≤exp(−((1−log 2)/2)μ).

This product recursion avoids the manuscript's intermediate logarithms a_t and is valid even if q_t=0. The exceptional M=0 case should be explicitly split before forming q_t. A finite proof of the one-step bound may use normalized elementary symmetric means (sampling without replacement) or a proved convex-order comparison. The manuscript cites Hoeffding 1963, Theorem 4, at 3089, but that fourth source is outside this task's allowed reading and has not been inspected or promoted to a trusted Lean theorem.

## Permitted-PDF anchors

- 2103.05068v3: Theorem 1, PDF p.3; graph representation Proposition 2.2, p.6; sparse factorial Lemma 3.3, p.11; first moment Proposition 4.1, p.15; Portenko-type conditional exponential moment Lemma 5.4, p.30; nonmixing ascent criterion Proposition 6.1, p.37; geometry Proposition 6.5, p.39; localization Lemma 6.6, p.40; collision count Lemma 6.8, p.42.
- 2510.22783v1: Theorem 1.1, PDF p.3; finite deterministic theorem Theorem 2.1, p.7; graph representation Proposition 2.2 and one-step hypergeometric estimates Lemmas 2.3–2.4, p.8; iterated prefix counts Lemmas 2.6–2.7, pp.9–10; sparse factorial Lemma 3.5, p.14; shared-edge moments Lemma 3.11, p.16; random-profile typicality Lemma 3.13, p.17; first moment Proposition 4.2, p.18; conditional exploration Lemmas 5.4–5.13, pp.35–50; largest-prefix Proposition 6.1 and ascent criterion Lemma 6.3, p.52; random-cut uniform-test union Lemmas 6.5–6.6, p.53; cold geometry/localization Lemmas 6.9–6.10, p.55; collision count Lemma 6.12, p.57.

## Freeze recommendation

Do not freeze the entire current manuscript as a consistent body of theorem statements: `lem:block-bd` is false. Freeze a specifically identified target and its reachable dependency cone only after the independent reports are compared. If the target is the general `lem:block-bd`, stop with the finite counterexample; no missing API can fix it. If the intended target is `lem:permutation-bd`, the two reconstructed routes above avoid the false dependency while preserving that target's hypotheses. The project still needs the user or existing task context to identify which declaration is actually blocked.
