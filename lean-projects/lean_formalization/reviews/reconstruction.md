# Independent mathematical reconstruction

This is the mathematical-argument review, prepared before any Lean implementation or statement freeze. I read only the three authorized mathematical sources. PDF citations below use the printed PDF page numbers and their named statements; line citations refer to `time_inhomogeneous_riffle_shuffle_unified_article.tex`. Faithful PDF text extraction was used for reading.

## Source correspondence and scope

The assigned statements are:

- `lem:ub-regular-partition-interval-blocking`, lines 857–896;
- `lem:ub-profile-estimates`, lines 898–1037;
- `lem:ub-bad-profile-reduction`, lines 1039–1119.

Their main definitions are at lines 249–307, 446–518, 521–697, and 699–747. The closest old proofs are 2510.22783v1, Lemma 4.8 and equations (4.11)–(4.16), pp. 23–24; Lemmas 4.11–4.13, pp. 26–27; the KL argument and equations (4.29)–(4.37), pp. 30–32; and the proof of Proposition 4.2, pp. 32–33. The earlier iid paper 2103.05068v3 supplies Proposition 4.2 and Definition 4.3, pp. 16–17, and the KL argument (4.19)–(4.20), pp. 26–27.

None of these papers is itself a previously proved Lean theorem. The mathematical dependencies identified here must be connected to actual proved project definitions/theorems by the coordinating agent; no such connection is asserted without inspecting the permitted formalization environment.

## Proof architecture

### Upper bound

1. Fixed-column shuffle matrices give legal words, prefix cylinders, lexicographic intervals, the shuffle graph, and the graph representation (`lem:ub-graph-representation`).
2. First-crossing left/right boundary prefixes give a boundary-pair partition. The first-crossing size-versus-fluctuation stopping rule gives stable blocks (`lem:ub-stable-partition`, `lem:ub-global-boundary-decomposition`).
3. The assigned regular-cell estimates convert finite logarithmic costs into profile integrals. The assigned entropy inequality bounds the number of continuations of each digit type. The assigned truncation and counting estimates bound discarded row mass and the number of retained boundary/profile descriptions.
4. Hypergeometric concentration and anti-concentration, conditional transfer, per-edge localization, and edge-density estimates supply probabilistic bounds for each stable block.
5. The numerical first-moment lemma combines the assigned estimates with FM. Large blocks use `4 c_L - c_F + 2 c_E + H`; small non-singleton blocks use `-c_F + 2 c_E + H`; singleton blocks use `c_L + c_E`.
6. Class counting, entropy bounds, and localization give `prop:ub-first-moment`.
7. Conditional preservation and RFM permit repeated conditional application during forward/backward exploration. Portenko-type estimates give shared-edge exponential moments. Local sparsity, the factorial bound, and truncated chi-square imply the deterministic upper bound.
8. The buffered-margin argument and dominance reduction reduce four margins to `Lambda_0` and `Lambda_1` and yield the critical-time upper theorem.

The assigned part depends on neither anti-concentration nor FM for its basic finite inequalities. Those are consumers of this part, not assumptions to add to it.

### Lower bound

The full lower proof begins at line 2791. Its declared imports U2/U3, lines 2853–2870, explicitly consume regular partition/interval blocking and profile bookkeeping from the assigned part.

- `Lambda_0 > 0`: maximal-pile product estimates identify a polynomial expected block size; successive hypergeometric thinning gives a large constant-string block; component sorting gives a long increasing run; the uniform-permutation bound `N/m!` separates the measures (`prop:largest-prefix`).
- `Lambda_1 > 0` with small `Lambda_0`: entropy inequalities and a buffered bridge yield a cold witness. Tilted prefix/tail types use regular-cell logarithms, entropy identities, truncation, and multinomial counting. Cold-set geometry, endpoint control, and bridge buffers localize the selected collisions. Fixed-column factorial and occupancy estimates give many cold edges. A uniform translate-scan ascent bound and Lalley's comparison separate the shuffle from uniform (`prop:cold-lower`).
- `thm:buffered-reduced-lower-bound` takes the appropriate branch.

The assigned finite entropy upper bound is not by itself the lower type-count asymptotic: the latter also requires the lower multinomial/Stirling estimate and rounded tilted types.

### Random pile sizes

The supplied TeX states the random **upper** extension at lines 1999–2011: condition on the realized cuts, apply the uniform deterministic upper estimate on the high-probability almost-like/good-shuffle event, and average. The exact finite inequality is

`TV(mixture(P_n), U) <= P(cuts not typical) + sup_{typical n} TV(P_n,U)`.

This corresponds to 2510.22783v1 §3.3, pp. 17–18. The supplied TeX does not state a random-pile matching lower theorem. A matching lower bound cannot be deduced merely by averaging deterministic TV lower bounds: a common distinguishing event is required. The oldest iid paper needs no bad-profile truncation because its fixed pile probabilities are strictly positive constants.

## Finite setup for exact statements

The following are explicit mathematical domains, not permission to strengthen the paper:

- `N >= 2`, `L = log N > 0`; `k >= 2`; `K` a natural number; optionally `K <= T L` with `T >= 0`.
- At each column `j`, `p_j : Fin k -> R` is a probability vector. In the fixed-pile model, `p_j(l)=n_j(l)/N` with nonnegative integer counts summing to `N`.
- A finite cell index set `I`, cell assignment `i(j)`, and representative probability vectors `r_i` are fixed. The partition properties hold with a fixed nonnegative oscillation constant `C chi`.
- Legal words have positive actual coordinate masses. All logarithmic word costs are only evaluated at legal digits. Terms with zero good counts may be omitted; this avoids interpreting `log(1/0)` as an extended-real operation.
- A fixed legal ambient prefix `w` and a legal extension `v <= x` have lengths `M_w <= M_v <= M_x <= K`.
- Product word mass is `lambda(x)=prod_{j <= M_x} p_j(x_j)` and expected row count is `m(x)=N lambda(x)`.
- If `b` is the paper's ambient exponent, retain the explicit error
  `e_w = log(m(w))/L - b`.
  Then `log(m(x))/L = c_L(x)+e_w` exactly. An eventual claim `e_w=o(1)` is a separate property of the ambient-block sequence.

Two facts about fixed-column sampling must precede probabilistic versions of the assigned lemmas: a fixed row has coordinate product law because different columns are sampled independently, and expected row counts equal `N` times the one-row probability by linearity. Independence between different rows is neither true nor required.

## Exact helper catalogue and proofs

Each item below is a proposed finite statement to be compared with the independent representation/adversarial reports before freezing.

### R1. Pointwise regular representative replacements

Assume `chi>0`, `p in D_i`, and the stated chi-regular partition.

1. For `theta in [2,4]`, `abs(psi_p(theta)-psi_{r_i}(theta)) <= C chi`.
2. `abs(a_p-a_{r_i}) <= C chi`.
3. If `r_i(l)>2 chi`, then `p(l)>chi` and
   `abs(log(1/p(l))-log(1/r_i(l))) <= C chi`.
4. If `r_i(l)<=2 chi`, then `p(l)<=3 chi`.

These are projections of the definition at lines 278–300; no almost-like hypothesis, local good-shuffle hypothesis, asymptotic error, or `+o(1)` is needed. Actual mass bounds are exactly strict `>chi` and weak `<=3chi`. The threshold cases `r_i(l)=2chi` and zero representative coordinates must remain in the exceptional branch.

### R2. Lattice interval counting

For `L>0`, the number of integer columns `j` with `j/L` in a real interval of length `d>=0` is at most `d L + 2`. The same holds after restricting to `1<=j<=K`. For a union of at most two intervals of combined length `d`, use `d L+4`.

Proof: multiply interval endpoints by `L`; distinct selected integers are separated by at least one. If there are `q>0`, last minus first is at least `q-1` and at most interval length. Half-open/closed changes affect at most endpoints.

This is the only probabilistic-free fact needed to control the two omitted grid boundary pieces.

### R3. Arbitrary-interval blocking

Assume `rho>0`; a finite rho-grid partition of `[0,T]`; and each cell `i` has a measurable density `h_i(t)` in `[0,1]`. The intended density is `mu_t(D_i)`. For every closed grid block `G`, suppose

`abs(count_i(G)/L - integral_G h_i) <= phi length(G)+1/L`.

Then for every subinterval `J` of `[0,T]`, a safe explicit bound is

`abs(count_i(J)/L - integral_J h_i) <= 4 rho + T phi + (2 ceil(T/rho)+8)/L`.

The harmless `+8` covers every endpoint convention, including closed source blocks converted to half-open disjoint blocks. A sharper constant is possible but unnecessary.

Proof: retain full grid blocks contained in `J`; there are at most `ceil(T/rho)`. Converting their source closed counts to disjoint half-open counts costs at most one column per block. Sum their discrepancies: `<=T phi+2 ceil(T/rho)/L`. The two residual end pieces have combined length at most `2rho`; their density integral is at most `2rho` and their normalized lattice count is at most `2rho+4/L`. Changing endpoint conventions for `J` adds at most another `2/L`. Triangle inequality gives the displayed safe bound.

The measurability/integrability condition is currently missing from the literal TeX phrase “a family of probability measures.” It must be resolved before freezing the integral theorem. One may prove all finite counting statements without it.

### R4. Generic finite-to-integral replacement

Let `f` be bounded in absolute value by `M>=0` on the simplex and oscillate by at most `epsilon>=0` within each cell. Write

`d_i(J)=abs(count_i(J)/L - integral_J mu_t(D_i))`.

Assuming the relevant finite partition integrals exist, the exact inequality is

`abs(L^-1 sum_{j/L in J} f(p_j) - integral_J E_{mu_t} f)`

`<= epsilon (count(J)/L + length(J)) + M sum_i d_i(J)`.

Proof: replace each discrete value by its cell representative, costing `epsilon count(J)/L`; replace each continuous integrand by the finite representative simple function, costing `epsilon length(J)`; the difference of the two representative sums is bounded by `sum_i abs(f(r_i)) d_i(J)`.

The count of simplex cells is a real dependency in the error. For fixed chi it is finite and parameters chosen later may absorb it. It must not silently disappear from a finite theorem.

No separate time mesh or continuity of `t -> mu_t` is needed for this argument. The time mesh is bookkeeping for type counts.

### R5. Bounded simplex costs

For every probability vector on `k>=1` symbols:

`0 <= a_p <= log k`;

for `theta>=1`, `0 <= psi_p(theta) <= (theta-1)log k`.

Proof: `p_max>=1/k` and `p_max<=1`; also `sum p_l^theta<=sum p_l=1`, while convexity/power-mean gives `sum p_l^theta>=k^(1-theta)`. Hence on `[2,4]`, `0<=psi<=3log k`; at theta two, `0<=psi(2)<=log k`.

These supply uniform bounded coefficients in R4 and in the entropy deletion error. Support may contain zeros; the power sum is nevertheless positive because some coordinate is positive.

### P1. Product mass and exact c_L identity

For legal extensions `v<=x`, let `G(x)` be the good positions after `v` and `E(x)` the exceptional positions. Define the paper's `S_x` from representative good costs and `Q_x` from actual exceptional costs. Then

`abs(c_L(x)-c_L(v)+S_x+Q_x) <= C chi |G(x)|/L`.

In particular the right side is at most `C chi K/L <= C chi T`.

Proof: split the defining sum for `c_L(x)` at `M_v`, separate good from exceptional positions, regroup good representative terms by `(q,i,l)`, and apply R1 to each good summand. Exceptional terms are kept exactly. No stability, admissibility, R-bound, local good-shuffle condition, or profile-integral hypothesis is used.

Also `S_x>=0`, `Q_x>=0`, since all contributing actual/representative probabilities are in `(0,1]`.

### P2. Tail c_E estimate

Let `u=M_x/L` and `c_E(x)=-L^-1 sum_{j>M_x} psi_{p_j}(2)`.
Apply R4 with `f=psi(2)`, `M=log k`, `epsilon=Cchi`, and `J=(u,T]`. All actual indices in this interval are exactly the tail indices when `K=floor(TL)`. Thus

`abs(c_E(x)+B_2(u,T)) <= Cchi (tailCount/L+T-u) + (log k) sum_i d_i((u,T])`.

R3 implies the stated asymptotic error. The last interval of length `<1/L` has no actual columns but is already handled by R3/R4. At a terminal word, `u=K/L`, not literally `T`; `0<=B_2(u,T)<=(log k)/L` explains the eventual negligible difference.

### P3. Maximal-pile estimate

For legal `v`, actual digit mass is at most the maximal pile at every position, so

`c_L(v) <= b - L^-1 sum_{M_w<j<=M_v} a_{p_j}`.

Apply R4 to `f=a`, `M=log k`. With `r_N=M_w/L`, `s=M_v/L`, this gives

`c_L(v) <= b-A(r_N,s) + Cchi((M_v-M_w)/L+s-r_N)`

`+ (log k) sum_i d_i((r_N,s])`.

If the paper uses an asymptotic ambient time `r` instead of `r_N`, add the explicit endpoint error `(log k) abs(r-r_N)`. The finite statement must not equate them.

The same estimate applies to every legal prefix, not only a boundary word. Choosing each digit to be a maximizer gives equality in the first displayed inequality; this is the exact input needed by the largest-prefix lower bound.

### P4. Side-cylinder product mass

For a legal continuation `x` and `M_w<i<=M_x`, the expected row count of the left side piece is exactly

`m(x up to i-1) * sum_{l<x_i} p_i(l)`.

All later positions of the side piece are unrestricted, so their product-law masses sum to one. The analogous right formula uses `sum_{l>x_i}`.

Consequently, if a left crossing at `i` leaves total mass at least `chi` to the left, then

`E |I(P_{x,i})| >= chi m(x)`.

Proof: `m(x)=m(prefix i-1)*p_i(x_i)*prod_{j>i}p_j(x_j)`, and the last two factors are at most one. Equivalently, the smaller subfamily keeping later digits fixed gives the paper's ratio proof. No division by zero occurs because `x` is legal.

### P5. Finite fluctuation comparison

Suppose both sides of the boundary pair have genuine crossings after `M_w` and at or before `M_v`. Then both side maxima in the definition of fluctuation are positive. By P4,

`c_F(x;y,z) >= (c_L(x)+e_w)/2 + log(chi)/(2L)`.

In particular,

`c_F(x;y,z) >= c_L(x)/2 - (abs(e_w)+log(1/chi)/L)/2`.

Both maxima are determined by `v=y vee z`: although side pieces are represented as words of length `M_x`, their later coordinates are unrestricted, hence their total mass does not depend on this length. Therefore `c_F(x;y,z)=c_F(v;y,z)` exactly.

For nonterminal boundary pairs the crossings are automatic from the first-crossing definition. No alpha-chi assumption is involved. The term `log(1/chi)/L` tends to zero only after chi has been fixed. This is a statement about the defined mean-based quantity; it does not establish genuine endpoint anti-concentration, discussed below.

### P6. Parent-crossing S bound

Suppose `x` is a strict descendant of `v` and the parent condition is

`c_L(parent x)-c_F(v)>=delta`.

For `0<chi<1/k`, P1 and nonnegativity of `Q` give

`S_x <= c_L(v)-c_F(v)-delta + Cchi K/L + log(1/(2chi))/L`.

If the last digit is exceptional the last logarithmic error is unnecessary. Proof: apply P1 to `parent x`; the change in `S` on adjoining the last digit is either zero or a single representative cost at most `log(1/(2chi))/L`. This recovers the paper's weaker estimate without extra assumptions.

The direct crossing condition also gives the complementary inequality

`S_x >= c_L(v)-c_F(v)-Q_x-delta-Cchi K/L`.

This second inequality is used in the numerical large-block calculation because `theta-4<=0`.

### E1. Finite weighted KL/log-sum inequality

Let `a_l>=0`, `A=sum_l a_l`, let `r` be a probability vector, and let `theta in [3,4]`. Assume only that `a_l>0` implies `r_l>0`. Set

`H(a)=sum_{a_l>0} a_l log(A/a_l)` and

`S(a,r)=sum_{a_l>0} a_l log(1/r_l)`.

Then

`H(a) <= theta S(a,r) - A psi_r(theta)`.

When `A=0` all counts are zero and both sides are zero. Otherwise put `q_l=a_l/A` and `b_l=r_l^theta/Z`, where `Z=sum_l r_l^theta>0`. For every positive `q_l`, the elementary inequality `log t<=t-1`, applied to `t=b_l/q_l`, gives

`sum_{q_l>0} q_l log(b_l/q_l) <= sum_{q_l>0} b_l - 1 <= 0`.

Expand `log b_l=theta log r_l-log Z` and multiply by `A`. This proof needs neither a general measure-theoretic KL library nor positivity of every representative coordinate. Zero coordinates with zero counts are simply outside the support.

### E2. Profile entropy with deletion error

Sum E1 over the finite `(q,i)` cells of the profile. The support condition holds because counted good digits satisfy `r_i(l)>2chi>0`. Exact regrouping gives

`H_x <= theta S_x - L^-1 sum_{good j} psi_{r_i(j)}(theta)`.

By R5, deleting exceptional positions reduces the full representative sum by at most

`R_x (theta-1)log k <= 3 R_x log k`.

Hence, with the R4 error for `f=psi(theta)` denoted `epsilon_theta(s,u)`,

`H_x <= theta S_x-B_theta(s,u)+epsilon_theta(s,u)+3 R_x log k`.

After the truncation `R_x<=alpha_chi` this is the paper's entropy estimate, uniformly in `theta in [3,4]`. This does not need an additional time-cell error: summing the `(q,i)` counts already gives the full `(s,u]` interval exactly.

### T1. Exact partial binomial-count bound

For natural `K,h`, a real `a>=0`, and `0<z<=1`, set

`C(K,h,a)=sum_{q=0}^{min(K,h)} choose(K,q) a^q`.

Then

`C(K,h,a) <= z^(-h) (1+a z)^K`.

Proof: for `q<=h`, `z^h<=z^q`; multiply each nonnegative coefficient by this inequality, sum, enlarge the finite sum to `0<=q<=K`, and use the binomial theorem. Division by `z^h>0` proves the result. This proof covers `h=0`, `K=0`, and `a=0` under the usual natural-power convention.

### T2. Exact weighted upper-tail bound

For natural `K,h`, `a>=0`, and `z>=1`, set

`Tail(K,h,a)=sum_{q=h}^K choose(K,q) a^q`, with an empty sum if `h>K`.

Then

`Tail(K,h,a) <= z^(-h) (1+a z)^K`.

Proof: for `q>=h`, again `z^h<=z^q`; use exactly the same finite coefficient argument as T1. No probabilistic theorem or Stirling formula is needed.

### T3. Product-word exceptional-count mass

Let per-column bad-digit sets `B_j` satisfy `sum_{l in B_j}p_j(l)<=a`. Under the product-word weight `W(x)=prod_j p_j(x_j)`,

`sum_{x : #{j:x_j in B_j} >= h} W(x) <= Tail(K,h,a)`.

Proof: partition full words by their exact bad-position set `J`. For fixed `J`, drop the requirements at positions outside `J`; the resulting product probability is `prod_{j in J}sum_{l in B_j}p_j(l)<=a^|J|`. There are `choose(K,q)` sets of size `q`. Sum over `q>=h`.

An optional stronger statement, obtained by a union bound over subsets of exactly `h` bad positions, is `mass<=choose(K,h)a^h`. It is not needed for the generating-function route.

The expected discarded row count is at most `N` times the displayed mass. This factor must be present when turning a one-row probability into a row/edge estimate.

### T4. From discarded row mass to discarded edge contribution

For any family of full words `V`, each graph edge attributed to rows in `V` uses a row in `V`, hence `|E(G_V)|<=numberOfRows(V)`. Therefore

`sum_m P(edge_m in G_V)^2 <= sum_m P(edge_m in G_V)`

`= E |E(G_V)| <= E numberOfRows(V)`.

For deleting `V` from the full shared-edge first moment, the difference is at most **twice** this expected row mass: if `p_m=g_m+b_m` are the full, good, and bad edge probabilities, then `p_m^2-g_m^2=b_m(p_m+g_m)<=2b_m`.

This distinction prevents quietly dropping good/bad cross terms. An arbitrary target power is unaffected by a fixed factor two, but the finite theorem must include it.

### T5. Admissibility truncation with an explicit exponent

Before a left boundary crossing, each digit below `I_left(j)` has actual mass `<chi`; their combined mass is at most `k chi`. A non-admissible prefix has more than `C_bdry L/log(1/chi)` such positions. The corresponding full word therefore has at least

`h_b=floor(C_bdry L/ell)+1`, where `ell=log(1/chi)`.

Apply T3 with `a=k chi`; right boundaries are identical. For `ell>=4`, choose

`z=1/(chi ell^2)>1`.

T2 and `log(1+t)<=t` give

`expected discarded rows per side <= N^(1-C_bdry+2 C_bdry log(ell)/ell+T k/ell^2)`.

Indeed `h_b>=C_bdry L/ell`, `log z=ell-2log ell`, and `K log(1+k/ell^2)<=TL k/ell^2`. The error tends to zero as chi decreases. Taking `C_bdry>C_0+2` and then chi sufficiently small makes this at most a fixed factor times `N^(-C_0-1)`; for large N the two boundary sides and the factor from T4 fit within `N^(-C_0)`.

The stop time depends on the word but causes no issue: every removed stopped prefix is contained in the global event of having this many small digits. No summation over arbitrary incompatible prefixes is needed.

### T6. Exceptional-profile truncation with an explicit exponent

Each exceptional digit has actual mass `<=3chi`, so the combined exceptional mass per column is at most `3kchi` (and safely at most `4kchi`, as used by the sketch). A bad stable profile with `R_x>alpha_chi` belongs to the global event of at least `alpha_chi L` exceptional positions in the full word, because its continuation positions are a subset of all columns.

Set `alpha_chi=1/sqrt(ell)` and use T2/T3 with `a=4kchi`, `h_e=ceil(alpha_chi L)`, and `z=chi^(-1/2)`. Then

`expected discarded rows <= N^(1 - sqrt(ell)/2 + 4 k T sqrt(chi))`.

The exponent tends to minus infinity as chi decreases, so any fixed target `C_0` is reached with room for fixed union/cross-term factors. This repairs the proof without any false unweighted count of large exceptional sets.

### C1. Subpolynomial small-subset counting

Assume `N>=2`, `K<=T L`, `T>=0`, `k>=1`, `0<d<=1`, and natural `h<=d L`. T1 with

`z=d/(k(T+1))`

gives

`C(K,h,k) <= N^g(d)`,

where `g(d)=d(log(k(T+1)/d)+1)`.

Proof: `z<=1`; `-h log z<=dL log(k(T+1)/d)`; and

`K log(1+kz) <= K kz <= TL d/(T+1)<=dL`.

This is an exact finite estimate. Also `g(d)->0` as `d->0+`, by `d log(1/d)->0`. The source's `O(d log(1/d))` count is thereby justified for **small** exceptional sets, not upper tails of arbitrary size.

### C2. Admissible boundary-family counting

For fixed ambient word and boundary digit sequence, an admissible left prefix is encoded injectively by its length, its final digit, its at most `h_b'` strictly-below-boundary locations, and the digit at each such location. Every other nonterminal digit is forced to equal the boundary digit. The terminal no-crossing case is covered by the same code. Hence

`#admissibleLeft <= k(K+1) C(K,h_b',k)`;

the same holds for the right family, where `h_b'=floor(C_bdry L/ell)`.

The factor `K+1` counts possible stopping lengths and the factor `k` records the final crossing/terminal digit. Empty pairs only reduce the number. This explicit coding is safer than the old paper's compressed sentence about “at most k choices.”

### C3. Coarse and labelled profile counting

Let `D=R * (#simplexCells) * k` be the number of integer good-count coordinates. Each lies in `{0,...,K}`, giving at most `(K+1)^D` possibilities. For at most `h_e'=floor(alpha_chi L)` exceptional positions, the **coarse** profile of the current TeX has at most

`(K+1)^D C(K,h_e',1)`

possibilities for fixed boundary pair. A separate labelled refinement, additionally recording each exceptional digit, has at most

`(K+1)^D C(K,h_e',k)`.

For the refined total boundary/profile descriptions the resulting upper bound is

`k^2 (K+1)^(D+2) C(K,h_b',k)^2 C(K,h_e',k)`.

Combining C1 with `d_b=C_bdry/ell` and `d_e=1/sqrt(ell)` gives

`<=k^2 (K+1)^(D+2) N^(2g(d_b)+g(d_e))`.

For every epsilon, choose chi so `2g(d_b)+g(d_e)<epsilon/2`; after chi and the meshes are fixed, `D` is a fixed integer, and for sufficiently large N the polynomial-in-log prefactor is at most `N^(epsilon/2)`. Thus the class count is at most `N^epsilon` in the claimed parameter order. The coarse count is bounded by the refined count through forgetting labels, not by redefining the coarse profile.

### C4. Cardinality inside a fixed profile class

For a fixed **labelled** refinement, the number of possible continuations is at most the product of cellwise multinomial coefficients. The multinomial theorem, applied to the empirical distribution of each cell, gives the exact bound

`#class <= exp(L H_x)=N^H_x`.

Proof for one cell: if integer counts `n_l` sum to `n>0`, the probability of that type under independent draws with probabilities `n_l/n` is

`multinomial(n_l) * prod_{n_l>0}(n_l/n)^n_l <=1`.

All factors in the product over positive counts are positive; rearrange and take logarithms. The zero-cell case is `1<=1`. Multiply over cells. Legal/stable restrictions only decrease the number.

For the original **coarse** profile, exceptional digits are not specified; therefore only

`#coarseClass <= k^(#Q_x) N^H_x = N^(H_x+R_x log k)`

follows from this argument. The additional exponent is `o_chi(1)` after truncation, not `o_N(1)` for fixed chi.

## Definition/dependency DAG within the assigned part

- Probability vectors, legal words, column product weights, finite cell assignment, chi-regular partition -> R1, R5.
- Column times, finite grid, cell count discrepancy, measurable cell densities -> R2 -> R3.
- R1/R3 + integrability/simple-function decomposition + R5 -> R4 applications P2 and P3.
- Legal word costs, good/exceptional partition, normalized digit counts -> P1, nonnegativity of S and Q.
- Product weights/expected row counts + side-piece definition + boundary crossing -> P4 -> P5.
- P1 + parent stable-crossing predicate + good-digit logarithm bound -> P6.
- Positive-support finite counts + elementary `log t<=t-1` -> E1.
- E1 + finite profile regrouping + R4/R5 + R-bound -> E2.
- Binomial theorem + monotonicity of natural powers -> T1/T2.
- Product-word probabilities + finite exact bad-set partition -> T3.
- Row/edge cardinality + linearity of expectation -> T4.
- T2/T3/T4 + boundary threshold -> T5; R1 exceptional bound + same helpers -> T6.
- T1 + logarithmic inequalities -> C1; injective boundary code -> C2; finite count tuples and labelled subset code -> C3.
- Multinomial theorem/finite product probabilities -> C4.
- P1/P2/P3/P5/P6/E2 feed the numerical first-moment lemma; T5/T6/C2/C3/C4 feed the aggregation into `prop:ub-first-moment`.

## Issues that must be reported before a freeze

1. **Missing measurability.** The literal setup does not say that `t -> mu_t(D_i)` or `t -> integral f dmu_t` is measurable, although the paper integrates these quantities. A proof must not smuggle integrability in as a new hypothesis after freezing. A finite cell-measure formulation can be completed while this is clarified.

2. **Coarse exceptional-set definition versus later labelled counting.** Lines 722–724 record only exceptional positions; 2510 Definition 4.7 records `(position,digit)` pairs. Lines 1873–1876 of the current first-moment proof act as though digit values were included. They are not. Retain the coarse definition and distinguish a labelled refinement, or use the exact extra `R log k` exponent. This is a definition issue, not an invitation to silently change the frozen object.

3. **c_L is not fixed by even a labelled profile.** Current c_L uses actual good-coordinate logarithms. Cellwise counts use representative logarithms. For fixed boundary and labelled exceptions, S,Q,H,c_E,c_F are fixed, but c_L only has oscillation at most `2 Cchi K/L`. The old 2510 c_L was defined with representative good costs. Apply numerical bounds pointwise, or explicitly handle the finitely many block regimes; do not assert exact constancy.

4. **The unweighted exceptional-tail count is false.** Lines 1103–1105 claim the number of choices for all `q>=alpha L` is `exp(O(alpha log(1/alpha)L))`. Such a tail includes subsets of size about K/2, whose number is exponential in K with a nonvanishing exponent as alpha goes to zero. T2/T6 prove the required *weighted* tail directly.

5. **A factor N is missing from the displayed exceptional mass bound if “mass” means expected interval cardinality.** Formula 1101 is a one-row probability bound; T3 adds N. The final arbitrary polynomial decay remains valid because the exceptional exponent tends to minus infinity.

6. **Ambient and terminal times are asymptotic.** `M_w/L=r+o(1)` is not exact equality. `K/L=T+O(1/L)` is not exact `T`. P2/P3 retain the explicit errors before taking limits.

7. **Fluctuation comparison versus actual fluctuation.** The finite mean-based P5 is true, but the current root definition includes the deterministic first column in the side maxima. The old homogeneous paper explicitly starts at column 2 (2510 p.19). For example, with first-column positive masses on digits 0,1,2 and an interior first digit 1, current `y=z=(1)` and `c_F~1/2` arise from deterministic first-column side counts. A continuation `(1,0,0,...)` has a deterministic left endpoint at the first-pile boundary. Thus this c_F cannot by itself justify a positive-scale endpoint anti-concentration theorem. This is outside the assigned finite comparison but prevents claiming that its downstream probabilistic use is already sound.

8. **Error hierarchy.** The number of partition cells and time cells can depend on chi and Delta. The finite inequalities above retain these constants. Chi is fixed before N tends to infinity; `O(alpha_chi)` is not `o_N(1)`. The order “choose epsilon after chi” in lines 1909–1911 is unsuitable for C3: fix a desired class-count exponent first, choose chi to meet it, then take N large.

9. **No extra nondegeneracy is needed for the assigned deterministic estimates.** Adding local good-shuffle, uniform positivity of all digits, FM, or a positive lower bound on all representatives to make these proofs easier would be an unauthorized strengthening. Good support positivity and nonterminal genuine crossings already suffice where needed.

## Reconstruction verdict

The finite regular-cell, cost, maximal-pile, mean-based fluctuation, KL, weighted truncation, and class-count estimates above have direct proofs under the source's finite data. They can be formalized without axioms or placeholders. Their precise integral/asymptotic wrappers must wait for the measurability and profile-description choices to be resolved and frozen. The current coarse-profile cardinality assertion and the unweighted exceptional-tail counting sentence should not be implemented literally as stated. The deterministic-first-column issue also requires attention before using the resulting library to certify the whole upper proof.
