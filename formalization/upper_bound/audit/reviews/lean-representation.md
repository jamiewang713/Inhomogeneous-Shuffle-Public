# Independent Lean representation review

Sources independently read: `time_inhomogeneous_riffle_shuffle_unified_article.tex`; `2103.05068v3.pdf` (Sections 2, 3, 5, upper/lower architecture); `2510.22783v1.pdf` (Sections 2, 3, 5, relevant first-moment recursion). No other mathematical notes or agents' reports were read. No Lean source was written or modified. This document proposes interfaces; it does NOT freeze them or certify any unproved interface.

## 1. Existing implementation and trust boundary

There are no project `.lean` files, `lakefile`, `lake-manifest.json`, or `lean-toolchain` outside dependency/tooling caches, and `formalization/RiffleShuffle` is empty. A completed inhomogeneous first-moment theorem therefore cannot currently be imported or audited. Its declaration name, precise statement, proof dependencies, and representation are unresolved. Do not replace it by an assumption or structure field that asserts its conclusion.

Two incompatible toolchains exist: `formalization/.lake/packages/mathlib/lean-toolchain` specifies `leanprover/lean4:v4.33.1`; `formalization/.tooling/mathlib/lean-toolchain` specifies `v4.19.0`. The former has extensive cached `.olean` artifacts; the latter appears to be sources without matching build artifacts. `formalization/.tools/lean` points to the 4.33.1 distribution in another workspace. Use one coherent toolchain only and verify its version before imports. No theorem compilation was attempted before the requested freeze.

Trusted interfaces actually found in the 4.33.1 mathlib sources:

- `PMF.uniformOfFintype`, `PMF.uniformOfFintype_apply`, `PMF.toMeasure_uniformOfFintype_apply` in `Mathlib/Probability/Distributions/Uniform.lean`.
- `PMF.map`, `PMF.map_apply`, `PMF.map_comp`, `PMF.bind_map`, `PMF.map_bind`, `PMF.ofFintype`, `PMF.toMeasure_ofFintype_apply` in `Mathlib/Probability/ProbabilityMassFunction/Constructions.lean`.
- `Finset.sum_mul_sq_le_sq_mul_sq` in `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean`.
- `ConvexOn.map_sum_le` in `Mathlib/Analysis/Convex/Jensen.lean`.
- `SignedMeasure.totalVariation` exists, but finite real total variation should be defined as the half-L1 sum and related to it later only if needed.

These are interface observations, not an assertion that imports have compiled under a project configuration.

## 2. Representation recommendations

All finite-N upper-bound work can be done over finite sample spaces with exact finite sums. This avoids conditional-expectation versions on null atoms, unnecessary integrability obligations, and mistakes from changing sigma-fields. If the imported first-moment theorem uses measure-theoretic expectations, prove a finite-PMF integral bridge rather than rewriting that theorem.

### Basic finite objects

Fix natural numbers N, k, K. Use vertices `Fin N`, digits `Fin k`, column indices `Fin K`, and strings as functions `Fin K -> Fin k`. A fixed-count matrix is a function `(Fin N) -> (Fin K) -> (Fin k)` together with the predicate that for every column j and digit a its a-count equals n(j,a). A pile array n has natural entries and row sum N at every j. The matrix law is the uniform PMF on the finite subtype of valid matrices. Nonemptiness must be proved from the pile sums by constructing each column; it is not an extra assumption.

Prove that this uniform matrix law equals the independent product of uniform column laws. Rows are exchangeable, but generally are NOT independent. Define an independent pair by the product PMF, not by an informal use of the same random variable twice.

Sort rows lexicographically, retaining multiplicities. Prefixes should carry their exact natural length M <= K; use a dependent pair of length and digit function or a bounded list. Define the cylinder B_x, row set R_x, sorted rank interval I_x, prefix mass lambda_x = product over j<M of n(j,x(j))/N, and suffix collision product C2(M,K) = product over M<=j<K of sum_a (n(j,a)/N)^2. Handle N=0 independently; asymptotic results work eventually with N>=2.

Use path edges as positions e with e+1<N, represented by the finite subtype `{e : Nat // e+1<N}`. A graph is a `Finset` of these positions. Its adjacency in `SimpleGraph` can be a proved bridge rather than its primary representation. This makes intersections, directional subsets, and interval edge counts direct finite-set operations.

A component is an interval between consecutive absent edges. One convenient component index at vertex i is the number of absent path edges strictly before i. Prove equivalence with connectivity, partition of the vertices, interval convexity, and `sum_C (card C - 1) = card E`. Define `Fact(G) = product_C (card C)!`.

Permutations are `Equiv.Perm (Fin N)`. Define component sorting by the unique permutation preserving the set of values in every component and increasing on that component. Existence and uniqueness can be proved by sorting each finite set of values. A group-action alternative uses the subgroup of position permutations preserving components; either route must prove the fiber cardinality, not assume it.

### Shuffle law and composition orientation

The actual inverse-shuffle law must be defined independently of graph sorting, for example by the physical uniform-interleaving kernels and inversion, or by a separately proved stable-sort kernel. Defining it to be the graph mixture would make the representation theorem tautological.

Chronology and lexicographic order must be fixed explicitly. In repeated stable sorts, the last applied column is most significant. The 2025 Proposition 2.2 recursive prefix-refinement argument supplies the appropriate coupling for the stated chronological shuffle product. Do not exchange or reverse unequal time columns merely because that was harmless in the homogeneous case.

### Finite probability and conditional histories

For a PMF P on a finite type and real X, use E_P X = sum_w (P(w)).toReal * X(w). Probability of an event is the corresponding indicator sum. A history H is a finite-valued map. On an atom h with positive mass, define E[X | H=h] as the weighted sum over the fiber divided by its probability. All conditional assertions quantify over positive-mass histories. This is equivalent to the usual almost-sure statement and excludes no actual samples.

For a directional exploration, history at step i reveals the appropriate sorted strings within one deterministic first-pile interval, in forward or reverse order. Use a finite vector/list for the history and prove that the previous history is a function of the next. Good-history predicates must be functions of the individual history. The pair good event is the intersection of the two individual predicates; final typicality is a single-matrix event intersected across all directions and steps.

### Profile layer

A measurable time family of probability measures on the simplex is needed to interpret the profile integrals. The source calls it a family but does not explicitly supply measurability. The actual first-moment declaration may already settle this. Do not silently introduce regularity of t -> mu_t beyond what is necessary and agreed.

Use the exact source quantities a, psi, A, B_theta, beta, and FM. At finite N use exact r=M/log N and exact size exponents, with explicit error parameters where the source writes o(1). Accessible blocks must be defined from the specified exploration/conditioning support; `accessible` cannot remain an uninterpreted predicate whose axioms assert whatever the proof needs.

## 3. Candidate theorem interfaces and dependencies

The following list includes each family needed for the assigned upper bound. It is a dependency contract, not a list of permissible new final hypotheses. Technical estimates in items P/E/R must be proved from the original frozen model assumptions and the imported first-moment theorem.

### F: finite model and shuffle representation

F1. From nonnegative integer pile sizes summing to N in each column, the fixed-count matrix subtype is nonempty and its uniform law factors over columns.

F2. For every prefix x, E|R_x| = N lambda_x. For any R distinct labeled rows and a specified digit array, the probability is the product over columns of [product_a (n(j,a))_(m(j,a))]/(N)_R, with zero impossible cases included.

F3. Row relabeling preserves the matrix law. Conditional on the sorted string multiset, row assignments are uniform among assignments with that multiset.

F4. Component sorting has image exactly the permutations increasing along every graph edge; every image fiber has cardinality Fact(G). Consequently P_unif(sort_G(pi)=sigma) = 1_sorted(G,sigma) Fact(G)/N!.

F5. The independently defined inverse K-shuffle law equals the mixture, over valid uniform matrices S, of sort_{G(S)}(pi) for independent uniform pi. Dependencies: F1, F3, F4, and the proved composition/refinement coupling.

### D: density/Radon-Nikodym algebra and truncation

D1. Define f(G,sigma) = 1_sorted(G,sigma) Fact(G), and f2(G,H) = E_sigma[f(G,sigma)f(H,sigma)]. Then f>=0 and E_sigma f=1. Its PMF-density interpretation follows from F4. The mixture density is E_S f(G(S),sigma). Dependencies: F4, F5.

D2. For every pair G,H, f2(G,H) = Fact(G) Fact(H)/Fact(G union H). Dependencies: D1 and the fact that simultaneous sortedness is sortedness on the union.

D3. Generic finite-density truncation: for any finite index law P, finite outcome law Q, f>=0 with E_Q f(s,.)=1, and a SINGLE-index event A, write rho(x)=E_P f(.,x). Then

    TV(rho*Q,Q) <= (1/2) sqrt(E_{P x P}[(E_Q f(s,.)f(s',.) - 1) 1_A(s)1_A(s')]) + P(A^c).

The radicand equals E_Q[(E_P[(f-1)1_A])^2] and hence is nonnegative. This identity must precede taking the square root. f2-1 is not pointwise nonnegative: incident but nonshared constraints can give f2<1. Dependencies: finite Fubini, normalization, weighted Cauchy-Schwarz. No homogeneity or first-moment assumption.

D4. Mixture TV inequality for random piles: TV(sum_c q_c P_c,U) <= sum_c q_c TV(P_c,U) <= sup_{c in A} TV(P_c,U)+P(c notin A). Dependencies: triangle inequality for the finite L1 sum. This is the upper random-pile extension, with no independence assumption among pile vectors.

### C: factorial and sparsity combinatorics

C1. For positive integers m_i and M with sum_i(m_i-1)<=M-1, product_i m_i! <= M!. Prove by induction or factorial comparison. This is the exact combinatorial inequality used in 2021 Lemma 3.1.

C2. For union components U, f2(G,H) <= product_{U containing a shared edge} |U|!. Components without a shared edge contribute at most 1. Dependencies: D2, C1, component partition/cardinality identities.

C3. Define L-sparse for integer L>=10: every consecutive vertex interval of length L wholly inside [N] contains <=L/3 graph edges, interpreted as 3*edgeCount<=L to avoid rational rounding. If G and H are L-sparse then each union component has <=L vertices. If N<L this follows from the total number of vertices, not from a nonempty family of L-windows. Dependencies: path interval connectivity and 2L/3<L-1.

C4. Under C3, f2(G,H) <= (L!)^(card(G intersect H)). Dependencies: C2, C3, inject one shared edge from each contributing union component.

### P: guards, edge covering, and block geometry

P1. Define exact deterministic first-pile rank interval J_p of length n(0,p), with empty intervals allowed. No edge of a shuffle graph crosses its boundary. Dependencies: sorted rows and fixed first-column counts.

P2. Select an initial good column and two subsequent nearby good columns using a pigeonhole argument from local good-column density. If a prefix is discarded to achieve this, prove TV contraction AND re-evaluate the time profile/margins at the absolute shifted times. The shift is O(rho log N), not an innocuous homogeneous symmetry. Alternatively develop guards without discarding; this requires explicitly tracking their mass.

P3. Given lower and upper guard prefixes l_p<r_p in J_p, define forward edges by equal strings <r_p and backward edges by equal strings >l_p. The deterministic cover theorem should assume explicit endpoint-count bounds on each S and S': enough overlap of the forward rank range and backward rank range implies every common edge lies in one of the 2k common directional edge sets. Formulate rank bounds in 0-based half-open intervals to avoid the endpoint arithmetic inconsistency in the paper. Empty and singleton J_p need no strict mass inequality.

P4. Prove the guard overlap and its concentration from selected good columns, including small first piles. Source statements `lambda_left+lambda_right < (1-vartheta)n_p/N` cannot hold when n_p=0; this is a zero-pile edge case, not a reason to assume all pile sizes positive. Do not freeze that strict inequality for every p as written.

P5. A lex interval of length-K strings between a current string and its directional guard is the disjoint union of at most 2kK prefix cylinders. Refine prefixes to just before a nearby good column when enough tail remains. The refined count is at most 2kK*k^(c rho log N+c0), NOT literally O(log N); this count loss must be budgeted explicitly. Dependencies: finite lex order, local good columns.

### E: exploration conditioning and comparison

E1. Conditional-reservoir representation (2025 Lemma 5.7): a positive-mass forward history ending at s, with y revealed copies of s, is represented by a uniform finite set of residual matrices. It has: residual column counts after deleting only strings strictly before s; a distinguished first-pile reservoir; all its rows >=s; at least y copies of s; other rows from outside that first pile. Prove the precise finite bijection/fiber multiplicity. This representation is substantially stronger than saying residual columns are hypergeometric.

E2. Finite conditional high-probability upgrade: if P(B^c)<=q then P(P(B^c | H)>sqrt q)<=sqrt q, for q>=0. Its event is history measurable. Dependencies: finite Markov inequality and tower identity.

E3. For independent random edge sets A,B on a finite edge universe,

    E|A intersect B| <= (E|A intersect A'|+E|B intersect B'|)/2.

Conditioning on separate histories preserves independence, so this holds atomwise for the pair. Proof: 2ab<=a^2+b^2 for edge inclusion probabilities.

E4. Refining a history increases the A-with-copy self-intersection expectation AFTER averaging the refined conditional quantity over the original history. Exact statement: sum_e P(e in A | H)^2 <= E[sum_e P(e in A | H,Z)^2 | H]. This is finite Jensen. It is not a pointwise inequality for each realized Z. The two copies must be independent conditioned on the SAME H,Z.

E5. Given a prefix cylinder wholly beyond the current history, condition additionally on its labeled row set/rank interval AND its entire array of tail-column counts. The residual tail within that block is uniform with those counts; after independent conditional resampling, it is exactly a pair of independent fixed-count block shuffles. Prove this by finite columnwise completions. Merely conditioning on the interval is insufficient because it does not fix the tail pile counts.

E6. Forward and backward generic histories may use a common reversed-order abstract lemma, but reversing direction does not reverse macroscopic time or make tails homogeneous. Prove a digit-order involution sends lower to upper guards and transforms every pile vector accordingly.

### R: quantitative conditional estimates and first-moment input

R1. On a history-measurable good event, uniformly for admissible future prefixes x and fixed sample size m, prove a residual sampling bound of the form

    P(m selected reservoir rows have prefix x | further reservoir history)
      <= C_m * lambda_x^(m(1-epsilon)) * N^(m epsilon),

with all quantifiers, good-event failure, epsilon, and guard constants fixed BEFORE coding. There is a separate repeated-current-string bound when the complementary reservoir already contains its required y copies. This prevents forced copies from being treated as rare. Dependencies: E1, E2, good-column guard, exact finite matrix counts; this is the content of 2025 Sections 5.3-5.4, not supplied by first moments alone.

R2. Derive on good histories: conditional expected future block size <= C N lambda_x^(1-epsilon) N^epsilon; conditional expected remaining copies of current full string <= the corresponding full-string bound; conditional expected edges in a prefix block <= C N^2 lambda_x^(2-epsilon) C2(M,K) N^epsilon. Dependencies: R1 and a two-row collision estimate. State the collision product explicitly for the inhomogeneous tail, then apply profile approximation.

R3. Large-block concentration: for prefixes with N lambda_x>=N^xi, conditional on a good history, block size and every sufficiently large-pile tail count have specified tolerances (e.g. (N lambda_x)^(4/5)) with conditional failure <= exp(-N^c). The good-history event itself has failure <= exp(-N^c'). Dependencies: unconditional fixed-column prefix concentration, E2, the actual history/reservoir law. A union bound over all necessary prefixes/columns is required.

R4. Robust first-moment application to each conditioned large block. Needed imported interface: expected common adjacent edges for an independent pair of fixed-count tail shuffles of actual size m, at absolute time M/log N and actual exponent b=log_N m, under numerical FM and the actual (possibly weak/perturbed) profile condition of those tail counts. Conditional tail arrays fluctuate, so the exact source theorem's interface matters. Dependencies: E5, R3, accessible-size bound, margin monotonicity, imported theorem and a proved perturbation transfer.

R5. Unrevealed common-edge estimate on every positive-mass good pair history. Decompose into: remaining copies of the currently revealed string; very small prefix blocks, handled by expected size; near-critical small blocks, handled by R2 collision product plus a positive remaining tail cost; large blocks, handled by R4 and conditional bad-event contribution <=N exp(-N^c). Sum over P5's actual prefix count. Dependencies: E3/E4 with their averaging intact, R2/R3/R4, RFM. Desired conclusion is <=C N^(-delta), uniformly in step and direction.

The source's phrase `bound small blocks directly by total size` does not handle near-critical blocks of expected size near 1 or N^xi. A total-size bound then is not o(1); the separate collision-tail estimate is essential.

### M: a correct Portenko interface and exponential moment

M1. Generic finite adapted counting theorem. Fix a finite law, a finite filtration represented by history maps H_i for i=0,...,m, and adapted natural counts X_i with X_0=0 and increments in {0,1}. Let good_i be H_i-measurable. For every positive history atom, assume

    good_i -> E[X_m-X_i | H_i] <= gamma.

This is a generic theorem hypothesis; in the shuffle application it must be supplied by the proved R5, not added as a new model assumption. Define Y to count increments only before the first failed good_i, and A=intersection_i good_i. Then Y>=X_m*1_A, and the adapted killed count itself has conditional future mean <=gamma. For 0<=gamma<1, prove P(Y>=r)<=gamma^r by disjoint decomposition over the first time the count reaches r (an event in the ORIGINAL history). No terminal event is added to the filtration.

M2. If t>=0 and exp(t)*gamma<1, conclude

    E[exp(t X_m) 1_A] <= E[exp(tY)] <= (1-gamma)/(1-exp(t)*gamma).

In particular when exp(t)*gamma<=1/2,

    E[(exp(t X_m)-1) 1_A] <= 2 exp(t)*gamma.

This excess-MGF form is cleaner than subtracting 1 from an expectation with a truncation indicator. Dependencies: M1 and a finite/geometric series bound. Do not appeal to an unproved external Portenko theorem.

M3. For q=2k directional counts X_d covering C=card(G intersect G') on a single-matrix product event A x A, and a>=1,

    (a^C-1)1_(A x A) <= (1/q) sum_d (a^(q X_d)-1)1_(A x A).

Dependencies: cover, convexity of exp, q>0. M2 at t=q log a for all directions therefore yields the shared-edge excess exponential estimate, with q fixed independent of N.

M4. High-probability sparsity needs conditional SINGLE-graph edge bounds from R2/current-copy control, not just R5's shared-edge bound. On the adapted good event, the probability of r prescribed directional edge successes is <=p_N^r. A robust union bound gives, with q=2k and r> L/(3q),

    P(not L-sparse) <= P(not good/regular)+q*N*2^L*p_N^r.

Choose fixed L so delta*r>2 when p_N<=C N^(-delta). This route does not need the paper's unjustified assertion that every short vertex interval intersects at most two first-pile intervals (tiny/zero piles make that assertion unreliable). The harmless extra fixed k factor only changes the required L.

### U: deterministic and random TV completion

U1. Let A_N be the intersection, for one matrix, of all directional good-history events, cover regularity, and L-sparsity. Prove P(A_N^c)<=C/N (or an explicit quantity tending to 0). Dependencies: R3/E2, P4, M4.

U2. Apply D3 and C4 on A_N x A_N, then M3 with a=L!. If the resulting shared-edge excess bound is <=C N^(-delta), conclude

    TV(P(n,K),U_N) <= (sqrt C/2) N^(-delta/2)+C'/N.

Dependencies: F5, D3, C4, R5, M1/M2/M3, U1. The theorem is not complete until R5 and M2/M3 are proved and supplied by this actual model.

U3. Make constants and N0 uniform over deterministic cut arrays satisfying the frozen hypotheses. Random piles then follow from D4 and probability 1-o(1) of admissible arrays. No averaging argument can compensate for a nonuniform deterministic convergence rate.

## 4. Full proof DAG, including lower bound and random piles

Shared setup -> fixed-count matrix model -> exact factorial row probabilities and hypergeometric estimates -> profile/Riemann-sum cost estimates.

Upper branch:

- Matrix exchangeability + component sorting fibers -> graph representation -> density identities -> truncated chi-square.
- Path components + factorial comparison -> sparse factorial bound.
- Local good columns + absolute-time shift/margin control -> guards -> single-matrix regularity -> forward/backward common-edge cover.
- Lex interval cylinders + local good columns -> refined exploration block partition.
- Residual matrix conditioning + finite counting + good-history projection -> conditional prefix/current-copy/collision estimates and large-block concentration.
- Large-block conditioning law + robust first-moment theorem + recursive margins -> large-block conditional first moment.
- Small-block collision estimates + large-block first moment + conditional-copy comparison + refined block count -> unrevealed shared-edge estimate.
- Adapted killed exploration -> geometric tails -> directional excess MGF -> shared-edge excess MGF.
- Conditional single-edge estimate -> sparsity probability.
- Typicality + truncated chi-square + sparse factorial bound + shared-edge MGF -> deterministic TV upper bound -> uniform random-pile upper bound.

Lower branch in the active latter half of the TeX (the earlier overview is inside a comment environment):

- Successive hypergeometric thinning -> iterated thinning -> largest-prefix occupancy -> large increasing component -> largest-prefix lower bound.
- Entropy inequalities + bridge-window cost control + reduced upper-margin witness -> cold-witness reduction with parameters s,u,theta.
- Truncated theta-tilted type estimates -> relative cold-prefix intervals and geometry.
- Two good bridge columns + tail 2-tilted types + relative endpoint control -> bridge buffers -> localization.
- Fixed-column factorial moments -> conditional factorial moments -> central-window comparison -> two-category Poisson approximation -> occupancy approximation -> many cold collisions/edges.
- Uniform translate-scan ascent test + component-value bounded differences + Lalley component comparison -> Lalley cold-spot test -> cold-spot lower bound.
- Positive Lambda0 selects largest-prefix branch; otherwise positive Lambda1 selects cold branch -> buffered matching lower bound.

Random-pile lower extension is distinct from D4: lower bounds do not generally survive averaging. It requires a common test, or a union of deterministic tests whose uniform false-positive probabilities beat the number of possible cut arrays. With k fixed and K=O(log N), the number of arrays is at most (N+1)^(kK)=exp(O((log N)^2)); a uniform exp(-N^c) false-positive bound survives this union. Typical-cut probability and shuffled-law power must also be uniform. This is structural context; the assigned work is upper bound.

Margin-analysis branch: profile definitions -> one-column entropy inequalities -> dominance of Lambda2/Lambda3 by Lambda0/Lambda1 -> buffered upper margins -> critical-time upper bound. Do not confuse this numerical branch with the unproved exponential branch.

## 5. Freeze blockers and failed homogeneous substitutions

1. **Missing actual first-moment theorem.** No source declaration can be imported or checked. Its exact block law, conditioning, normalization, perturbation tolerance, parameter order, and axiom dependencies are unknown.

2. **Literal conditional profile preservation is false.** The TeX uses an exact fixed partition cell-count notion of almost-time-profile-likeness. Small perturbations of a pile vector can cross a cell boundary with order-one probability. For example take k=2 and all original tail vectors (1/2,1/2), with a regular partition having a boundary at p0=1/2 and assigning that boundary to the left cell. In a prefix block containing N/2 labeled rows, each tail within-block first pile count is hypergeometric around N/4. Its normalized vector lies on either side with probability bounded away from zero, independently across independent tail columns before extra conditioning. A positive fraction of columns moves to the other cell although all original columns belonged to one cell. Coordinate concentration therefore cannot imply that the same exact cell frequencies persist. The 2025 proof explicitly invokes a weak-almost-like first-moment extension to handle this. The current theorem statement does not supply it. A proved robust transfer or an already robust imported theorem is needed; do not add it as an assumption after freeze.

3. **Conditional law is not IID rows or independent unconditioned columns.** Sorted histories impose lexicographic inequalities and minimum multiplicity constraints. E1 and the m-row matrix counting are indispensable. The 2021 IID-uniform-interval argument cannot be substituted.

4. **Conditional-copy inequality requires averaging.** In 2025 (5.10), the display passes from the conditional average of self-intersections to a pointwise quantity under an enlarged history, and then says `by symmetry` to select one history. The valid application controls the average of BOTH conditional self-intersections uniformly; symmetry does not compare two fixed unequal histories.

5. **Printed Portenko proof has a tower error.** 2025 Lemma 5.4 adds the final good-event indicator to the filtration, then interchanges conditional expectations as though the new sigma-field were smaller. Conditioning on future survival changes the law. M1's killed adapted process repairs the proof without new model assumptions.

6. **Single typical event versus pair event.** The TeX calls S1 both a set of individual matrices and an event that both matrices are regular/sparse. D3 requires a single-matrix event A and product A x A. A rare arbitrary pair event cannot be discarded in the same truncation step.

7. **Initial good columns and chronology.** Homogeneous time shifts preserve the reference distribution; inhomogeneous shifts move the profile. P2 must prove the absolute-time margin transfer. Local density does yield nearby good triples by a pigeonhole argument, but this needs an exact finite statement and buffer budget.

8. **No small-block shortcut.** Total size is insufficient for blocks with expected size near 1. The inhomogeneous tail collision product and a uniform tail-cost margin are required.

9. **Fixed partition and small piles.** Do not infer `all n_p>0`, a uniform p_min, or concentration relative to a tiny expected count. Empty first-pile intervals and exceptional digits must be handled explicitly. The source's strict guard margin at n_p=0 is false.

10. **Sparsity does not follow from common-edge first moments.** It needs marginal repeated-string estimates or a separate high-order collision argument. A single random graph can have a large component with a diffuse random location even if two independent graphs rarely intersect.

11. **Asymptotic quantities must become quantified contracts.** O(N^-delta), o(1), accessible b+o(1), and `sufficiently small` cannot be fields left unspecified. The final declaration must quantify positive constants, parameter choices, and one uniform N0; all error losses must fit before the freeze.

No global freeze is currently justified. The finite model/RN/factorial/abstract stopped-process statements above can be finalized independently after cross-agent comparison, but completing only those would not complete the assigned upper bound.
