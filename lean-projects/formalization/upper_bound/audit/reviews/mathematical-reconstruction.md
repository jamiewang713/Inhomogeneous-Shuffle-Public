# Independent mathematical reconstruction — pre-freeze review

Research sources read: `time_inhomogeneous_riffle_shuffle_unified_article.tex`, `2103.05068v3.pdf`, `2510.22783v1.pdf`, and nothing from other project notes or Lean files. The two PDFs were extracted to `/tmp/*-math-review.txt`. No Lean has been written and no source has been modified. This report reconstructs mathematical obligations; it does not certify that the whole upper bound is proved.

## 1. Whole proof and dependencies

Common root: fixed integer k >= 2; N cards; K = floor(T log N); each deterministic column vector n^(j) has nonnegative integer entries summing to N. Independently sample each column uniformly among assignments with these counts. Row strings are then sorted lexicographically. The single-row product cylinder weight is lambda_x = product_{j<=|x|} p_j(x_j), where p_j = n^(j)/N. A prefix cylinder B_x gives a contiguous random interval I_x in the sorted row list. The graph G has edge i exactly when sorted strings i and i+1 agree. Two independent matrix samples give G,G'.

Time-profile root: a_p = log(1/max p), psi_p(theta) = -log(sum p_l^theta), tilted laws p^[theta], costs I_p(theta), entropies H_p(theta); average against mu_t and integrate to A(r,s), B_theta(r,s), J_theta(r,s). Additivity and nonnegativity feed all margin comparisons. The exact almost-profile condition is a finite partition cell-count condition on rho-grid time intervals. The local good condition is a lower bound gamma rho log N on the number of columns having at least two coordinates >= chi in each relevant rho interval.

The upper dependency chain is:

1. Fixed-count matrix law -> inverse-shuffle graph representation -> component sorting density -> exact two-graph density -> truncated chi-square.
2. Integer-path component combinatorics -> union-component factorial inequality -> sparse factorial inequality.
3. Legal prefix tree, ambient exponent b, c_L, c_E, boundary crossings, admissible boundary pairs, stable blocks, space-time digit profiles -> stable partition and boundary decomposition.
4. Regular partition/interval blocking + profile estimates + hypergeometric estimates + ambient conditioning transfer -> ambient concentration/anti-concentration.
5. Bad-profile reduction + stable localization + edge-density bounds + terminal singleton bound + numerical FM margin lemma -> **completed first-moment proposition**, treated as an intended input rather than reproved here.
6. Local good columns + convolution contraction + margin stability under a short initial deletion -> first good column and two nearby good columns; directional cutoffs and single-matrix regularity -> 2k-way shared-edge covering.
7. Conditional matrix-completion counting + reservoir concentration + adapted good events -> conditional block-size bounds, current-string repetition bounds, small-block collision bounds, and large-block count concentration.
8. Lexicographic interval prefix decomposition (+ bounded-delay refinements, if needed) + conditional independent replicas + AM-GM + conditional Jensen + exact block self-reduction + a **proved robust application of the first-moment input** -> conditional unrevealed shared-edge bound.
9. Adapted killing/geometric tail argument -> directional truncated exponential excess; convexity -> shared-edge factorial exponential excess.
10. Current-string repetition bound + sequential joint success bound -> local sparsity with probability 1-O(N^-1).
11. Single-matrix typical set + items 1,2,9,10 -> TV upper bound.
12. Convexity of TV under mixtures + uniformity over deterministic cut sequences -> random-pile upper bound.

Margins: beta(s)=1-A(0,s); Lambda_0=beta(T); Lambda_1 is sup_{s<=u} inf_{theta in [3,4]} ((theta+3)/2 beta(s)-B_theta(s,u)-2B_2(u,T)); Lambda_2 uses (theta-1)/2; Lambda_3=sup_s(beta(s)-B_2(s,T)). The one-column inequality psi_p(theta)>=(theta-1)a_p gives Lambda_2,Lambda_3<=Lambda_0. Additivity gives maximal accessible b_r=1-A(0,r), and monotonicity in b transfers global buffered margins to FM(r,b,T,eta) for b<=b_r, subject to explicit finite-N error budgets. Margin monotonicity in T gives the reduced critical-time upper result after the deterministic theorem is established.

The lower dependency chain in the active part of the TeX (starting around line 2790; the earlier lower overview is inside a comment environment) is:

* Graph representation + product weights + successive hypergeometric thinning -> large maximal prefix/full-string block when Lambda_0>0 -> long contiguous increasing run -> separating test.
* One-column entropy inequalities + buffered bridge window + Lambda_1 witness reduction -> (s,u,theta), maximal ambient prefix a_s, and positive buffers for h, Gamma-h/2, entropy-versus-width, endpoint fluctuations, and full-string occupancy.
* Regular cells + truncated tilted type classes -> prefix/tail type estimates -> relative deterministic cold set H_rel, its size, and boundary bound.
* Iterated hypergeometric thinning + relative endpoint theorem + bridge buffers -> localization into the random translate H_{L_{a_s}}.
* Exact fixed-column factorial moments -> conditional factorial moments -> central-window comparison -> two-category Poisson approximation -> occupancy mean/variance -> many distinct cold collision strings -> many cold graph edges.
* Uniform translate-scan ascent concentration + component-sorting ascent comparison -> Lalley scan test -> cold lower bound.
* Split Lambda_0>=kappa_0 versus Lambda_0<kappa_0 and Lambda_1>=eta -> matching buffered lower bound.

Random lower extension is separate from mixture convexity: take a union of deterministic separating tests over all possible cut sequences and translates. For fixed k and K=O(log N), the number of count arrays is at most (N+1)^(kK)=exp(O((log N)^2)); uniform false-positive probabilities must be exp(-N^c) to survive this union. Merely averaging deterministic TV lower bounds would be wrong.

## 2. Statements that can be fixed without time-homogeneity

### Graph representation

For any fixed count array, if pi is uniform on permutations and independent of the matrix, component sorting pi_G has the same law as the inverse shuffle permutation. This needs a precise definition/order of composing the elementary inverse shuffles. Proof: induction in K; append a uniformly permuted fixed-count column and refine sorting only within previous equal-prefix blocks. The 2025 Proposition 2.2 proof uses no homogeneous assumption.

### Density and exact second moment

For a deterministic path subgraph G, define V(G)=product_C |C|!, over its connected components. Then

* density f_G(sigma) = V(G) * 1_{sigma increasing on every G-component};
* E_uniform f_G = 1;
* if U=G union G', then f_{G,G'}=E_uniform(f_G f_G')=V(G)V(G')/V(U).

The fiber of component sorting has exactly V(G) permutations. The event of increasing along both graphs is exactly increasing along U. No independence of adjacent ascent indicators is needed.

### Truncated chi-square

Let A be a **single-matrix** event, and let S,S' be independent with the original matrix law. Then

TV(P,uniform) <= (1/2) sqrt(E[(f_{G,G'}-1)1_{A(S)}1_{A(S')}]) + P(A^c).

The radicand equals the uniform average of the square of E_S[(f_G-1)1_A], hence is nonnegative even though f_{G,G'}-1 need not be pointwise nonnegative. This identity is essential; replacing A x A by an arbitrary pair event is not justified. Dependencies: graph representation, finite sums/Fubini, density mean one, Cauchy-Schwarz.

### Factorial component and sparse bounds

For U-components C, f_{G,G'} <= product_{C containing a shared edge} |C|!. Proof uses the elementary inequality product_j m_j! <= M! whenever sum_j(m_j-1)<=M-1. In a U-component with no shared edge, the G- and G'-component edge counts collectively total at most |C|-1, so its density factor is <=1. Otherwise bound each separate numerator factor by |C|!.

Define L-sparse for integer L>=10: every L-vertex interval has at most L/3 edges (equivalently 3 times the edge count <=L). If G,G' are L-sparse, U cannot contain an L-vertex connected interval because 2L/3<L-1. Thus each U-component has size <=L (indeed <L whenever an L-vertex interval exists), giving f_{G,G'} <= (L!)^(number of shared edges). This also covers N<L, since then every component already has size <L.

### Finite random-subset reductions

For independent random subsets A,B of a finite universe and independent replicas A',B', E|A intersect B| <= (E|A intersect A'|+E|B intersect B'|)/2, by per-edge ab<= (a^2+b^2)/2.

For a random subset A and extra finite information H, the average conditional replica intersection is at least the unconditional replica intersection, by (E q)^2<=E q^2 for each edge. The conditional version must keep the outer conditional expectation over H. The 2025 proof around (5.10) drops this averaging and invokes symmetry too aggressively; use the averaged inequality and bound both terms separately.

### Lexicographic prefix decomposition

An open lexicographic interval of length-K words is a disjoint union of at most 2kK prefix cylinders. Take maximal cylinders contained in the interval. At each depth at most two partially intersected cylinders can have children entering the decomposition. Legal words/zero probabilities may be handled by deleting empty cylinders; the combinatorial statement is for the full finite alphabet.

## 3. Directional definitions and covering to freeze

After a justified short initial deletion, let column 1 be good, and let 1<a_2<a_3<=D be two later good columns, with D depending only on the local good density. Let l_j=min{l:p_j(l)>=g}, r_j=max{l:p_j(l)>=g}, using the given good threshold g.

For first digit p, define the right cutoff prefix R_p=(p,r_2,...,r_{a_3}) and left cutoff L_p=(p,l_2,...,l_{a_3}). Define forward strings to have first digit p and prefix through a_3 strictly below R_p, backward strings similarly strictly above L_p. A directional edge of G is an equal-string edge with its string in that class. A shared directional edge is in that direction for **both** graphs. The first-digit vertex intervals are deterministic because column-1 counts are fixed.

An exact useful covering lemma: on each deterministic first-digit interval of size n_p, let badLeft(G),badRight(G) count strings outside the backward/forward classes. If deterministic upper bounds bLeft_p,bRight_p apply separately to both samples and bLeft_p+bRight_p<n_p, the forward and backward shared-edge sets cover all shared edges in that part. State empty/singleton parts separately or use integer endpoint counts; the strict inequality is impossible for an empty part but no edges exist there.

The manuscript's declaration that 2k directional explorations cover all edges is currently a missing definition/proof, not an input that follows from first moment. The 2025 Definitions 3.6-3.8 and Lemmas 3.9-3.10 supply a blueprint, but rare/zero first piles require explicit handling.

## 4. Exact repaired finite Portenko theorem and proof

Let (Omega,P) be finite, (F_i)_{0<=i<=m} an increasing filtration, and A_i an F_i-measurable integer variable. Assume A_0=0 and A_{i+1}-A_i is either 0 or 1. Let B_i in F_i be good events, let B=intersection_{i=0}^m B_i, and let gamma>=0. Assume for every i<m,

1_{B_i} E[A_m-A_i | F_i] <= gamma 1_{B_i}.

At i=m the same inequality is automatic. For t>0 with exp(t)*gamma<1,

E[(exp(t A_m)-1)1_B] <= (exp(t)-1)*gamma/(1-exp(t)*gamma).

Consequently E[exp(t A_m)1_B] <= 1+(exp(t)-1)*gamma/(1-exp(t)*gamma), and if exp(t)*gamma<=1/10 this is <=1+2exp(t)*gamma. Any smaller terminal event C subset B may replace B on the left of the nonnegative exponential-excess bound.

Proof, without enlarging the filtration by B:

For j>=1 let T_j=min{i:A_i>=j}, with a cemetery value if never reached; set T_0=0. Unit increments give A_{T_j}=j whenever T_j is finite. Let C_j be the event that T_j is finite and every B_i up to T_j holds; let C_0=B_0. Each C_j is F_{T_j}-measurable. Because C_{j+1} subset C_j intersect {A_m>A_{T_j}}, sum over the finitely many values i of T_j and apply conditional Markov on C_j intersect {T_j=i} subset B_i. This proves P(C_{j+1})<=gamma P(C_j), including j=0; the i=m term is zero. Thus P(C_j)<=gamma^j. Since B intersect {A_m>=j} subset C_j,

P(A_m>=j,B)<=gamma^j.

For an integer a>=0, exp(ta)-1=(exp(t)-1) sum_{j=1}^a exp(t(j-1)). Interchange the finite sums and insert the tail bound. Sum the resulting geometric series to obtain the assertion.

This is an adapted killed-exploration proof. In the 2025 Lemma 5.4 proof, replacing sigma(a_i,a_i') by sigma(a_i,a_i',1_B) invalidates the displayed tower-property step. The conclusion is recoverable by the proof above with the original filtration. For the graph exploration, A_i counts revealed shared directional edges; revealing one vertex produces at most one new such edge. If the source provides the conditional estimate only before the penultimate position, its separately imposed cutoff endpoint event must make the remaining directional count zero there. This supplies the last B_i inequality rather than adding an assumption.

## 5. Conditional estimates actually required

Fix a direction and history a_i in one first-digit part. Future strings greater than the current string and before the directional cutoff decompose into prefix cylinders. On a history-measurable good event F_i with P(F_i^c)<=exp(-N^c), the proof needs four different estimates:

(a) For every future prefix x, E[|I_x| | a_i] <= C N lambda_x^(1-alpha) N^epsilon.

(b) For the current full string s_i, E[#{j>i:s_j=s_i} | a_i] <= C N lambda_{s_i}^(1-alpha) N^epsilon.

(c) For every future prefix x of length M,
E[|E(G_{B_x})| | a_i] <= C N^2 lambda_x^(2(1-alpha)) exp(-sum_{j>M} psi_{p_j}(2-2alpha)) N^epsilon.
The power/cost losses must be quantified and chosen below the terminal/recursive FM margins.

(d) For every x with N lambda_x>=N^xi, conditional probability at least 1-exp(-N^c) that |I_x|-N lambda_x and all induced tail column counts minus |I_x|p_j(l) are bounded by a fixed sublinear power such as C(N lambda_x)^(4/5).

The source's 'conditional preservation' is not a replacement for (a)-(c). Large-block conditional concentration follows from unconditional concentration plus conditional Markov after truncating histories. It does not say all conditioned counts are hypergeometric with their original parameters; conditioning a sorted history also imposes lexicographic and duplicate-count constraints.

Given these estimates, AM-GM and conditional replicas reduce unrevealed shared edges to the repeated-current-string term plus a sum of self-intersections in aligned future blocks. For very small lambda use (a). Near N^-1 use (c), with remaining collision cost bounded below by the terminal margin (not by a homogeneous constant times remaining time). For large blocks, condition additionally on its vertex interval and all induced tail column counts; prove the conditional law inside is the uniform fixed-count matrix law, and apply a **verified robust first-moment theorem** at the actual absolute birth time and actual size exponent. Sum over the number of blocks, keeping the finite polynomial exponent loss.

The manuscript says 'N^{o(1)} blocks' and the 2025 proof says O(log N) after a refinement. A refinement through O(rho log N) columns actually gives N^{O(rho)} blocks. One must subtract O(rho) from the final decay exponent; it is not o(1) for fixed rho.

## 6. Alternative reconstruction of the difficult conditional argument

This is a proposed proof route with identified obligations, not a completed proof.

### A. Obtain constant-length reserves using local density

In any interval of n approximately rho log N columns containing at least gamma n good columns, partition into windows of length D=ceil(6/gamma). If every window had at most two good columns, the total would be at most 2ceil(n/D)<gamma n for large N. Therefore one window contains three good columns. Start at the first of those three: the other two are within D columns, while the deleted initial segment has at most rho log N+O(1) columns.

Keep absolute times instead of invoking stationarity. If r_0 is the deletion time, the restarted whole-deck mass exponent at s is beta(s)+A(0,r_0). Every N_1 expression therefore increases by at most (7/2)A(0,r_0), N_2 by at most (3/2)A(0,r_0), and the other expressions by at most A(0,r_0). Since a_p<=log k, the maximum loss is <=(7/2)rho log k+o(1). Absorb it into a fixed fraction of eta by an explicit pre-frozen parameter choice. This derives the shifted FM inequalities; it does not assume a stationary profile or unchanged margins.

### B. Use exact finite reservoir counting and normalize the first pile

Condition on the sorted history in the first-digit p part, keep the currently revealed repeated word in the unsorted residual block, and fix all but m of that block's rows, with m=1 or 2. The complement of the first-digit part is a reservoir of size c=N-n_p>=gN because column 1 is g-good. Candidate m-row masses are products of exact falling-factorial ratios for the residual column counts. The normalizing denominator is a sum over candidates satisfying the lexicographic cutoff and required current-word multiplicity.

Use conditional cylinder weight q_x=lambda_x/p_p, not lambda_x, because these rows are already known to start with p. Even if p_p is very small,

n_rem^m q_x^{m(1-alpha)} <= (N p_p)^m (lambda_x/p_p)^{m(1-alpha)} <= N^m lambda_x^{m(1-alpha)}.

Hence no positive constant lower bound on every p_p is needed. For p_p=0 there is no part to explore. To bound extra current-string repetitions, condition only on configurations in which the other residual rows already supply the required copies of s_i; otherwise the 'remaining' copy may be forced. This produces estimate (b) for extra copies rather than wrongly bounding all copies including the observed ones.

### C. Separate the good-column threshold from rare-coordinate cutoff

Retain the given nondegeneracy threshold g>0. Choose a separate analytic cutoff tau>0 much smaller than g. On a reservoir concentration event, for coordinates p_j(l)>=tau the residual ratios differ from p_j(l) by a multiplicative 1+o(1). For p_j(l)<tau, use the deterministic bound ratio<=p_j(l)/g. If a word has r rare positions, lambda_tail<=tau^r, so g^-r<=lambda_tail^-alpha for alpha=log(1/g)/log(1/tau). Alpha can be made arbitrarily small by choosing tau small at fixed g. This avoids a false o_chi(1) loss when the same chi controls both a reservoir of size merely chi N and the rare threshold.

A right reserve cylinder uses only the D early cutoff digits, each with probability >=g, and restricts later digits to probability >=tau. Its mass is at least a fixed constant times (1-k tau)^K, hence N^-O(tau). The exact denominator comparison then yields the required m-row bounds with lambda_x^(m(1-alpha)) and N^O(m tau) losses. The m=1 cases give (a),(b); m=2 and summation over full completions give (c). This requires a complete counting proof and uniform control of exceptional history probabilities.

### D. Conditional concentration and same-cell obstruction

Let H be the event that all large-prefix sizes and induced tail counts concentrate; there are only sum_{j<=K}k^j=N^O(1) prefixes. Prove P(H^c)<=exp(-N^c) from the fixed-column concentration lemmas. Define F_i^H={P(H|a_i)>=1-exp(-N^{c/2})}. Conditional Markov gives P((F_i^H)^c)<=exp(-N^{c/2}). On F_i^H the random block selected by a_i obeys the desired concentration with high conditional probability.

But induced normalized counts q_j need not lie in the same finite partition cell as p_j, even when their distance tends to zero: p_j may lie on a cell boundary. Thus the exact almost-profile hypothesis in the displayed first-moment proposition is not automatically inherited. The 2025 paper explicitly uses a weak-1/6 almost-like first-moment interface. This is a genuine unresolved interface obligation in the current TeX.

Cost-level robustness gives, for ||q-p||_infinity<=epsilon,

|a_q-a_p|<=C_k epsilon,
sup_{theta in [2,4]}|psi_q(theta)-psi_p(theta)|<=C_k epsilon,

and on p_l>=tau with epsilon<=tau/2,

|log q_l-log p_l|<=2epsilon/tau.

Consequently induced counts within C(N lambda_x)^(-1/5) preserve all integrated collision/maximal-pile costs with o(1) exponent errors and preserve regular-coordinate digit cost estimates. This suggests proving a robust FM corollary from the completed first-moment proof using the original column-to-representative assignment, without requiring q to retain literal cell membership. It is **not** a formal consequence of an exact-cell FM proposition treated as an opaque theorem. Such a corollary must itself be proved, or a two-level boundary-null/guard-band partition construction must be selected and proved before freeze. It cannot be added as a hypothesis.

## 7. Completing sparsity and TV once the obligations are proved

The terminal maximal-string margin gives max_s lambda_s<=N^-1-eta' after error budgets. Estimate (b) then bounds conditional directional next-edge success by q_N<=N^-delta on good histories. For any a selected increasing edge locations in an L-vertex interval, adapted sequential conditioning gives joint probability <=q_N^a up to the separately charged global bad-history event. A union bound gives at most binom(L,a)q_N^a. Choose a around L/(constant*k) or handle the deterministic first-digit intervals carefully; do not assert an L interval meets at most two first-digit parts when arbitrarily small piles are allowed. Taking L sufficiently large yields O(N^-2) per interval and O(N^-1) globally. Small initial parts may instead be made edge-free on the typical event using their total pair-collision expectation and the terminal margin.

Let A be a single-matrix typical set with P(A^c)<=epsilon, L-sparsity, and all needed regularity/exploration good events. Let d=2k, X=number of shared edges, X_j=number in direction j. On A x A, X<=sum_j X_j. If the killed-exploration theorem supplies

E[(exp(d log(L!)*X_j)-1)1_{A x A}]<=b_j,

then pointwise convexity gives

((L!)^X-1)1_{A x A} <= (1/d) sum_j (exp(d log(L!)*X_j)-1)1_{A x A}.

Therefore the exact finite upper bound is

TV(P,uniform) <= (1/2)sqrt((1/d)sum_j b_j)+epsilon.

This formulation proves the needed exponential **excess** directly and avoids silently replacing a truncated expectation by a normalized conditional law. If b_j=O(N^-delta) and epsilon=O(N^-1), TV tends to zero.

## 8. Freeze assessment

The finite graph, density, truncation, factorial, subset-comparison, lexical decomposition, killed-exploration, convexity, and TV-assembly statements have complete reconstructible proofs and require no new time-profile assumptions.

The overall freeze cannot yet pass. 'Accessible', 'regular', the conditional sigma-fields, precise directional sets, finite-N error hierarchy, and the robust completed-first-moment interface must be fixed. The conditional reservoir/row-count estimates, small-block cases, high-probability directional regularity for small first piles, and sparsity are genuine proof obligations. The first-moment proposition alone does not establish them. No exponential-moment completion claim is justified until these are proved in Lean from the original cut/profile assumptions.
