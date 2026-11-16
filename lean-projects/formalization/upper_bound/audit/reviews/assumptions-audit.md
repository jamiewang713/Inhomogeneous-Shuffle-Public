# Independent assumptions audit (pre-freeze)

Sources read: `time_inhomogeneous_riffle_shuffle_unified_article.tex`, `2103.05068v3.pdf`, and `2510.22783v1.pdf` only. No Lean or project source was inspected or changed. This report separates proved finite arguments from proposed repairs requiring further proof. No theorem or assumptions have been frozen.

## Decision

The graph/Radon–Nikodym/truncation/combinatorial-sparsity pipeline is valid for finite path graphs without homogeneity. The inhomogeneous exponential-moment pipeline is not ready to freeze: the stated conditional-preservation lemma is false for exact fixed-partition profile-likeness, several homogeneous conditional arguments contain errors, and a precise robust first-moment interface is required. A first moment alone cannot complete this pipeline.

## Per-family dependency and assumptions ledger

### 1. Shuffle graph representation

Input: integers N, K, k; nonnegative integer column counts summing to N; uniform distribution on all matrices with these column counts (equivalently independent uniform multiset columns); lexicographically sorted rows; an independent uniform permutation. Output: law of the inverse shuffle equals law obtained by sorting this independent permutation increasingly on each equal-row block. Sources: TEX graph-representation lemma; 2510 Proposition 2.2, p.8; 2103 corresponding representation preceding Section 3.

No time-profile or regularity assumption is needed. Independence of the uniform permutation from the graph must appear explicitly. Freeze the permutation convention and column/time convention: stable sorting by a new most-significant key reverses key significance, while the paper's row refinement appends a least-significant column and has a different interpretation of inverse composition. Prove the induction in the chosen convention; do not commute time-dependent columns. Zero-size piles and N=0/1 need explicit conventions or a fixed N>=2 domain.

### 2. Radon–Nikodym reduction

For a fixed path subgraph G, the density is f_G(sigma)=1_{sigma is increasing on G-components} times the product of component-size factorials. Every increasing output has exactly that product of preimages. Thus E_sigma f_G=1 and the mixture density is E_G f_G.

For U=G union G', exact second moment:

    f(G,G') = [prod_{C in comp G}|C|!][prod_{C' in comp G'}|C'|!] / prod_{D in comp U}|D|!.

This follows because simultaneous increasingness is increasingness on U. These are finite counting results independent of the shuffle law. It is false that f(G,G')>=1 pointwise: adjacent nonoverlapping edge constraints can give f<1. The nonnegativity needed later is an averaged square.

### 3. Truncated chi-square

Let A be a measurable event of ONE matrix, use independent S,S' with the same law, and truncate on A(S) and A(S'). The exact squared term is

    E_sigma [E_S ((f_G(sigma)-1)1_A(S))]^2
      = E_{S,S'}[(f(G,G')-1)1_A(S)1_A(S')].

It is nonnegative. Cauchy–Schwarz and E_sigma f_G=1 yield the TEX bound with bad-event cost P(A^c). This is valid. An arbitrary pair-event cannot replace the product event. The TEX phrase defining S_1 as 'both matrices regular and both graphs sparse' is a typing error: freeze S_1 as a one-matrix set, then use S,S' in S_1.

### 4. Sparse factorial bound and high-probability sparsity

Deterministic bound: L is an integer >=10; every L-vertex interval contains at most L/3 edges in each graph. Every U-component has at most L vertices, because otherwise an L-window would contain L-1>2L/3 edges. Components with no shared edge contribute at most 1, and each component with a shared edge contributes at most |D|!; there are at most |E(G) intersection E(G')| such components. Hence f<= (L!)^shared.

High-probability sparsity is a DIFFERENT lemma. It needs a uniform conditional single-edge/repetition bound on adapted good histories. Its proof is not supplied by the completed shared-edge first moment. Source 2510 p.42 says a fixed L-window meets at most two initial-pile intervals; that is false when many initial piles are short (e.g. k>=3, several unit-sized piles). Repair without assumptions: work globally with the 2k directional classifications, use a per-direction threshold L/(constant*k), and a union bound; or exclude collisions in tiny initial piles first and prove remaining large intervals exceed L.

### 5. Forward/backward covering

Freeze deterministic first-pile intervals, a selected early triple of good columns, right/left guard strings, and directional edge membership. 'There are 2k directions covering all edges' cannot be an undefined primitive. The covering argument needs both matrices to satisfy individual endpoint-count regularity and a positive deterministic overlap gap. This prevents the two copies choosing opposite directions at the same shared location.

Backward means reverse the VERTEX exploration / alphabet order, not reverse chronological columns. No stationarity or time reversal of mu_t is permissible.

A local density of gamma*rho*log N good columns gives a three-good-column cluster of bounded span O(1/gamma) by pigeonhole, somewhere within an initial O(rho log N) window. Deleting the initial segment is valid by TV contraction, but the profile must retain absolute time and margin errors O(rho); the new root has exponent 1, not automatically 1-A(0,r). Slack must absorb that discrepancy before freeze. Never silently assume the first column is already good.

### 6. Exploration and conditional representation

Natural history at location i reveals both strings up to i within a deterministic first-pile interval. Given a history, remaining columns are NOT independent ordinary hypergeometric samples: every remaining row is lexicographically at least the current string, and a number of copies of that string may be forced. Source 2510 Lemmas 5.7,5.9–5.11 provide a finite constrained-matrix counting representation; its exact counterpart is required.

Partition the strict-future lexicographic interval into prefix cylinders. The initial antichain has <=2kK blocks. Extending blocks to a future good column creates O(log N) N^{C rho} blocks, NOT N^{o(1)} when rho is fixed. The source says both N^{O(rho)} and later O(log N); the latter is wrong after refinement. Choose C*rho strictly below the conditional first-moment exponent. The source's grid argument also gives extension up to 2*rho*log N, rather than rho*log N as claimed in one line. Neither is fatal if frozen with the correct constants.

### 7. Unrevealed shared-edge estimates

The two histories differ. AM–GM gives an AVERAGE of two conditional self-intersections. More conditioning increases self-intersections only after conditional averaging; it is not a pointwise bound by a realized fine-history value. Source 2510 p.38 (5.10) does not follow 'by symmetry' pointwise. Bound each history uniformly and retain the average.

The decomposition must include repeated copies of the currently exposed string separately. Subsequent blocks require THREE regimes: N*lambda <<1, N*lambda around 1, and N*lambda >>1. Total size suffices only in the first regime. The middle regime requires a single-graph pair/collision estimate using remaining tail B_2. Large blocks need conditional fixed-count shuffle law, uniform cost/profile control, and the robust completed first-moment theorem. Recursive numerical margins do not themselves give any of those conditional distribution facts.

### 8. Exponential moment

A uniform small conditional expectation of all FUTURE directional edges on ADAPTED good histories is sufficient. A global first moment or a terminal regularity event by itself is insufficient. Source 2510 Lemma 5.4 has an invalid tower-property step after enlarging the filtration by the final event. Its statement admits the killed-process proof below.

For total shared count, use pointwise cover and convexity:

    exp(c*shared)-1 <= (1/(2k)) sum_direction [exp(2k*c*direction_count)-1].

To derive a bound on E[(exp(t*count)-1)1_A] from E[exp(t*count)1_A]<=1+epsilon, also use P(A^c) small; the difference costs at most epsilon+P(A^c). Avoid silently subtracting 1 instead of P(A).

### 9. TV upper bound and random piles

With one-matrix A of probability >=1-r_N and shared truncated exponential excess <=epsilon_N, the exact conclusion is TV<=sqrt(epsilon_N)/2+r_N. All constants and the large-N threshold must be uniform in admissible deterministic cuts.

For random piles, condition on the ENTIRE cut sequence, whose mixture construction includes an independent conditional shuffle. Convexity gives TV(mixture,uniform)<= E TV(conditional law,uniform). Thus high-probability admissibility plus the uniform deterministic result suffices, without independence of the random cuts across time. Averaging small pointwise bounds without uniformity is not the stated deterministic-to-random proof.

## Concrete counterexamples / failed substitutions

1. **Exact-cell conditional preservation is false.** Take k=2, every original column proportion (1/2,1/2), profile a point mass there, and a chi-regular partition with boundary p_0=1/2, assigning the point to the upper-side cell. Original cell counts are exact. In the first-prefix block of N/2 rows, each future column's normalized first-pile count is a hypergeometric variable centered at 1/2. Conditional on that prefix block, columns are independent and about half land in the lower-side cell. The conditional cut sequence violates almost-like cell counts for phi<1/4 with probability tending to 1. Arbitrarily small coordinate perturbations do not preserve Borel cell membership. A robust cost-based first-moment corollary must be proved from the original hypotheses; it cannot be added as an assumption.

2. **Tiny first piles break source switching statements as written.** A chi-good first column only guarantees two large piles. For k=3 take its p-pile size 2, other sizes near N/2, and all subsequent columns fair on the other two symbols. A future guard-eligible prefix x starting in the size-2 pile has global lambda_x=O(1/N), but, conditional on starting with p and a suitable previously revealed smaller row, its continuation probability is bounded below by a constant. Source Lemma 5.8's bound C lambda_x^{1-o_chi(1)} N^{O(chi)} therefore fails for sufficiently small chi. Its proof p.49 incorrectly asserts (1,p) is a large coordinate and lambda_guard>=chi^3(...); p.41 incorrectly asserts lambda_left^p>=chi^A independently of p.

3. **The source reciprocal estimate is wrong.** From n_p/N<=1-chi one obtains 1/(1-n_p/N)<=1/chi. Source (5.37) uses 1/(1-2chi), which does not follow, e.g. n_p/N=1/2 and chi=0.01.

4. **First moment plus sparsity cannot imply MGF.** Let H_N be a deterministic path graph with an edge every four vertices, and let G=H_N with probability N^{-q}, otherwise empty; G' is independent. Both are L-sparse for a fixed suitable L. For q>1/2, E|G intersection G'|=O(N^{1-2q}) tends to zero, but E exp(t|G intersection G'|)>=N^{-2q} exp(c t N) diverges. This is an abstract obstruction to using first moment alone, not a claim this graph law is a shuffle law.

## Valid replacements reconstructed independently

### Killed adapted exploration proof of truncated MGF

Let block vertices be a,...,b, with natural history H_i, and C_i the cumulative directional shared-edge count revealed at i. Then C_a=0, C_i-C_{i-1} is 0 or 1. For a<=i<=b-2 let A_i belong to H_i and assume E[C_b-C_i|H_i]<=gamma on A_i. The terminal endpoint event ensures C_b=C_{b-2} on the final event F, which is contained in every A_i.

For a+1<=i<=b-2 define Y_i=(C_i-C_{i-1})1_{intersection_{h=a}^i A_h}; let Y=sum Y_i. This process is adapted and stops counting permanently after the first failed A_i. On F, Y=C_b. At time i, future Y increments are zero unless the history is still alive; while alive their conditional mean is at most E[C_b-C_i|H_i]<=gamma. The initial-time bound gives P(Y>=1)<=E Y<=gamma.

At the stopping time T_r of the r-th Y-success, finite tower/summation yields P(Y>=r+1)<=gamma P(Y>=r). Hence P(Y>=r)<=gamma^r, including the base r=1. For t>0 and exp(t)*gamma<1,

    E[exp(t*C_b)1_F] <= E exp(tY)
      <= 1+(exp(t)-1)*gamma/(1-exp(t)*gamma)
      = (1-gamma)/(1-exp(t)*gamma).

For exp(t)*gamma<=1/2 this is <=1+2 exp(t)*gamma. No enlarged filtration and no conditioning on final F are used. Blocks with <=3 vertices have no directional edge on the specified endpoint event and can be handled directly.

### Small-first-pile normalization and exclusion

For an active first pile let p=n_p/N and q_x=lambda_x/p. Exact row counting must use q_x. For m fixed,

    n_p^m q_x^{m(1-e)}
      =N^m lambda_x^{m(1-e)} p^{m e}
      <=N^m lambda_x^{m(1-e)}.

Thus summing over at most n_p rows, rather than N before normalization, repairs the loss. Piles p=0 are empty and omitted.

For n_p<=N^xi, a direct pair count gives

    E edges in p-block <=n_p^2 exp(-sum_{j>=2} psi_j(2)).

Since psi_j(2)>=a_j, a_1<=log k, and the terminal margin gives A(0,T)>=1+eta, this is at most C N^{2xi-1-eta+small error}. Choose 2xi<eta/2 and discard any collision in these tiny piles at cost o(N^{-1}). Remaining n_p>=N^xi allow relative endpoint concentration, provided the bounded-length guard construction has been proved. These are derived cases, not added model hypotheses.

### Proposed alternative switching regularity (not yet fully implemented/proved)

An N-dependent threshold may avoid the source's wrong reciprocal bound. Call (j,l) large when p_l^(j)>=N^{-1/8}. With a chi-good first column, the outside-reservoir fraction is >=chi. Require all outside digit counts within N^{2/3} of their means; Hoeffding plus O(log N) union bounds gives exponential failure, and Markov produces typical natural histories. Fixed-m resampling changes counts by at most m.

On large coordinates the conditional row weights are (1+O(N^{-5/24}/chi))*p_l. On rare coordinates they are <=(2/chi)*p_l. If x has d rare coordinates then q_x<=N^{-d/8}, so (2/chi)^d<=q_x^{-8 log(2/chi)/log N}. Numerators therefore have q_x^{m(1-e_N)} bounds with e_N tending to zero. For the denominator, use the bounded-length guard prefix and then only large coordinates; their retained mass is at least chi^A(1-k N^{-1/8})^K>=chi^A/2. Forced copies of the current string still require the exact constrained-matrix case split. This is a promising proof plan, not a checked theorem.

## Whole-proof context

Upper branch: common fixed-column model -> graph/RN/truncation; numerical margins and profile/hypergeometric estimates -> completed first moment; conditional counting + robust first moment + adapted exploration -> directional MGF; endpoint covering + sparsity -> shared MGF -> TV -> randomized extension.

Lower branch (active detailed TEX section): largest-prefix test follows from successive thinning and a long increasing component. If that obstruction is small and Lambda_1 is positive, entropy inequalities and bridge-window lemma produce a cold witness. Type estimates and relative endpoint concentration yield cold geometry and localization; fixed-column factorial moments and occupancy approximation yield many cold edges; component-value bounded differences and the translate-scan ascent test yield TV tending to 1. The detailed branch depends on graph representation and profile/hypergeometric results, not the upper exponential moment. Random lower mixtures need a uniform test or a many-to-one union bound; convexity alone cannot transfer TV tending to 1.

The old lower-bound blueprint is inside a commented TEX block, and should not replace the later detailed lower proof. Its random-test count is exp(O((log N)^2)), dominated by a uniform exp(-N^c) false-positive bound when proved.

## Freeze prerequisites still unresolved

Obtain the exact completed first-moment theorem statement, including ambient conditioning, alignment, large-block size range, perturbation tolerance, constants, and uniformity. Prove the robust interface from the existing assumptions (the literal exact-cell preservation route fails). Finish the conditional constrained-matrix counting estimates, guard selection and small-pile handling, refined-block exponent accounting, adapted regularity, and single-edge bounds. Only then freeze all assumptions and statements for the requested upper pipeline. No exponential-moment completion claim is justified yet.
