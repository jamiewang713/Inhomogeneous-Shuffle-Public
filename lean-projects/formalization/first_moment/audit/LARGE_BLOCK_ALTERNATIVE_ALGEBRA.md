# Large-block alternatives: algebra and the remaining stochastic statement

This is a bounded mathematical audit, not a new frozen contract or a Lean implementation. No existing definition, assumption, or theorem has been changed. The mathematical sources are the authorized unified TeX, 2103.05068v3, and 2510.22783v1. The existing small-block repair and the proved finite endpoint/collision declarations were also inspected.

## Outcome

1. Exact two-row collision counting alone does not give enough decay for every large profile class under the stated variational margins.
2. The manuscript's **large-block density estimate itself is false**, including for cut sequences satisfying its good-column and first-moment assumptions. An explicit example is given below. This is a counterexample to the intermediate estimate, not to `prop:ub-first-moment`.
3. There is a concrete reduction of the final theorem to a reservoir version of the stochastic estimates. Expose through one early good column, keep the full population when revealing future columns, and decompose the resulting fixed row subsets. This uses the original model assumptions and the original time-inhomogeneous N1/N3 margins. It requires a new proved stochastic input and a different proof-local decomposition; it does not prove the false original estimate.

## 1. What the exact collision estimates do and do not imply

For a fixed prefix x write lambda=E Y_x=N^(L+o(1)) and let q_tail be the exact two-row tail collision factor. Fixed-column sampling gives

    E[internal edges in x] <= (lambda^2/2) q_tail,
    q_tail <= N^E,
    sum_m p_x(m)^2 <= (E[internal edges in x])^2.

Consequently the unconditional bound is

    sum_m p_x(m)^2 <= (1/4) N^(4L+2E+o(1)).

The other elementary bound is `sum p_x^2 <= E[internal edges]`, giving exponent `2L+E`. For a class with entropy exponent H the two resulting exponents are `4L+2E+H` and `2L+E+H`. Neither is controlled by N1 in general.

For example, take the uniform k-pile profile and put t=T log k. Choose t=8/5. Then

    beta(s)=1-s log k,
    B_theta(s,u)=(theta-1)(u-s) log k,
    B_2(u,T)=(T-u) log k.

Evaluation at theta=3 gives N1 <= 3-2t-s log k <= -1/5. N2, N3, and the terminal margin are also strictly negative. For the typical first-crossing profile in the middle first-column pile, the limiting parameters are

    V=1, F=1/2, L=1/2, S=H=1/2, E=-t+1/2.

The source's desired exponent is `4L-F+2E+H=3-2t=-1/5`, whereas exact-collision squaring gives `7/2-2t=3/10`, and the first-power bound gives `2-t=2/5`. Thus even the minimum of the two available collision bounds is insufficient. Exact without-replacement corrections over O(log N) balanced columns are only `N^o(1)` and cannot supply the missing fixed power.

This is a failure of that proof route, not a lower bound on the actual common-edge expectation.

The already compiled declarations expressing the valid finite bounds include

- `EdgeLocalization.matrix_expected_internal_edges_le_half_mean_bound`;
- `EdgeLocalization.matrix_internal_density_le_mean_tail_fourth`;
- `EdgeLocalization.internal_density_le_expected_edges`.

## 2. Counterexample to the large-block density estimate

Let q tend to infinity through positive integers and set

    N=12 q^4, T=2, K=floor(2 log N), t=K-2.

Use independent fixed-count columns with counts

    column 1: (N/4, N/2, N/4),
    column 2: (2q, (N-2q)/2, (N-2q)/2),
    columns 3,...,K: (N/3, N/3, N/3).

All entries are integral and sum to N. For any sufficiently small fixed chi<1/4, every column is chi-good. The constant uniform-third macroscopic profile is almost-like: the first two columns change any empirical cell count by at most 2/log N, which is absorbed by the positive fixed grid tolerance for large N.

Writing l=log 3, evaluation at theta=3 gives, for 0<=s<=u<=2,

    N1(0,s,u;1) <= 3-4l-sl < -1,
    N2(0,s,u;1) <= 1-4l+sl <= 1-2l < -1,
    N3(0,s;1)=1-2l < -1,
    beta(2)=1-2l < -1.

In particular the source's FM condition holds with eta=1/2.

Take w empty, y=z=v=(1), and x=(1,0). The boundary pair is admissible, compatible, retained and nonterminal. Its first-column side pieces have deterministic size N/4. The exact source exponents are

    F=(1/2) log_N(N/4)=1/2-log_N 2,
    V=log_N(N/2)=1-log_N 2,
    L=log_N q=1/4-(log_N 12)/4,
    E=-t log 3/log N.

For all sufficiently small fixed delta>0, eventually `V-F=1/2>=delta`, `L-F<delta`, and `L>=2delta`. Hence x belongs to the printed large first-crossing stable case, is not a terminal fallback, and has the required fluctuation comparison. Its sole extension digit is exceptional, but its exceptional fraction is only 1/log N and survives the stated truncation.

The left endpoint of x is deterministically N/4. Its occupancy is at most 2q because column 2 contains exactly 2q zeros. Thus all possible internal edges are supported in at most 2q fixed locations.

Let C2 be the number of unordered pairs of equal full rows extending x, and C3 the number of unordered triples of equal full rows extending x. Direct fixed-column sampling gives

    E C2 = [(N/2)_2/(N)_2] * [(2q)_2/2]
            * [ (1/3)(1-2/(N-1)) ]^t.

For all sufficiently large N, the first bracket is at least 1/5, the second factor is at least q^2, and `(1-2/(N-1))^t>=1/2`. Therefore

    E C2 >= (q^2/10) 3^(-t).

For triples, condition on the 2q zero labels in column 2. A triple lies in the middle first pile with probability at most 1/8, and one balanced tail column has triple-collision probability at most 1/9. Hence

    E C3 <= binom(2q,3) (1/8) 3^(-2t)
          <= (q^3/6) 3^(-2t).

For every integer occupancy h>=0,

    (h-1)_+ >= binom(h,2)-binom(h,3).

Applying this inside each full-string component gives `E edges >= E C2-E C3`. Since `q 3^(-t)->0`, eventually

    E[internal edges in x] >= (q^2/20) 3^(-t).

Cauchy--Schwarz on the at most 2q possible edge locations now yields

    sum_m p_x(m)^2 >= (q^3/800) 3^(-2t).

The claimed large-block bound at TeX lines 1491--1495 instead gives

    sum_m p_x(m)^2 <= 2 q^4 N^(-1/2+C delta+o(1)) 3^(-2t).

After division by q^3 3^(-2t), this would require

    1/800 <= 2*12^(-1/4) N^(-1/4+C delta+o(1)),

which is impossible after choosing delta small and then N large. This uses the same nested interpretation of O(delta) required in the source's final assembly.

The example still has a rapidly decaying contribution: its lower exponent is `3/4-4 log 3+o(1)<0`, and the valid two-row upper exponent is `1-4 log 3+o(1)<0`. It therefore does **not** contradict the final first-moment proposition. It proves that no algebraic rearrangement can establish the original large-density statement with its definitions unchanged.

## 3. A proof-local reservoir reduction

The relevant distinction in 2510.22783v1 is explicit. Definition 4.3 starts genuine crossings after column 1; its fluctuation maxima start at column 2. In Lemma 4.5 the first good column gives `N'<= (1-chi)N`, which supplies a population outside all reveal sets. The uniform first-column endpoint is excluded from the fluctuation scale. The discussion following Definition 4.7 explicitly identifies strings `j00...0` and `j(k-1)(k-1)...` as exceptional rigid locations. The multinomial proof in 2103.05068v3, Section 4.2, uses a conditionally random external shift and cannot be transplanted to a fixed first-column endpoint.

Here is a reduction respecting the original model hypotheses, while using a different proof-local partition.

### 3.1 Expose through an early good column

Choose the first chi-good column j0 after the ambient birth Mw. Provided the remaining macroscopic interval has length at least rho, the stated local-good hypothesis places such a column within `rho log N+O(1)` steps. Expose all columns through j0; call this finite information H0.

For each legal extension a of w of length j0, its row-label set R_a, cardinality M_a, and its lexicographic location relative to the ambient block are H0-measurable. Moreover, exactly and without a concentration argument,

    M_a <= n^(j0)_{a[j0]} <= (1-chi)N.

The second inequality holds for every digit because column j0 has two piles of size at least chi N. There are at most

    k^(j0-Mw) <= N^(rho log k+o(1))

such anchors. Future columns remain independent uniform permutations with their original **global** fixed counts. One must not replace their population N by M_a or condition on all future counts inside R_a.

A vacuous short tail is harmless: when `T-r<rho`, the boundedness `B2(r,T)<=rho log k`, together with N1 at s=u=r and rho sufficiently small compared with eta, forces b to be a negative constant. The elementary bound by expected ambient occupancy then already gives polynomial decay.

### 3.2 Conditional squaring removes random anchor translations

For the original edge-probability vector p and its conditional version p_H0,

    sum_m p(m)^2 <= E_H0 [sum_m p_H0(m)^2].

This is ordinary conditional Jensen/Cauchy--Schwarz. Given H0, distinct anchor intervals are fixed and disjoint, and no equal-full-row edge crosses between them. Therefore their conditional density contributions add exactly. In particular, sharing the early history in the upper bound is justified by convexity; it is not an assertion that the original independent copies have a shared history.

Anchors with very small deterministic mean can be removed directly using the collision bound and N3. If their mean exponent is at most zeta, then

    2 cL(a)+cE(a) <= zeta-eta+e,

using `cL(a)<=beta(t_a)+e` and `cE(a)<=-B2(t_a,T)+e`. Summing over the above number of anchors is harmless for small zeta and rho. For the other anchors, the source's prefix concentration estimates give, outside a uniformly exponentially small event,

    M_a <= N^(e) E M_a.

Only this upper comparison is needed to transfer the numerical margins. The exceptional event contributes at most N times its probability.

### 3.3 Numerical conditions for the refined decomposition

Inside a fixed R_a, begin the auxiliary boundary construction **after** j0 and define its side-piece scale using only those later columns. These are auxiliary data; the original manuscript definitions and existing frozen interfaces are not redefined.

Use conditional size exponent

    L_a(v)=log_N M_a - sum_{j0<j<=|v|} log_N(1/p^(j)_{v[j]}).

On the preceding upper-comparison event, `L_a(v)<=cL_original(v)+e`, hence for every new boundary join v at time s,

    V=L_a(v)<=beta_original(s)+e.

No new homogeneous cutoff constant and no stronger variational condition appears. The same entropy and tail inequalities are available for the original time profile. Genuine new crossings give `F>=V/2-e`; the auxiliary stopping rule gives `L-F<=delta`; splitting the digit cost gives `L+S+Q<=V+e` with Q>=0. Thus the already reconstructed numerical identity remains

    4L-F+theta S
      = theta(L+S+Q)+(4-theta)(L-F)+(3-theta)F-theta Q
      <= ((theta+3)/2) beta_original(s)+O(e+delta).

Consequently N1 supplies the same negative large-class exponent. Small nonsingletons can use the previously audited collision repair; small and terminal singletons use N3 and the terminal margin. All prefix/cell/exceptional counting losses remain controllable, with the additional anchor-count loss `rho log k`.

### 3.4 Why the reservoir fixes the finite-population degeneracy

The required stochastic calculation is now in a fixed subset R of [N] of size M<=(1-chi)N, while every future column is sampled in the original N-point population. The manuscript's reveal sets R1,R2 and their complementary sampled sets all lie in R. Therefore

    a2+|R1|<=M<=(1-chi)N,
    b2+|R2|<=M<=(1-chi)N.

These deterministic inequalities supply the population-complement factor missing from the original first-column argument. In the equal-column case the mean selected fraction is at most M/N<=1-chi; concentration gives the corresponding strict upper bound for the realized selected fraction.

The other complementary fraction is controlled by the side-piece decomposition. If the left maximum is the smaller and Qmax is the right maximum, then for a nonterminal boundary join

    M <= (2K+chi^(-1)) Qmax.

This follows by partitioning R into left pieces, right pieces, and the join cylinder; the latter is at most chi^(-1) times a crossing side piece. Consequently the relevant global digit-side probability is at least

    Qmax/M >= 1/(2K+chi^(-1)).

Using Qmax/M, rather than Qmax/N, is essential when the anchor is small. This is a direct finite-population inequality, independent of time homogeneity.

These observations identify the valid non-exhaustion mechanism in all three reveal cases. They do not by themselves constitute a completed conditional-probability or concentration proof.

### 3.5 The density proof needs no endpoint-window theorem

If the reservoir version of conditional endpoint anti-concentration is proved on a good event S, it gives

    sup_m P(edge m in x, S) <= A E[internal edges in x],
    A=N^(-F+O(delta)+o(1)).

Together with `sum_m P(edge m in x,S)<=E[internal edges in x]`, this immediately yields

    sum_m P(edge m in x,S)^2
      <= A (E[internal edges in x])^2
      <= (1/4) N^(4L-F+2E+O(delta)+o(1)).

The bad-event contribution is bounded separately by N P(S^c)^2, up to the elementary factor 2. Thus the endpoint-window estimate can be omitted from the **density** proof. It remains useful for per-edge localization of different auxiliary stable blocks.

For localization the stopping parent has expected size at least `N^(F+delta)`. A window of scale `N^(F+delta/2)` is strictly smaller. At each fixed depth, ordered disjoint parent intervals of that minimum expected width leave at most two candidates for a fixed location; multiplying by k children and K depths gives `2Kk`. A proof must choose the negligibility threshold consistently with the concentration exponent. The manuscript's printed comparison between `exp(-N^delta)` and `exp(-N^(delta-o(1)))` does not itself give the claimed contradiction.

## 4. Precise remaining result

The following is a description of the missing result, **not** an exported or assumed theorem:

> Uniformly for a fixed row subset R of cardinality M<=(1-chi)N, with future columns sampled independently using their original global fixed counts, prove the conditional endpoint atom and prefix concentration/localization bounds for the auxiliary boundary/stable partition rooted at R. Its fluctuation scale must exclude all already exposed columns. The proof must retain the outside-R population in every hypergeometric reveal. Combine those bounds with the original profile estimates, N1/N3/terminal margins, and refined class counts to bound the conditional squared edge-probability sum by N^(-c), uniformly over the good early histories.

Once this result and its model-to-profile links are proved, Sections 3.1--3.3 give an explicit conditional-Jensen reduction to `prop:ub-first-moment`, with an anchor-count loss at most `rho log k+o(1)` and exponentially small exceptional-history error. Choosing rho below the remaining margin absorbs this loss.

The current audit establishes the algebraic reduction and identifies a valid source-derived reservoir. It does not complete the stochastic input, does not establish a counterexample to the final theorem, and does not justify marking the final first-moment target complete.
