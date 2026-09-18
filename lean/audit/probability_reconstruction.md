# Independent probability reconstruction

This report is an independent mathematical review, not a frozen specification and not Lean code. Only `time_inhomogeneous_riffle_shuffle_unified_article.tex`, `2103.05068v3.pdf`, and `2510.22783v1.pdf` were read as mathematical sources. The report reviews every candidate lemma listed below. No source theorem is treated as an axiom.

## Decision before freezing

The finite hypergeometric core proposed by the coordinating agent is mathematically sound, including empty populations, singleton populations, all factorial-moment orders, and positive-atom conditioning. The source's ambient-conditioning/non-exhaustion conclusion is false as stated. It must not be frozen as a theorem to prove. The endpoint anti-concentration lemma also has a concrete counterexample under its present stated scope.

The crucial difference from the homogeneous paper is an omitted anchor: `2510.22783v1.pdf`, Definition 4.3 and Lemmas 4.4–4.6, excludes the first column from the fluctuation maxima and assumes the first column is chi-good. Its proof retains the full population of size N and uses the strictly smaller first-column pile N' <= (1-chi)N. The TeX changed the maxima to start immediately after the ambient prefix and then replaced the population by the ambient size, erasing the complement used in the homogeneous proof.

## 1. Exact basic model and edge cases

Use one named parameter order throughout: population N, marked count K, draw count m, with N,K,m natural and K <= N, m <= N. The TeX upper-bound section uses Hyp(marked,population,draw), while its lower-bound section uses Hyp(population,marked,draw). Positional notation is unsafe here.

Fix a population V of size N and a marked subset A of size K. Select S uniformly from all m-element subsets of V, and put Y = |A intersection S|. This is equivalent to intersecting two *independent* uniform subsets of fixed sizes. Two marginally uniform subsets without independence do not suffice.

An exact finite PMF can have outcome type `Fin (m+1)` and weight

    p(q) = choose(K,q) choose(N-K,m-q) / choose(N,m).

All products and the quotient above are interpreted in the reals. The outcome type enforces q <= m; without that condition, natural subtraction m-q would make the displayed formula wrong at some q > m. The denominator is positive by m <= N. Its support consists exactly of integers q satisfying

    max(0,m-(N-K)) <= q <= min(K,m).

Vandermonde gives total mass one. At N=0 validity forces K=m=0 and the distribution is the point mass at 0. At N=1 every valid distribution is deterministic. More generally K=0 or m=0 gives Y=0; K=N gives Y=m; m=N gives Y=K. These are proofs of degenerate cases, not additional hypotheses.

The suggested real formulas, with all casts occurring before real subtraction, are valid using total real division:

    mu = K*m/N;
    variance = K*m*(N-K)*(N-m)/(N^2*(N-1)).

At N=0 and N=1 the variance formula evaluates to 0. No proof may cancel N or N-1 until the relevant positive-population branch is established.

## 2. Individually reviewed candidate lemmas

### P01 — Normalization, support, and intersection-law equivalence

Under exactly K <= N and m <= N, the preceding weights are nonnegative, sum to 1, and equal the law of the intersection construction. Count m-subsets according to q marked elements: there are choose(K,q) choose(N-K,m-q) possibilities. The fixed-marked and independent-two-subset encodings agree by permutation symmetry. Empty populations are included.

### P02 — All factorial moments

For every natural r,

    E[(Y)_r] = (K)_r (m)_r / (N)_r.

Here falling factorials can be natural descending factorials cast into the reals; for natural arguments these agree with the real polynomial falling factorial. The statement is valid for *all* r with total division. At r=0 both sides are 1, also when N=0. At r>N, the support gives Y <= m <= N < r, so the left side is 0, and all relevant descending factorials on the right vanish, giving 0/0=0. For 1 <= r <= N count ordered distinct marked r-tuples that are selected; each is selected with probability (m)_r/(N)_r. If r>K or r>m but r<=N, both sides are again zero. This does not require an extra r<=N assumption in the final theorem.

### P03 — Expectation

Under the same validity assumptions, E[Y]=K*m/N. Either specialize P02 to r=1 or sum selection indicators of marked elements. For N>0 a fixed element is selected with probability m/N; for N=0 there are no marked elements and both sides are 0. This exact statement handles zero pile sizes.

### P04 — Variance and its zero cases

Under the same validity assumptions,

    Var(Y) = K*m*(N-K)*(N-m)/(N^2*(N-1)).

For N>=2, P02 at r=2 gives E[Y(Y-1)] = K(K-1)m(m-1)/(N(N-1)), and E[Y^2]=E[Y(Y-1)]+E[Y]. Subtract the square of the mean and simplify. The N<=1 branch is deterministic.

Consequently Var(Y)>0 exactly when 0<K<N and 0<m<N; these integer inequalities imply N>=2. Var(Y)=0 in every other valid case. The exact finite weighted variance agrees with the variance of the associated finite probability measure, because all random variables involved have finite support and hence all needed integrability properties.

### P05 — One-step exponential/transform comparison

For every real lambda,

    E[exp(lambda*Y)] <= (1-p+p*exp(lambda))^K,
    p=m/N.

For N=0 both sides equal 1. For N>0 use the symmetry of intersection sizes to view Y as sampling K entries without replacement from an N-vector containing m ones. Hoeffding's convex comparison with K independent samples applies to the convex function exp(lambda*x), for either sign of lambda. Equivalently, for 0<s<=1,

    E[s^Y] <= (1-p+p*s)^K.

The latter statement is the exact LT input used in TeX lines 3080–3150. Do not replace without-replacement samples by independent indicators as an equality. The probability comparison is an inequality. A Lean proof must supply a trusted existing comparison theorem or prove the finite comparison; the cited article is not itself a trusted Lean theorem.

### P06 — Two-sided concentration

The source's statement is mathematically valid with an absolute c>0; one may in fact take c=1/2 in

    P(|Y-mu| >= t) <= 2 exp(-t^2/(2*(mu+t)))     (t>=0).

The source's minimum with t is redundant for nonnegative mu,t because t^2/(mu+t)<=t, with total division at mu=t=0. For mu=0, Y=0 almost surely; t=0 gives the harmless bound 1<=2 and t>0 gives probability zero. The same treatment covers deterministic positive means.

For mu>0, P05 and log(1+u)<=u yield the Poisson-type MGF bound exp(mu*(exp(lambda)-1)). For the upper tail choose lambda=t/(mu+t)<1 and use exp(lambda)-1-lambda <= lambda^2/(2*(1-lambda)); this gives exp(-t^2/(2*(mu+t))). For the lower tail when t<=mu choose lambda=-t/mu and use exp(-s)-1+s<=s^2/2, giving exp(-t^2/(2*mu)), which is stronger. When t>mu the lower-tail event is empty. The union bound proves the result. Freezing an existential absolute c rather than 1/2 is also faithful to the source and avoids committing implementation to this particular proof.

### P07 — Small means and uniform one-edge deviation

Two useful exact consequences, not requiring positive variance, are:

    A>=1 implies
    P(|Y-mu| >= A*(sqrt(mu)+1)) <= 2 exp(-A/4);

    a>=2*mu and a>=0 imply
    P(Y>=a) <= 2 exp(-a/8).

For the first, t=A(sqrt(mu)+1) satisfies t^2/(mu+t)>=A/2. For the second use t=a-mu>=a/2 and mu+t=a, with the a=0 case handled separately. These exact bounds are preferable to freezing O(delta) or o(1) placeholders. Small means do not justify multiplicative lower bounds on realized counts; zero is often the overwhelmingly likely outcome.

### P08 — Point-mass anti-concentration

For positive standard deviation sigma,

    P(Y=q) <= 16/sigma

for every integer q. Outside the support the left side is 0. For zero variance use the bound P(Y=q)<=1; do not use 16/0=0 and do not write min(1,16/sigma) without a positive-sigma branch.

A fully elementary proof, avoiding the source's abbreviated central-window Stirling argument, gives the explicit constant 16. More generally let a finite PMF have contiguous support and be log-concave. Let M>0 be its largest mass, attained at mode z, and let ell=floor(2/M). Since M<=1, 2<=ell<=2/M, while ell+1>2/M. Monotonicity away from the mode and total mass one imply p(z+ell)<=M/2 and p(z-ell)<=M/2: otherwise the ell+1 terms between the mode and that endpoint already sum to more than one. Log-concavity then implies

    p(z +/- (j*ell+i)) <= M*2^(-j)    (j>=0, 0<=i<ell).

If an endpoint falls outside the support, its mass is zero and all later masses on that side are zero. Summing the second moment around the mode gives

    Var(Y) <= E[(Y-z)^2]
            <= 2*M*ell^3*sum_{j>=0} (j+1)^2*2^(-j)
            = 24*M*ell^3
            <= 192/M^2.

Thus M*sigma<=sqrt(192)<16. Hypergeometric log-concavity follows from its consecutive-mass ratio on the positive support:

    p(q+1)/p(q) = (K-q)(m-q)/((q+1)(N-K-m+q+1)),

which decreases as q increases. All denominator factors are positive on the interval where the ratio is used. This proof is uniform in small means, near-exhaustion, and all positive variances. The zero-variance cases are handled separately as above.

### P09 — Residual law under a positive finite reveal

Let S be a uniform m-subset of a population V of size N. For a fixed R subset of V, reveal S intersection R=D. This event has positive probability exactly when D subset of R, |D|<=m, and m-|D|<=N-|R|. Conditional on this event, S minus R is uniform among subsets of V minus R of size m-|D|. Therefore for a fixed B subset of V minus R,

    |B intersection S| | (S intersection R=D)
       ~ Hyp(N-|R|, m-|D|, |B|).

The named arguments above are population, marked, draw; symmetry of the last two counts permits other equivalent readings. Prove it by the bijection T -> D union T on the conditioning fiber. No new independence assumption is needed after the fiber is fixed. If the fiber is null, it is not a conditional probability space. State the result only on positive atoms or almost surely. A zero-measure conditional convention must not be presented as a probability distribution with the asserted mean.

The reveal set R can depend on independently revealed other columns: first fix those columns, so R is fixed, then apply the preceding argument. It cannot be an arbitrary set chosen by inspecting the unrevealed target-column symbols.

### P10 — Prescribed rows in a multicolor column and independence after conditioning

For a uniform column with fixed counts n_l summing to N, prescribe digits on r distinct labeled rows. Let r_l count the prescriptions of digit l. The event is positive exactly when r_l<=n_l for all l. Conditional on it, assignments to the remaining N-r labeled rows are uniform with counts n_l-r_l. If independent columns are conditioned by a product of such admissible column events, the residual columns remain independent. This follows directly from the product probability formula on finite positive fibers.

A pile of size zero permits no prescribed occurrence of its digit. A residual population of size zero has the unique empty assignment. The source's admissibility condition must be used before subtracting natural counts.

### P11 — Conditional hypergeometric transition and prefix mean

For independent uniform fixed-count columns, let S_t be the labeled rows matching a fixed target word through time t. Conditional on the entire first t-1 columns,

    |S_t| ~ Hyp(N, |S_(t-1)|, n^(t)_(a_t));
    E[|S_t| | earlier columns] = |S_(t-1)| n^(t)_(a_t)/N.

This is an exact positive-atom statement and hence an almost-sure conditional-expectation identity. Taking expectations yields E[|S_t|]=N product_{j<=t}(n^(j)_(a_j)/N). It includes empty populations and zero piles. For a proper fixed subset of row labels, the restricted pile counts are initially random; they are not silently equal to fixed global pile counts.

After prescribed labeled rows are removed, replace N by N-r and each chosen pile size by n^(t)_(a_t)-r_(t,a_t). These are the exact residual parameters, not the original ones. An unconditional multi-column prefix count is generally not itself a one-step hypergeometric variable.

### P12 — Successive thinning lower tail

Let independent uniformly selected subsets of an M-element labeled population have deterministic cardinalities m_t<=M. Starting from all M rows, let X_t be the size of their successive intersection. Put q_t=m_t/M and mu=M product q_t, using total division. Then

    P(X_h<=mu/2) <= exp(-c_Ch*mu),
    c_Ch=(1-log(2))/2 > 0.

For M=0 or any zero selected pile, mu=0 and X_h=0, so both sides equal 1. At h=0, X_0=M and the assertion is immediate. For M>0 and nonzero piles, apply P05 backwards with terminal s=1/2 and the affine recursion s_(t-1)=1-q_t+q_t*s_t. It gives

    E[2^(-X_h)] <= (1-(product q_t)/2)^M <= exp(-mu/2).

Markov at threshold 2^(-mu/2) proves the displayed constant. This proof avoids logarithms of possible zero population ratios. P10 applies the identical theorem on every positive prescribed-row fiber, using the residual means from P11. The r<=r0 asymptotic bound is not needed by the exact finite probability theorem.

### P13 — Prefix-tree concentration with explicit finite error

Let F be a deterministic ancestor-closed finite family of words with maximum depth h, and choose A>=1. With probability at least

    1 - 2*(number of nonroot nodes of F)*exp(-A/4),

every v in F obeys

    |C(v)-mu_v| <= |v|^2*A^2*(sqrt(mu_v)+1),
    mu_v=N*lambda_v.

Apply P07 conditionally on the preceding columns for each tree edge, take expectations, and union bound. On the intersection of those events set B_r=r^2 A^2. The source's deterministic induction is valid: for a child with digit probability p in [0,1], p*mu_parent=mu_child, and

    B_r + A*(1+sqrt(B_r)) <= B_(r+1).

This exact formulation handles zero-mean prefixes, all zero piles, and N=0. The asymptotic version in the TeX follows when h=O(log N), |F|<=N^D and A=N^(epsilon/4), for sufficiently large N. The non-exhaustion/collision-count consequence P(C(w)<2)<=exp(-c_Ch*mu) requires mu>=4; for small means use the general thinning bound or the trivial bound, not that particular event inclusion.

### P14 — Fine-to-coarse conditional point-mass transfer

Let U be contained in the finite revealing sigma-field G, let A be G-measurable, and let Z=A+Y. Let Good be G-measurable. Suppose on every positive G-atom in Good the conditional law of Y is a valid hypergeometric law with standard deviation at least s0>0. If S is any event contained in Good, then for every integer j,

    P(Z=j and S | U) <= 16/s0     almost surely.

First use P08 on each positive G-atom; the shift A is constant there. Restrict to Good and take conditional expectation back to U. S itself need not be G-measurable if S is contained in such a Good event. However, a high unconditional probability for S does not imply a uniform conditional high probability given U. The source correctly retains S in its conditional point-mass expression; it cannot simply be dropped.

### P15 — Exact deterministic non-exhaustion implication

Suppose R and B are disjoint subsets contained in an anchor V0 inside an N-point population, with |V0|<=N-h and h>0. Then with n=N-|R|,

    n-|B| >= h,
    1-|B|/n >= h/n >= h/N > 0.

This is the sample-complement estimate actually used by the homogeneous proof, with h>=chi*N. It does not follow merely from the existence of digit mass to the left and right of a crossing.

For valid hypergeometric parameters, positive L, alpha, beta, if

    mu>=L,
    1-K/N>=alpha,
    1-m/N>=beta,

then N>=2 and Var(Y)>=L*alpha*beta. Indeed positive mean forces K,m,N>0, positive complements force K,m<N, and the variance formula is mu*(1-K/N)*(1-m/N)*N/(N-1). This is an elementary implication; the difficult source-specific work is to establish its hypotheses. They must not be added as new assumptions to the false ambient theorem merely to make it provable.

### P16 — Random pile sizes / mixture interface

Let the cut sequence be an arbitrary random finite parameter value. Conditional on that value, generate independent uniform columns with its prescribed counts. Every preceding finite conditional law applies after first conditioning on this parameter, on positive atoms only. If the parameter lies in a good set with probability at least 1-epsilon and every good parameter has failure probability at most delta, then the unconditional failure probability is at most epsilon+delta.

Unconditional means and variances must be averaged correctly:

    E[Y]=E[mu(parameter)],
    Var(Y)=E[conditional variance]+Var(conditional mean).

A conditional hypergeometric variable with random parameters is generally not unconditionally hypergeometric. In particular a large *unconditional* variance cannot replace the conditional variance lower bound in P14. A mixture of two point masses is a simple counterexample to that replacement.

## 3. Concrete source counterexample

Take any N divisible by 3, k=3, and K_shuffle>=2; let every column have three piles of size N/3. Choose any fixed chi<1/3. Every column is chi-good, so local good-column frequency is satisfied as strongly as possible. Take the root ambient block w=empty and the one-letter prefixes y=z=x=(1).

Under the TeX definitions, I_left=0 and I_right=2, so y and z both make their first genuine crossing at column 1. They are admissible, nonterminal, retained, and fluctuation-regular. The two maximal side-piece expectations are N/3, attained at a=b=1, and

    c_F = (1/2)*log_N(N/3),
    c_L(x)=log_N(N/3).

Every continuation has smaller c_L, so the required uniform fluctuation-regularity holds. The interval occupied by the first digit 1 is nevertheless deterministically [N/3,2N/3), up to the irrelevant one-based endpoint convention.

In the source's case a=b, after revealing the rows whose column-1 digit is 1, the remaining population has size n=2N/3, marked count N/3, and draw count d2=2N/3=n. Thus

    Y3 ~ Hyp(2N/3,N/3,2N/3),
    Y3=N/3 surely,
    1-d2/n=0,
    Var(Y3 | F3)=0.

Both side means are macroscopic; this is not a small-mean or exceptional-pile phenomenon. It directly contradicts the strictly positive complementary-fraction conclusion in `lem:ub-ambient-conditioning-transfer` and the asserted conditional variance bound in `lem:ub-ambient-concentration-anti-concentration`.

It also contradicts the latter lemma's stated anti-concentration for arbitrary x in A_(y,z): its endpoints are deterministic. If S_x has probability tending to one, then the expectation of P(endpoint=its deterministic value and S_x | U_x) tends to one, whereas the asserted uniform upper bound tends to zero when delta is sufficiently small relative to the asymptotic c_F=1/2. No choice of null-atom convention repairs this.

The homogeneous paper prevents precisely this example. It starts the crossing/maximization indices at 2; N'=n^(1)_(x[1])<= (1-chi)N is its reserve of rows outside the anchor. Its three reveal cases repeatedly use a2+|R1|<=N', b2+|R2|<=N', or d2 approximately <=(N'/N)(N-n_digit). These inequalities supply the positive complementary population fractions. The TeX's replacements do not preserve them.

## 4. Other source gaps that must remain visible

1. **Conditioning on an ambient prefix does not only change N to its size.** The labels in B_w are determined by earlier columns. Conditional on that set, a later column restricted to it has random multivariate-hypergeometric counts sampled from the full N-row column. Conditional additionally on those restricted counts, its internal assignment is uniform, but those counts must be tracked. Treating the restricted piles as deterministic original proportions is unjustified.

2. **The transfer statement includes small or empty ambient blocks.** It asserts positive conditional-mean lower bounds without a large-mean restriction in its consequence. If the ambient block can be empty with nonnegligible probability, the corresponding conditional variables can be identically zero. A small-mean concentration upper bound supplies no positive lower bound.

3. **The endpoint-window proof uses a minimum as if it bounded both sides.** c_F is the minimum of the left and right log fluctuation scales. Hence all left summands are bounded by N^(2c_F) only when the left side is the smaller side, and conversely for the right. The homogeneous proof explicitly chooses the smaller side and transfers to the other endpoint using the block size. The TeX sentence asserting the bound simultaneously for both decompositions is not justified. This is a proof-repair issue distinct from the fatal non-exhaustion counterexample.

4. **Fine reveal measurability and the good event need exact definitions.** U_x must be measurable with respect to the finer reveal, including both which labeled rows have prefix x and their internal continuation data. The source's intended reveal sets have this property, but it must be proved. A good event on which the parameter-dependent variance is large must be contained in a good event measurable for that reveal; otherwise the stated conditioning step has not been established.

5. **Union bounds need an explicit finite family.** An N^(o(1)) count of all relevant prefix families is asserted without a full indexing construction. The stretched-exponential bounds would absorb any proved N^D count, so there is no need to freeze the stronger unsupported counting assertion.

6. **An event that restricts several columns need not preserve independence unless it factors.** Prescribing fixed labeled digits column by column does factor, as used in P10 and the source's lower-tail proof. Arbitrary exploration constraints or random prefix-selected rows can correlate columns and require an additional exact description of their conditioning fibers.

## 5. Dependency map for the assigned probability part

    valid counts + finite uniform subset model
      -> P01 normalization/support/intersection law
      -> P02 factorial moments -> P03 expectation -> P04 variance
      -> P05 convex exponential comparison -> P06 concentration -> P07 scales
      -> log-concave ratio -> P08 point masses

    finite positive fibers + uniform column assignments
      -> P09 residual subset law
      -> P10 residual multicolor law + retained column independence
      -> P11 conditional transitions and exact residual means
      -> P12 successive thinning lower tail
      -> P13 simultaneous prefix concentration

    P04 + P15 actual non-exhaustion hypotheses
      -> lower conditional variance
    P08 + lower conditional variance + P14 tower transfer
      -> conditional endpoint point-mass bound

    P16 mixture conditioning
      -> random-pile versions of all valid conditional probability statements

The missing arrow is from the current TeX's boundary definitions/local good-column assumption to P15's required population complement. That arrow is false for the current definitions. The upper-bound first-moment/edge-density proof depends on it, so completing the finite hypergeometric core does not complete that upper bound. The lower-bound thinning and simultaneous prefix concentration arguments can proceed independently of this false ambient assertion.

## 6. Recommended freeze boundary

Freeze the named finite parameters, PMF, finite probability/expectation/variance, exact all-order factorial moments, expectation, variance and degeneracy cases, and the finite positive-fiber conditional interfaces. Freeze concentration and point-mass claims only with explicit quantified absolute constants and an intended proof route. P08 supports the concrete constant 16. Keep the false source ambient transfer and source non-exhaustion applications outside the frozen theorem list; retain the counterexample and exact missing geometric obligation in the audit.

No further hypothesis should be attached to an already-frozen source theorem to bypass the counterexample. Any future revised ambient theorem or revised boundary construction is a new specification requiring the same independent review before implementation.
