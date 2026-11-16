# Large blocks and the final first moment: independent adversarial investigation

This is a bounded mathematical investigation, not a new frozen contract or
a Lean proof. No assumptions, definitions, contracts, or code were changed.
The source material is the authorized TeX, both authorized PDFs through
their existing extracts, and the earlier independent audit.

## Result

No counterexample to the final `prop:ub-first-moment` was found. This is
not a proof that the proposition is true. There is, however, a concrete
counterexample to the printed **large-block edge-density estimate itself**,
in addition to the previously identified conditional anti-concentration
failure. A related construction also contradicts the printed small
non-singleton density estimate. Both constructions satisfy the final
macroscopic almost-like, local-good, and variational assumptions. Their
actual lower bounds still decay polynomially, so neither contradicts the
final proposition.

A repair must therefore replace the density inputs, not merely supply
missing details for the written conditional hypergeometric argument.

## A common explicit environment

Let `N=3^n`, `k=3`, and choose

`T*log 3 = t = 31/20 = 1.55`, `eta=1/20`.

The macroscopic profile is constantly the uniform ternary vector. Take
the whole-deck ambient block, `r=0`, `b=1`. Let delta be positive and
sufficiently small. Put

`M=floor((1/2-2*delta)*n)`, `j=M+1`, `K=floor(t*n)`.

All columns are uniform ternary except column j. For a fixed desired size
exponent ell, set

`a=1/2+2*delta-ell`,

`n_0^(j)=floor(N^(1-a))`,

and split the remaining cards between piles 1 and 2 as equally as possible.
The choices below have `0<a<1`, so all piles used by the construction are
nonempty and the rare pile still contains a positive power of N cards.

Every column is chi-good for any fixed sufficiently small chi. The one
outlier column does not change almost-likeness to the constant uniform
profile for the fixed finite partition and positive rho, phi: its effect
on each normalized cell count is at most `1/log N`, and endpoint counting
errors are absorbed for large N.

The profile variational conditions hold with margin eta. Indeed, at
theta=3, writing `l=log 3`,

`N1(0,s,u;1) <= 3-2*t-l*s <= -1/10`,

`N2(0,s,u;1) <= 1-2*t+l*s <= 1-t = -11/20`,

while `N3(0,s;1)=1-t` and `beta(T)=1-t`. Thus all four source FM
requirements hold. No homogeneous cutoff constant is used here; these
are direct evaluations of the inhomogeneous variational inequalities.

## The stable block and its deterministic anchor

Take the source boundary pair `y=z=[1]`, and let x be the word of length j
whose first digit is 1 and every remaining digit is 0. The first column
is uniform, so the source left and right indices are 0 and 2. Thus both
boundary words are admissible genuine crossings with zero outward
violations. They are compatible and nonterminal, and

`F = (1/2)*log_N(N/3) = 1/2-1/(2*n)`.

The parent of x has length M and size exponent

`L_parent = 1-M/n = 1/2+2*delta+O(1/n)`.

After the rare final digit,

`L = cL(x) = ell+o(1)`.

Hence the parent does not satisfy `Stop`, while x does. Thus x belongs
to the actual source first-crossing stable family, not to its terminal
fallback. It has precisely one exceptional digit, so it survives the
exceptional cutoff for all sufficiently large N. All earlier extension
digits are 0, so the source entropy is zero.

The interval for x starts exactly at the first position of the first-column
digit-1 pile: its global left endpoint is deterministic. In one-based
vertex labels, the fixed candidate edge is `(N/3+1,N/3+2)`.

Let `X=|I(B_x)|`, `mu=EX=N^(ell+o(1))`, and let

`A_tail=3^(K-j)`, `E=cE(x)=-log_N A_tail`.

Then

`E=-(t-1/2+2*delta)+o(1)=-1.05-2*delta+o(1)`.

## Actual large-density counterexample

Choose `ell=1/20`, with `2*delta<ell`. This is a large stable block under
the literal source size criterion.

The exact two-row prefix probability implies `Var(X)<=EX`, since each
fixed column has negative pair correlation for a prescribed digit and
columns are independent. Therefore

`P(mu/2 <= X <= 2*mu) = 1-o(1)`.

Conditional on the prefix row set of size m in this range, the tail
columns are still independent uniform fixed-count columns. Their law on
these m labeled rows is uniformly multiplicatively `1+o(1)` close to
m iid uniform tail words. To see this, for one uniform column and a
prescribed pattern with digit counts `m_0,m_1,m_2`, its density relative
to iid uniform digits is

`3^m * product_a (N/3)_(m_a) / (N)_m`.

The logarithm is `O(m^2/N)` uniformly over patterns. Across all remaining
columns it is `O(K*m^2/N)=o(1)`, since `m=N^(1/20+o(1))`.

For m iid uniform words from an ordered alphabet of size `A_tail`, with
`A_tail/m -> infinity`, the probability that the first two order statistics
are equal is at least `c*m/A_tail`. One direct proof sums the disjoint
events that exactly two words equal r and all others exceed r, for
`1 <= r <= floor(A_tail/m)`:

`sum_r choose(m,2)/A_tail^2 * ((A_tail-r)/A_tail)^(m-2)`.

Every term in this range has a constant lower bound on its last factor,
and there are order `A_tail/m` terms. The relative-density estimate
transfers this lower bound to the actual fixed-column tail law.

Since all x-rows precede every other row in the first-column digit-1 pile,
this collision is an edge at the same deterministic global location.
Consequently

`sum_m P((m,m+1) in E(G_Bx))^2 >= N^(2*ell+2*E-o(1))`.

The printed large-density upper bound has exponent

`4*ell-1/2+2*E+O(delta)+o(1)`.

The lower exponent exceeds the upper exponent by
`1/2-2*ell=2/5`, before the arbitrarily small delta losses. Thus the
printed estimate is false. With the displayed numerical choices, the
lower exponent is approximately `-2-4*delta`, while the proposed upper
exponent is approximately `-2.4-4*delta`.

The use of multiplicative approximation above is essential: an additive
total-variation error would be larger than the rare collision probability
and would not justify this counterexample.

## Actual small-density counterexample

In the same construction choose `ell=-epsilon`, where
`0<epsilon<1/8`, for example `epsilon=1/100`.
The block is a small non-singleton first crossing with `F` bounded away
from zero. Its expected population tends to zero.

The fixed-column factorial-moment formulas give

`E(X)_2=(1+o(1))*mu^2`, `E(X)_3<=mu^3`.

The first equivalence holds because the smallest prescribed pile count
is still a positive power of N, so the products of falling-factorial
corrections tend to one. Since `(x)_2<=(x)_3` for integers `x>=3`,

`P(X=2) >= (E(X)_2-E(X)_3)/2 = (1+o(1))*mu^2/2`.

For those two rows, the independent uniform tail columns give equal tail
words with probability `(1+o(1))/A_tail`. They again produce an edge at
the deterministic anchor. Hence

`sum_m P((m,m+1) in E(G_Bx))^2 >= N^(4*ell+2*E-o(1))`.

The printed small-density exponent is `-1/2+2*E+O(delta)+o(1)`, which is
strictly smaller when `epsilon<1/8`. For epsilon=1/100 the gap is 0.46.
The earlier alternative using `sum p_m^2 <= (sum p_m)^2` does not make
this false point-mass inference and remains a possible small-block route.

## Why this has not refuted the final proposition

Both actual lower bounds above are negative powers of N. The examples
show that a proposed intermediate upper bound decays too quickly; they
do not show that expected common edges fail to decay.

The simplest whole-graph collision estimate also cannot prove the final
claim under its stated margins. If `C_full` counts unordered equal-row
pairs, then exactly

`E C_full = choose(N,2)*product_j [sum_a n_a^(j)*(n_a^(j)-1)/(N*(N-1))]`,

and each bracket is at most `sum_a (p_a^(j))^2`. Thus

`E common edges <= E edges <= E C_full <= N^(2-B2(0,T)+o(1))`.

This only closes when `B2(0,T)>2`; the valid uniform FM example has
`B2(0,T)=1.55`. Squaring the total expected edge count has the same
threshold. These coarse collision bounds therefore leave a genuine
missing localization or smoothing gain.

Trying to replicate the deterministic-anchor example at many arbitrary
prefixes loses its defining property: fixed column totals fix the
first-column pile boundaries, but mixed-prefix population counts are
random. This obstructs the straightforward attempt to amplify these
examples into a final nondecay counterexample. It is not a proof that all
such amplification mechanisms are impossible.

## A possible reserve-aware replacement and its exact missing work

The deterministic-column PDF `2510.22783v1`, Definition 4.3 and Lemma 4.5
(pp. 18–22), starts boundary crossings after a first good column and
omits that column from the fluctuation maxima. Its reserve is a different
fact from the false assertion that positive side mass alone prevents
exhaustion. The multinomial PDF `2103.05068v3`, Section 4.2 and Lemma 4.13,
uses an iid/binomial shift whose law is unavailable under fixed counts.

A mathematically plausible replacement is to choose a chi-good anchor
column within rho macroscopic time of the ambient start and split into
prefixes through that anchor. The local-good assumption supplies such a
column whenever the relevant tail has length at least rho. There are at
most `k^(rho*log N+O(1)) = N^(rho*log k+o(1))` prefixes, an explicit loss
that can be budgeted. For each such prefix v, its row set V is contained
in one anchor pile, giving the deterministic bound

`|V| <= (1-chi)*N`.

For a later unrevealed column and disjoint revealed/sample subsets
`R,B` contained in V, this gives the genuine reserve

`(N-|R|)-|B| >= N-|V| >= chi*N`.

This establishes the sample-complement factor for the unequal-column
cases using the full global residual population. It does not justify
replacing that population by the ambient set V. In the equal-column
case, revealing all rows of one digit changes the residual population;
one must additionally prove concentration of the outside-V rows carrying
the remaining digits. A variance or complement bound for that case is
not automatic from the displayed deterministic reserve.

The variational margins can survive this short shift without invoking
a homogeneous cutoff constant. If the new ambient exponent is at most
`b+o(1)` and its start is `r'<=r+rho+o(1)`, boundedness
`0<=a(t)<=log k` gives

`beta_new(s) <= beta_old(s)+rho*log k+o(1)`.

All beta coefficients in N1, N2, and N3 are positive and at most 7/2,
so the margin loss is at most `(7/2)*rho*log k+o(1)`. This comparison
uses the ordinary interval additivity of A. Even under a totalized
integral interpretation, in the relevant `b>=-eta/2` case the tail FM
condition forces `A(r,T)>=eta/2>0`, hence integrability on that interval;
restriction and additivity do not require a newly postulated hypothesis.
Very small ambient exponents can instead be handled by their factorial
population bounds. Also, if a tail shorter than rho had `b>=-eta/2`,
the tail FM margin would contradict `A(r,T)<=rho*log k` once rho is
chosen sufficiently small.

This describes an alternative proof architecture, not a completed proof.
It still needs actual derived theorems establishing:

1. The conditional residual law, with the internal graph information
   measurable under the chosen finer reveal.
2. Both complementary fractions and the mean lower bound, uniformly in
   every applicable boundary/continuation case, including the equal-column
   residual population.
3. Concentration for the required prefix/lexicographic subsets, with the
   actual number of sets in the union bound.
4. Smoothing and localization for a partition based on crossings after
   the anchor, and numerical/entropy bookkeeping for that partition.
5. A valid localization threshold gap and a separate polynomial error
   for discarded mass, avoiding the two earlier threshold/coverage errors.

The current source's fluctuation F cannot simply be retained in this
replacement: it includes deterministic side pieces, and the counterexamples
above rule out the desired source density inequalities with that F. Any
new analysis partition or additional theorem must be independently reviewed
and frozen before implementation. No such change was made here.
