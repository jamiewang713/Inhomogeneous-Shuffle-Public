# Whole-TeX reread: intended small non-singleton edge-density statement

This is an independent interpretation report, not a new theorem contract. I reread all 5,221 lines of `time_inhomogeneous_riffle_shuffle_unified_article.tex` in source order, including the inactive overview at lines 2562–2785 and the complete active lower proof. I also checked the permitted 2510 paper's initialization and first-moment arguments. No source, Lean file, or frozen-contract file was changed.

## 1. What the result is intended to mean

The estimate at lines 1496–1503 is an averaged overlap estimate for a fixed deterministic prefix cylinder. Its left side is

\[
D_x=\sum_{m=1}^{N-1}\mathbb P\{(m,m+1)\in E(G_{B_x})\}^2.
\]

For two independent copies generated from the same deterministic cut array, this is the expected number of common adjacent positions occupied by equal-string edges from the same prefix block in both copies. This interpretation is fixed by the shuffle-graph definitions at lines 460–472 and the identity at lines 1837–1842.

“Small” means small **expected occupancy exponent**, namely `c_L(x)<2δ`; it does not mean that the realized block has size zero or one. “Non-singleton” means that the deterministic stable family for the boundary pair does not stop immediately at its root `v=y∨z`, namely `A_stable≠{v}`. It does not mean that the realized occupancy is at least two. A prefix in this case may have zero, one, or several rows in a realization. These distinctions follow from the stopping definition at lines 661–686 and the separate terminal/root/first-crossing cases at lines 1699–1726.

The intended mechanism is:

1. The child prefix has only `N^{O(δ)}` rows with high probability, so its expected number of internal collision edges is bounded by the tail collision factor, up to `N^{O(δ)}` (lines 1569–1575).
2. Its much larger parent crossed the stability threshold only when passing to this child. The boundary pair supplies a purported remaining random translation of size `N^{c_F}`.
3. Conditioning on the internal word data fixes the internal edge offsets but leaves this translation random. A conditional atom bound supplies a factor `N^{-c_F}` to each edge probability (lines 1530–1541 and 1577–1579).
4. Only `N^{c_F+O(δ)}` positions are relevant. Squaring the pointwise probability and summing over that window leaves one net factor `N^{-c_F}` (lines 1581–1583).

Thus the printed conclusion

\[
D_x\le N^{-c_F(x;y,z)+2c_E(x)+O(\delta)+o(1)}
\]

claims a genuine spatial spreading gain. It is not just a bound on the expected number of internal edges, a conditional bound after the graph has been fixed, or a statement only after summing all prefix profiles.

## 2. Quantifiers supported by the complete text

The natural intended quantifier order is the following.

1. Fix `k,T,η,γ`; choose the regularity and truncation parameters in the nested order at lines 474–488; choose `N` sufficiently large only afterward.
2. Fix a deterministic integer cut array with every column sum `N` (lines 95–113). The matrix law is the uniform fixed-column law (lines 388–392 and 446–454), equivalently independent uniform assignments in its columns. This is stated again explicitly in the active lower setup at lines 2921–2923.
3. Fix a legal ambient prefix `w`, with its birth time and expected-size exponent `(r,b)` (lines 490–518). The whole deck is expressly included by `w=∅, r=0, b=1` (lines 497 and 1833–1834).
4. Fix an admissible compatible boundary pair `(y,z)` and its join `v`, all determined by the cut array (lines 529–643). Require the pair to be nonterminal, retained, and fluctuation-regular (lines 645–659).
5. Fix `x∈A_stable\Lambda` satisfying the three explicit small non-singleton conditions at lines 1488–1503. The estimate is uniform over the retained profile classes, rather than allowing its error or implicit constant to depend arbitrarily on `x` (lines 482–485, 1216–1217, 1666–1667).
6. Take probability over the matrix randomness for this fixed data. No random choice of `x`, no internal-data conditioning, and no averaging over random pile arrays occurs in the displayed conclusion.

For use in the first-moment proposition, the ambient tail is almost-profile-like, locally good, and satisfies `FM(r,b,T,η)` (lines 1817–1834). The structural edge-density lemma does not repeat all these assumptions, and the surrounding upper theorem supplies the broader intended application regime. I therefore tested the statement even under this stronger contextual reading; it still does not force the asserted spreading factor.

An eventual Lean signature would have to quantify uniformly over the cut arrays, ambient data, retained pairs, and prefixes after the hierarchy is fixed. Its `O(δ)+o(1)` cannot be formalized as an arbitrary real chosen separately to make each conclusion true: lines 1689–1692 and 1909–1913 require those losses to be chosen small enough relative to `η`. An exact implementation must eventually expose an error envelope and constant independent of the prefixes and final `N` limit. This report proposes no replacement envelope as an assumption.

## 3. Three different probability spaces occur

### Original fixed-column law

By lines 112–113, undecorated probability and expectation refer to the fixed cut array's shuffle-matrix randomness. In the whole-deck case this is unambiguous. A fixed ambient prefix determines a random subset of row labels under that law; restricting to this subset does not by itself replace the original population or condition on its realized cardinality.

The relative-coordinate convention at lines 509–512 says to remove the random translation of the **ambient block `B_w`**. It does not say to remove the translation of the child `B_x`. Removing the latter would remove precisely the random shift used at lines 1530–1541. In addition, a random recentering preserves each sample's edge count but does not in general preserve `D_x`; the coordinate convention must therefore be part of the definition of the edge events, not justified only by count invariance.

### Conditioning on internal information

`U_x` is specified at lines 1209–1212 and used at lines 1530–1541. It records the rows in `B_x` and their continuation strings. Given this information, the edge offsets inside `B_x` are fixed; the intended residual randomness is external placement.

The three more detailed reveal constructions at lines 1303–1415 are meant to produce a finer information partition containing `U_x`. Their hypergeometric parameters and the claim that a random shift remains must be proved for each positive-probability information fiber. An expectation-scale comparison for the original law does not automatically give a conditional variance lower bound on those fibers.

The text itself changes notation temporarily at lines 1286–1290: `N_w` is the realized ambient population and `n_l^{(j)}` there denotes corresponding ambient counts. That paragraph is not a global redefinition of the original deterministic counts in `c_L`, `c_E`, or `c_F`. A Lean implementation needs explicit separate names and a transfer theorem relating the two objects.

### Conditioning during recursive exploration

Lines 1923–1943 intend to apply the first-moment estimate inside residual large ambient blocks after conditioning on previously explored data. `RFM` supplies the required numerical inequalities for every accessible ambient block (lines 366–372), while conditional preservation is supposed to supply the residual shuffle law and retained empirical profile.

This is a conditional **application** of a uniformly proved fixed-data theorem. It is not permission to assume the edge-density conclusion on all exploration histories, nor to condition on an arbitrary event while preserving the original product probabilities. The exact conditional law of residual columns, and any independence between the two residual graph samples, remain proof obligations. The active lower proof confirms this intended standard: it explicitly proves residual-count changes and factorization of the conditioning event at lines 3138–3166 and repeats the same principle at lines 4432–4451.

## 4. What `c_F` actually denotes, and what it is intended to control

The literal definition at lines 619–643 is a deterministic proxy:

\[
N^{2c_F}=\min\left\{
\max_{M_w<i\le M_\vee}\mathbb E|I(P_{x,i})|,
\max_{M_w<i\le M_\vee}\mathbb E|I(Q_{x,i})|
\right\}.
\]

It uses expected side masses, not variances. It is constant along continuations beyond `v` because the side pieces allow arbitrary later digits. The fluctuation-regular condition at lines 647–652 is only a comparison between this side-mass proxy and `c_L`. Its proof at lines 965–993 is a first-moment comparison obtained from genuine left/right crossings.

The anti-concentration argument attempts to promote that proxy into a conditional standard-deviation scale. The extra ingredient needed for such a promotion is visible in its own variance formula: in addition to a large mean, both complementary fractions must be nonzero and quantitatively large (lines 1174–1178, 1343–1352, and 1400–1413). Positive masses on the two lexicographic sides do not alone ensure that an unrevealed sample is a proper subset of its population.

The later definition at lines 3362–3373 is instructive. There the author introduces a **different** quantity `c_loc(w)` from the actual variances of `L_w` and `U_w`. This does not rename or override `c_F`. It occurs in the lower setup, and the later relative endpoint theorem is proved directly from prefix concentration (lines 4123–4224). The active lower imports at lines 2844–2895 do not import the upper edge-density/anti-concentration theorem. Thus the full file recognizes a distinction between actual fluctuations and an upper-proof proxy; it does not contain a later convention making them automatically equal.

## 5. Initial good shuffles and the intended old-paper reduction

The strongest textual evidence for an intended initialization is the remark at lines 310–313: local good shuffles are called the time-inhomogeneous replacement for the homogeneous harmless shift. But no later upper-proof paragraph actually performs such a shift or excludes the first post-ambient column from the fluctuation maxima.

The old fixed-column paper does both relevant pieces explicitly:

* 2510 §3.1, PDF pages 12–13, removes an initial sequence by TV contraction and restarts at a good shuffle, with two further good shuffles nearby.
* Its Definition 4.3/Lemma 4.4, PDF pages 18–19, starts fluctuation side sums at column **2** and separates off the deterministic first-column prefix count. Lemma 4.5, page 20, uses the first good column to leave a proper population for a later reveal.

These are two different roles. “The first shuffle is good” is not itself a statement that its fixed pile counts fluctuate. The new maxima start at `M_w+1` (lines 623 and 628), and both boundary families permit genuine crossings at that same first post-ambient column (lines 534–539 and 554–559).

A charitable reading is that the author intended the old initialization/residual-population mechanism to be reconstructed under the local good-shuffle hypothesis. That identifies a missing reduction, not an already stated convention. Changing the start index, redefining the boundary families, or restarting from a newly conditioned ambient block would alter the displayed `c_F` or stable partition. None can be inserted silently into the frozen statements.

The local assumption controls macroscopic intervals of length `ρ` (lines 305–308 and 2902–2909). It guarantees available good columns over such intervals. It does not force every microscopic selected digit to have positive constant mass, force the stopping prefix to lie after an initialization interval, or forbid one exceptional early column. The profile truncation also permits finitely many exceptional selected digits, since their fraction `R_x` is `O(1/log N)` (lines 713–735 and 1095–1111).

## 6. Testing the strongest contextual reading

The issue is not confined to the previously discussed root singleton, or to a failure to assume enough total shuffles. One can test exactly the small non-singleton branch while keeping a long, good, well-mixed tail.

Let `N` tend to infinity through multiples of three, `k=3`, and take `K=floor(T log N)` for a fixed sufficiently large `T`, for example `T=3`. Let the first column have equal piles `(N/3,N/3,N/3)`, the second have piles `(2,N−2,0)`, and every later column again have three equal piles. Use the constant uniform three-pile profile.

For any fixed small `χ<1/3` and `γ<1`, all but one column are `χ`-good. The local good-column requirement holds on every length-`ρ` interval for large `N`; the one exceptional column changes profile counts by only `O(1/log N)`. The profile margins have a fixed negative buffer when `T=3`: `A(r,s)=(s−r)log 3`, `B_θ(r,s)=(θ−1)(s−r)log 3`, and the `θ=3` values bound the local margins uniformly for `b≤1−r log 3+o(1)`. In particular the whole-deck first-moment hypotheses do not exclude this sequence.

Take `w=∅`, `y=z=v=(1)`, and `x=(1,0)`. Both boundary crossings occur in the first, good column. The pair is admissible, nonterminal and fluctuation-regular. The original definitions give

\[
c_L(v)=\log_N(N/3),\qquad
c_F(x;y,z)=\tfrac12\log_N(N/3),\qquad
c_L(x)=\log_N(2/3).
\]

For fixed sufficiently small `δ>0`, `v` is above the stopping threshold and `x` is its first-crossing child. Thus `x∈A_stable\Lambda`, `A_stable≠{v}`, `c_L(x)<2δ`, and `c_F(x)≥δ−(log N)^{-1/2}`. The second-column selected digit is one exceptional position, so its profile is not discarded for `R_x>α_χ`.

There are exactly two rows having second-column digit zero. If both have first-column digit one and have identical future strings, they form the only edge in `G_{B_x}`, at the deterministic position `m=N/3+1`. No other position can support an edge from `B_x`. Consequently, with

\[
r_N=\frac{(N/3)(N/3-1)}{N(N-1)},\qquad
q_{\rm tail}=\prod_{j=3}^K\sum_\ell
\frac{n^{(j)}_\ell(n^{(j)}_\ell-1)}{N(N-1)},
\]

the exact density is `D_x=r_N² q_tail²`. Here `r_N→1/9`, while

\[
q_{\rm tail}/N^{c_E(x)}
=\left(1-\frac{2}{N-1}\right)^{K-2}\longrightarrow1.
\]

Thus `D_x=N^{2c_E(x)+o(1)}/81`, whereas the printed right side contains an additional `N^{-1/2+O(δ)+o(1)}`. Increasing `T` makes both sides smaller by the same tail factor; it cannot supply the missing spatial spreading. This test shows that FM, a good first shuffle, admissibility, profile truncation, non-singleton first crossing, and a long good tail do not jointly resolve the literal assertion.

## 7. An exact finite alternative under the existing unconditioned model

The full proof's underlying aim for this branch can be approached without endpoint anti-concentration. The following is an interpretation/proof alternative, not a new frozen declaration.

Let `N≥2`, let the columns be independent uniform fixed-count columns, let `x` be any prefix of length `M≤K`, and put

\[
\mu_x=N\prod_{j\le M}\frac{n^{(j)}_{x[j]}}N,
\qquad
q_{\rm tail}=\prod_{j>M}\sum_\ell
\frac{n^{(j)}_\ell(n^{(j)}_\ell-1)}{N(N-1)}.
\]

Then

\[
\begin{aligned}
D_x
&\le\left(\sum_m\mathbb P\{m\in E(G_{B_x})\}\right)^2\\
&=(\mathbb E|E(G_{B_x})|)^2\\
&\le\left(\frac{N-1}{2N}\mu_x^2q_{\rm tail}\right)^2
\le\left(\frac{\mu_x^2q_{\rm tail}}2\right)^2.
\end{aligned}
\]

The first inequality expands the square of a finite sum of nonnegative terms. For the remaining bound, an adjacent equal-string pair is among the unordered equal-full-row pairs whose common string has prefix `x`. Independence across columns gives their expected count exactly as

\[
\binom N2
\prod_{j\le M}
\frac{n^{(j)}_{x[j]}(n^{(j)}_{x[j]}-1)}{N(N-1)}
\ q_{\rm tail}.
\]

For each selected pile of size `n≤N`,

\[
\frac{n(n-1)}{N(N-1)}\le(n/N)^2.
\]

Substitution proves the displayed estimate. Zero selected piles, selected piles of size one, an empty prefix, and an empty tail are all covered. Legal status is needed only for subsequent logarithmic notation.

This remains valid for a prefix `x` inside any fixed ambient ancestor `w` in the original, unconditioned probability space: `μ_x` includes the full prefix from the original deck. It also remains valid if each sample's edge positions are recentered at the random left endpoint of `B_w`, because the proof uses only nonnegativity and the sample's total edge count. This does **not** assert that recentering preserves `D_x`; it proves the bound for either specified coordinate convention.

Furthermore

\[
q_{\rm tail}\le\prod_{j>M}\sum_\ell (n^{(j)}_\ell/N)^2
=N^{c_E(x)}.
\]

Using the source's expected-mass relation `μ_x=N^{c_L(x)+o(1)}` at lines 503–508 gives

\[
D_x\le\tfrac14 N^{4c_L(x)+2c_E(x)+o(1)}.
\]

If `c_L(x)<2δ`, this implies both

\[
D_x\le N^{2c_E(x)+8\delta+o(1)}
\]

and

\[
D_x\le N^{2c_L(x)+2c_E(x)+4\delta+o(1)}.
\]

The second consequence proves the printed small-singleton exponent by a different route, and even applies to every small block. The first gives the natural small non-singleton bound without the unsupported `−c_F` gain. No good event, exceptional-event remainder, or occupancy second-moment estimate is required for these finite inequalities.

Under an exploration conditioning, the same finite argument can be applied only after identifying the actual conditional law as independent uniform columns with their actual residual population and pile counts. The original unconditional `μ_x` and `q_tail` must not be retained automatically. This is precisely the kind of structural conditional-law obligation already intended by lines 1923–1943.

## 8. Why this weaker bound may still fulfill the branch's role

The first-moment proof does not ultimately need the isolated factor `N^{-c_F}` for its own sake. It needs the sum over an entropy class to be a negative power of `N` (lines 1873–1892). The published route combines the printed density with the auxiliary margin `N_2` (lines 1776–1800).

There is another numerical route under the already assumed `FM` margins. Write `v=y∨z`, `L_v=c_L(v)`, `F=c_F(v;y,z)`, and let `e` collect the existing deterministic small-parameter and final-limit errors. The source's first-crossing estimate and fluctuation comparison give

\[
S_x\le L_v-F+e\le\tfrac12L_v+2e
\le\tfrac12\beta_{r,b}(s)+O(e).
\]

The entropy and tail estimates therefore imply, for every `θ∈[3,4]`,

\[
H_x+2c_E(x)
\le\frac\theta2\beta_{r,b}(s)
-B_\theta(s,u)-2B_2(u,T)+O(e).
\]

Because this is a non-singleton first-crossing family, the root stopping test failed:

`L_v−F≥δ`. Combined with `F≥L_v/2−e`, this gives `L_v≥2δ−2e`, and consequently `β_{r,b}(s)≥−O(e)` by the maximal-pile comparison. Thus replacing `θ/2` by `(θ+3)/2` costs at most `O(e)`, rather than a fixed positive exponent. Taking the infimum gives

\[
H_x+2c_E(x)\le\mathcal N_1(r,s,u;b)+O(e)\le-\eta+O(e).
\]

The finite bound from section 7 adds only `8δ+o(1)`. With the existing hierarchy making these losses smaller than the margin, the entropy-weighted contribution still decays. This uses the already present `N_1` hypothesis; it introduces no additional margin or probabilistic assumption.

This explains a possible way to preserve the *purpose* of the small non-singleton branch and the final reduced upper target while changing that intermediate estimate. It is also consistent with the file's conclusion that `Λ_2` is an auxiliary proof diagnostic, not a separate critical obstruction (lines 2515–2518). It does not retroactively make the printed `−c_F` assertion true. It does not by itself complete the large-block density argument or the conditional exploration proof.

## 9. Interpretation verdict for later formalization

Supported by the full text:

* deterministic prefix families and uniform estimates after the parameter hierarchy;
* fixed-column, independent-column matrix randomness;
* small expected size, as distinct from realized size;
* non-singleton stopping at a descendant, as distinct from a one-row block;
* external-placement averaging before squaring edge probabilities;
* conditional reapplication to residual large ambient blocks, after proving their law and regularity;
* a profile-class first-moment bound as the ultimate use of this branch.

Not entailed by any whole-file convention:

* omitting the first post-ambient column from the stated `c_F`;
* assuming every relevant prefix already lies beyond an initial good-column buffer;
* treating expected side mass as a positive conditional variance;
* discarding every prefix containing an exceptional digit;
* interpreting the displayed density as already summed over profiles or as conditioned on an event that creates a random shift.

The most faithful eventual formalization should preserve this distinction. Either the initialization and fluctuation proxy must be explicitly repaired before the printed spatial-spreading estimate is adopted, or the small-block portion of the proof can be rebuilt from the exact pair-counting inequality and the existing stronger margin. The latter route respects the original model and its assumptions, recovers the small-singleton claim, and can supply the small non-singleton branch's first-moment role. It remains a visible change to the intermediate small non-singleton statement, so this report does not alter the freeze or implement it.
