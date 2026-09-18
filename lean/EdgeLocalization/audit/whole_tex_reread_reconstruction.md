# Whole-source reread: meaning and use of the edge-density estimates

This is an independent reread of **all 5221 lines** of
`time_inhomogeneous_riffle_shuffle_unified_article.tex`, in source order.
The sequential reading covered 1–520, 521–1040, 1041–1560, 1561–2080,
2081–2600, 2601–3120, 3121–3640, 3641–4160, 4161–4680, and 4681–5221.
Targeted comparisons used only the two permitted PDFs. No source, frozen
contract, or Lean statement was changed. The finite inequalities below are
mathematical proof proposals, not newly implemented or silently substituted
formal statements.

## 1. What the result is trying to measure

For a deterministic prefix (x), write

\[
 p_x(m)=\mathbb P\{(m,m+1)\in E(G_{B_x})\},\qquad
 D_x=\sum_m p_x(m)^2,\qquad e_x=|E(G_{B_x})|.
\]

The density result concerns **the sum of the squared probabilities at the
individual edge locations**, not the expected number of edges in a single realization.
For two independent copies it is exactly the expected number of matching
edges contributed by the same prefix block. This is stated explicitly in
the first-moment identity at 1837–1841 and its block reduction at 1860–1869.

The proposed mechanism at 1530–1541 is this: condition on the internal row
set and its continuation strings, so that the internal graph is fixed up to
translation. If a random translation has point masses at most (N^{-F}),
then (p_x(m)\lesssim (\mathbb E e_x)N^{-F}). If the relevant locations
occupy only (N^F) positions, one expects

\[
 D_x\lesssim (\mathbb E e_x)^2N^{-F}.
\]

Here and below (F=c_F^{r,b}(x;y,z)), (L=c_L^{r,b}(x)), and
(E=c_E(x)). The large-block calculation uses
\(\mathbb E e_x\lesssim N^{2L+E}\), giving (N^{4L-F+2E})
(1550–1567). The small non-singleton calculation absorbs the small block
size in (N^{O(\delta)}), giving (N^{-F+2E+O(\delta)})
(1569–1583). This interpretation agrees with the homogeneous paper's
explicit outline: stable blocks are meant to behave like edge patterns
spread through their possible locations; see 2103.05068v3, pp. 18–19,
especially (4.8)–(4.10), and pp. 24–25, Lemmas 4.12–4.14.

“Non-singleton” refers to the **stopped prefix family**
\(A_{y,z}^{\mathrm{stable},r,b}\ne\{y\vee z\}\). It does not assert that
the random block contains more than one row. Such a block can have zero,
one, or two rows. The stopping definition (661–696) and the repeated use
of the parent condition (999–1007 and 1776–1782) make that reading
unambiguous. An exceptional last digit can cause a large jump from a
substantial parent to a very small child.

## 2. Role in the whole upper proof

The dependencies found in the complete source are:

1. **Model and numerical data:** fixed column counts and independent column
   assignments, profile costs, and global margins (85–247); empirical
   profile and local good-column hypotheses (249–313); local margins and
   recursive first-moment condition (315–384).
2. **Graph-to-distance reduction:** the sorted-row graph, independent
   uniform value permutation, truncated second moment and sparse factorial
   bound (388–438).
3. **First-moment decomposition:** fixed ambient prefix and exponents
   (490–519), first left/right boundary crossings and stable stopping
   (521–697), profile statistics (699–747), partition and profile
   estimates (788–1037), then discarded profiles and class count
   (1039–1119).
4. **Geometric and probabilistic block estimates:** concentration and
   proposed conditional anti-concentration (1121–1434), relevant stable
   blocks for one edge (1436–1484), density cases (1486–1638), and terminal
   singleton estimate (1640–1660).
5. **Class sums:** numerical inequalities (1662–1815), followed by the
   actual block-density sums (1817–1914). The count of prefixes in a class
   supplies (N^{H_x}). Large blocks use the exponent
   (4L-F+2E+H) (1878–1885); small non-singletons use
   (-F+2E+H) (1886–1892); remaining small singleton and terminal classes
   are treated separately (1894–1908).
6. **Conditional exploration and distance:** the first-moment proposition
   is intended to be reapplied after exploration; conditional preservation
   and decomposition into ambient blocks are sketched at 1923–1943.
   Directional conditional first moments give exponential moments
   (1945–1972); regularity and sparsity then complete the distance bound
   (1974–1997). Random pile sizes are treated by conditioning on typical
   realized cuts and averaging (1999–2011).
7. **Numerical reduction:** a buffered global margin implies recursive
   local margins (2013–2157); monotonicity gives a critical-time upper
   bound (2159–2321). The later inequalities
   (B_2\ge A), (B_3\ge2A) show
   (\Lambda_2,\Lambda_3\le\Lambda_0) (2323–2469), and identify the
   full and reduced thresholds (2471–2553).

The distinction between the first moment and the recursive exploration
is real. The first-moment proposition is stated for a fixed ambient
prefix and two independent copies (1822–1834). Its block estimates are
unconditional probabilities in that model. They are proved, or proposed
to be proved, by conditioning internally on \(\mathcal U_x\). They are
not statements conditioned on the final explored sigma-field, nor is
\(D_x\) an expectation of squared conditional probabilities.

The conditional exploration theorem later needs a precise residual-law
statement before that fixed-model proposition can be applied. The phrase
“bound small blocks directly by total size” at 1943 refers to the
**unrevealed ambient blocks of that exploration**, not to all small stable
children appearing in 1886–1892.

## 3. Meaning of (b), (c_F), and the several populations

The ambient exponent (b) is the expected size exponent of a fixed prefix
block, with the original (N) as base (490–508). Thus

\[
 \mathbb E|B_w|=N^{b+o(1)},\qquad
 c_L^{r,b}(x)=b-\frac1{\log N}\sum_{M_w<j\le M_x}
                  \log\frac N{n_{x[j]}^{(j)}}.
\]

It is not a new population size, a conditional variance exponent, or a
change from (\log N) to (\log|B_w|). All local numerical formulas keep
this normalization. The accessible comparison is
\(b\le1-A(0,r)+o(1)\) (368 and 2063–2145). For the maximal accessible
choice, \(\beta_{r,b}(s)=\beta(s)\); other choices only decrease the
relevant local margins.

The upper (c_F) is literally a minimum of logarithms of square roots of
**expected side-piece counts**, whose maxima include (i=M_w+1)
(619–638). It is fixed along every continuation of the same boundary pair
(640–643, 1693–1696). This constancy is intentional: a small descendant is
supposed to retain the location uncertainty inherited from its earlier
boundary pair. Fluctuation regularity says (F\ge L(\xi)/2-o(1))
(645–657); it is a comparison of these defined exponents. It does not
independently say that any conditional variance is positive.

The source changes the meaning of “population” in the upper conditioning
proof. Lines 1256–1258 say that conditioning on the ambient block changes
the initial population to \(|B_w|\). Lines 1284–1290 then explicitly
intersect all row sets with (B_w), use (N_w=|B_w|), and temporarily
reinterpret the column counts as counts within that slice. Those are
material instructions, not an implicit convention to keep outsiders.

The active lower proof gives a more precise distinction. At 2961–3016,
the fixed label set has size (M), while the survivor count (X_t) is
thinned by
\(X_t\mid\mathcal S_{t-1}\sim\operatorname{Hyp}(M,X_{t-1},m_t)\).
The population remains (M); it does not become (X_{t-1}). In the
original law, (M=N) (2996–3001). Prescribing finitely many complete row
values leaves a new whole population (N-r) with explicitly reduced
column counts (3032–3077, 3134–3167). This is not the same operation as
restricting attention to a prefix slice of the remaining rows. The lower
factorial argument again uses residual population (N-b) at 4400–4452;
that (b) is an integer number of prescribed rows, unrelated to the
upper ambient exponent.

## 4. Is an initial shuffle or shift implicit?

There is one explicit pointer: the remark at 310–313 calls the local
good-shuffle condition a replacement for the old harmless shift ensuring
good initial columns. However, no ensuing definition selects an initial
good anchor, excludes its coordinate from the (c_F) maximum, or retains
its outside rows as a reservoir. The whole-deck convention remains
\(r=0,b=1,w=\varnothing\), and the first allowable crossing is the first
post-ambient column (490–518, 534–592, 619–638).

The deterministic-cut paper makes all three old ingredients explicit:

- 2510.22783v1, §3.1, pp. 12–13, uses convolution contraction to discard
  a short initial string of shuffles and starts at a good column.
- Its Proposition 4.2 and Definition 4.3, p. 18, assume that first column
  is good and start boundary crossings strictly after it.
- Its fluctuation maxima start at coordinate **2**, p. 19. In Lemma 4.5,
  pp. 20–22, the first-column slice has size
  (N'=n_{x[1]}^{(1)}\le(1-\chi)N), while the hypergeometric residual
  population still comes from **all (N) rows**. In particular,
  (a_2+|R_1|\le N'\le(1-\chi)N) supplies a non-exhaustion estimate.

This comparison identifies the intended source of the missing spatial
randomness. It does not turn the TeX's current indexing into old indexing.
Even making the first actual column good is insufficient for the literal
new definition: its fixed side counts are still included in (c_F).
Selecting an anchor and changing the boundary decomposition may be a
promising new proof with existing local-good assumptions and numerical
buffers. It is a substantive decomposition change, not an assumption-free
proof of the displayed unchanged per-block statement.

The independent uniform permutation in the component-sorting
representation is also not an initial shuffle that moves graph edges.
It randomizes values assigned to graph components after the graph on
sorted ranks is constructed (388–408; 2841–2870; 5151–5153). It cannot
randomize a deterministic boundary between first-column piles.

## 5. A valid alternative for the actual small-class use

The full reread reveals that the (-F) saving is **unnecessary for the
small non-singleton class sum**. This is stronger information than merely
finding a defect in the displayed bound. It follows from an exact
fixed-column calculation and the one-column dominance inequality already
proved later in the source.

Assume (N\ge2), fix a deterministic legal prefix (x) of length (M),
and put

\[
 \mu_x=N\prod_{j\le M}\frac{n_{x[j]}^{(j)}}N,\qquad
 q_x=\prod_{j>M}\sum_\ell
       \frac{n_\ell^{(j)}(n_\ell^{(j)}-1)}{N(N-1)}.
\]

Every adjacent equal-string edge maps injectively to its unordered pair
of row labels. Summing over all pairs and using independence of columns,

\[
 \begin{aligned}
 \mathbb E e_x
 &\le {N\choose2}\prod_{j\le M}
       \frac{n_{x[j]}^{(j)}(n_{x[j]}^{(j)}-1)}{N(N-1)}\;q_x\\
 &\le \frac{\mu_x^2q_x}{2},
 \end{aligned}
\]

because (n(n-1)/(N(N-1))\le(n/N)^2). This uses the actual
without-replacement pair probabilities, not independence of different
rows. Nonnegativity gives the deterministic inequality

\[
 D_x=\sum_m p_x(m)^2\le\Big(\sum_m p_x(m)\Big)^2
      =(\mathbb E e_x)^2\le\frac{\mu_x^4q_x^2}{4}.
\]

Thus (D_x\le N^{4L+2E+o(1)}/4). For (L<2\delta), this is

\[
 D_x\le N^{2E+8\delta+o(1)}/4.
\]

It also gives the printed small-singleton exponent:

\[
 4L+2E\le2L+2E+4\delta.
\]

No concentration event, endpoint window, or positive variance is needed.
For (N=0,1), there are no edges and one handles that case before writing
the denominators. A selected pile of size zero or one makes the relevant
two-row factor zero; an empty tail has product one; a zero tail
coincidence factor forces the expected edge count to be zero. All these
cases are consistent with the finite bound.

For the class estimate, abbreviate

\[
 v=y\vee z,\quad L_v=c_L^{r,b}(v),\quad
 \beta_s=\beta_{r,b}(s),\quad\beta_T=\beta_{r,b}(T).
\]

Let (\varepsilon) stand for the source's uniform profile errors.
In any retained nonterminal first-crossing non-singleton case,

\[
 L_v-F\ge\delta,\quad F\ge L_v/2-o(1),\quad
 S_x\le L_v-F+O(\varepsilon),\quad
 L_v\le\beta_s+O(\varepsilon).
\]

In particular (L_v\ge2\delta-o(1)), so
\(\beta_s\ge-O(\varepsilon)-o(1)\). Use the entropy estimate at
\(\theta=3\) (925–930), (B_3\ge2A), and (B_2\ge A)
(2349–2367):

\[
 \begin{aligned}
 H_x+2E
 &\le3S_x-B_3(s,u)-2B_2(u,T)+O(\varepsilon)+o(1)\\
 &\le\tfrac32\beta_s-2A(s,T)+O(\varepsilon)+o(1)\\
 &=2\beta_T-\tfrac12\beta_s+O(\varepsilon)+o(1)\\
 &\le-2\eta+O(\varepsilon)+o(1).
 \end{aligned}
\]

Consequently

\[
 \sum_{x\in\mathcal C}D_x
 \le N^{-2\eta+8\delta+O(\varepsilon)+o(1)}
\]

for the same retained profile classes, before the already-present class
count loss (N^\epsilon). This supplies the decay needed at 1886–1892
using only the existing tail-size margin. The parent-crossing estimate
remains valid when the final digit is exceptional: that digit changes
(S_x) by exactly zero (1005–1007), however large its cost (Q_x).
The entropy argument uses the source's existing truncation
(R_x\le\alpha_\chi); no bound on an individual exceptional cost is
introduced.

This proof does not need the extra (F\ge\delta-(\log N)^{-1/2})
split. It covers any retained nonterminal small non-singleton first
crossing, and hence avoids relying on the low-(F) singleton inference
at 1585–1592. Terminal fallback blocks are first excluded by the existing
tail-size reasoning (1709–1726); terminal boundary-pair singletons remain
a separate case. If a terminal-time first crossing survived the same
class assumptions, the inequalities above would apply with (E=0);
there is no hidden “last digit is good” requirement.

This is an **alternate proof of the needed aggregate conclusion**. It
does not prove (D_x\le N^{-F+2E+O(\delta)+o(1)}). In particular it does
not contradict the previously checked two-row example: that example can
violate the extra (-F) saving while its contribution still decays fast
enough for the main first moment.

## 6. Exact scope of conditioning for that alternative

For the first-moment proposition's **fixed ambient prefix** (w), apply
the exact calculation above to the entire deterministic extension (x).
It gives the unconditional bound with
\(\mu_x=\mathbb E|B_x|=N^{c_L^{r,b}(x)+o(1)}\), even though membership
in (B_w) is random.

If one conditions on all columns through (M_w), the set of labels in
(B_w) is fixed with some size (h). Future columns remain independent
columns on all (N) labels, and the conditional version uses

\[
 \mu_{x\mid w}=h\prod_{M_w<j\le M}
                         \frac{n_{x[j]}^{(j)}}N.
\]

The conditional second factorial count starts with \({h\choose2}\),
but the per-column denominators remain (N(N-1)). Thus the same bound
holds with this conditional mean. One cannot replace (h) by its
unconditional expectation in a pointwise conditional statement without
another estimate.

If an exploration really produces an independent fixed-column law on
(M') unexposed labels, the same finite argument applies with (M') and
the actual residual counts. Arbitrary conditioning on selected graph
information need not have that law. Establishing it, controlling its
profile, and identifying its conditional exponent are obligations of
1923–1943, not consequences of an interval recentering convention. The
alternative therefore repairs the fixed-model small-class step, while
leaving the precise recursive-conditioning interface to be proved.

## 7. What the active lower proof says about the intended geometry

Lines 2562–2785 are inside a `comment` environment. They contain an older
lower blueprint and a randomized lower extension, not an active proof.
The active lower proof begins at 2791 and completes at 5206. It imports
graph representation, the regular profile approximations, one-column
hypergeometric facts, and numerical dominance (2841–2895), rather than
the upper anti-concentration or edge-density lemma.

Its two obstructions match the **reduced** upper numerical conditions:
the largest-prefix obstruction is governed by \(\Lambda_0\)
(3375–3428); the cold-spot obstruction is governed by the large-block
expression \(\Lambda_1\) (3430–3798). The witness makes collision count
larger than the square root of the target region's size. Type selection,
bridge buffers, relative localization, and fixed-column occupancy
estimates establish this (3800–4895); a translate-scan ascent test then
detects it (4897–5163), giving the matching lower theorem (5165–5206).

At 3449–3451 the ambient location enters only as an unknown random
translation. The relative endpoint theorem gives an upper deviation
bound inside the ambient block (4123–4224), and subsequently adds back
the random shift. The lower test scans all (N+1) possible translates
(4899–4948, 5151–5162). It therefore does not need the ambient shift to
be spread out. Deterministic first-column boundaries are compatible with
this lower proof's intended mechanism.

The lower source separately defines a “true location-fluctuation
exponent” from actual endpoint variances at 3362–3373. A complete search
shows that the macros \(c_{\rm loc}\) and \(M_{\rm loc}^*\) occur only in
their declarations and this definition; they do not replace the upper
(c_F) in any later theorem. Actual variance, and especially a
conditional atom bound, cannot be substituted for the expected-side
definition merely because the names sound similar.

The absence of a third lower obstruction agrees with the dominance
section's description of \(\Lambda_2\) and \(\Lambda_3\) as auxiliary
diagnostics (2515–2518). That observation originally only removed them
from the final numerical threshold. The argument in §5 above gives a
direct reason the small non-singleton class contribution can be handled
by the tail-size margin without its claimed spatial saving.

## 8. Interpretation verdict

The intended role of the displayed small non-singleton result is to
control overlap of sparse edge patterns after averaging their locations,
then pay for the number of prefixes in a profile class. The current
definition of (c_F) is a proposed proxy for that averaging scale; it is
not already a conditional-variance definition. The surrounding proof
does not supply a hidden conditioning or initial shift that changes the
literal theorem.

For the actual small-class use, there is a valid decomposition with the
same model and numerical assumptions: exact unordered-pair counting,
followed by the existing entropy inequality at \(\theta=3\) and the
tail-size margin. It establishes the aggregate decay needed by the upper
first moment while bypassing the stronger spatial estimate. Large-block
density, relevant-block localization, and the exploration law still have
their separate proof obligations. The full reread therefore supports a
targeted repair of the proof dependency structure, not a claim that the
unchanged stronger per-block estimate has acquired a different meaning.
