# Independent pre-freeze reconstruction: exact fixed-column collision bound

This report proposes a new, separately reviewed finite inventory. It does
not edit or supersede frozen contract v1, D1–D8 or F01–F33. No Lean code
was written. The probability model below is constructed; independence,
uniformity, pair formulas, sorting, and density bounds are conclusions to
prove, not fields recording assumed estimates.

The mathematical sources used are the permitted TeX, especially 85–113,
388–392, 1516–1523, 1530–1541 and 4338–4398, and the previously read
permitted papers. The exact one-column request probability appears at
4360–4367. Its proof by finite exchangeability below does not need the
positive-pile or asymptotic hypotheses of the surrounding higher-order
factorial-moment approximation. Trusted mathlib was inspected for finite
sums, permutations, and sorting.

## 1. Recommended finite model

The direct uniform-column model is preferable to enumerating permutations.
It is exactly the law specified at TeX 388–392: uniformly choose a matrix
with the prescribed column histograms. The permutation construction is an
equivalent optional route, discussed in §6; no claim about that
implementation should be made unless its pushforward theorem is included
in the final reviewed inventory.

Use natural numbers (N,K,k). For every (j:\mathrm{Fin}\ K), the data
are (n_j:\mathrm{Fin}\ k\to\mathbb N), with

\[
 \sum_{a:\mathrm{Fin}\ k}n_j(a)=N.
\]

No pile-positivity assumption is needed. The source has (k\ge2), but the
finite proof is valid also when (k=0,1), wherever the data exist. A final
contract may retain the source's (k\ge2); it must decide this before
implementation. The natural maximal generality does not add a hypothesis.

The proposed new definitions, with exact mathematical content, are:

| ID | Proposed name and definition |
|---|---|
| CD01 | `FiniteLaw.uniform Ω`: for finite nonempty Ω, every weight is (1/(\#\Omega:\mathbb R)). Normalization and nonnegativity are proved in its constructor, using the existing `FiniteLaw` structure. |
| CD02 | `columnHistogram c a`: the cardinality of ({i:\mathrm{Fin}\ N:c(i)=a}), for (c:\mathrm{Fin}\ N\to\mathrm{Fin}\ k). |
| CD03 | `FixedColumn n`: the subtype of such (c) with `columnHistogram c a = n a` for every digit (a). Its `Fintype` instance is derived finite enumeration; its nonemptiness is proved from (\sum n=N). |
| CD04 | `reindexColumn e`: the equivalence of `FixedColumn n` given by (c\mapsto c\circ e), for (e:\operatorname{Perm}(\mathrm{Fin}\ N)), with inverse (e^{-1}). Histogram preservation is a proved dependency. |
| CD05 | `ShuffleColumns n`: the finite product (prod_{j:\mathrm{Fin}\ K}\mathrm{FixedColumn}(n_j)); `shuffleLaw n` is its uniform finite law. It has a derived nonempty instance. |
| CD06 | `wordList f`: ([f(0),\ldots,f(M-1)]) converted from `Fin k` digits to natural digits, for (f:\mathrm{Fin}\ M\to\mathrm{Fin}\ k). `labelledWord ω i` is `wordList (fun j => (ω j).val i)`. |
| CD07 | `extendRows f i`: (f(\langle i,h\rangle)) if (h:i<N), and `[]` otherwise, for (f:\mathrm{Fin}\ N\to\mathrm{List}\ \mathbb N). `labelledRows ω` uses this extension of `labelledWord ω`. Values outside (i<N) cannot enter frozen D3–D5. |
| CD08 | `sortingPerm f`: choose the permutation whose existence is proved in C22 below; its property is that (f\circ\texttt{sortingPerm}(f)) is nondecreasing in lexicographic order. `sortedRows ω` extends that reordered finite row function by CD07. The choice is justified by a theorem, not an axiom or an assumed sorting certificate. |
| CD09 | `singleFactor N n := (n:ℝ)/(N:ℝ)` and `pairFactor N n := ((n*(n-1):ℕ):ℝ)/((N*(N-1):ℕ):ℝ)`. Subtractions inside the casts are natural subtractions. Real division uses its total convention at zero; probability formulas for actual labels derive their nonzero denominators from the existence of the label(s). |
| CD10 | For (M\le K) and (x:\mathrm{Fin}\ M\to\mathrm{Fin}\ k): `prefixOne` is (prod_{t:\mathrm{Fin}\ M}\texttt{singleFactor}(N,n_{\iota(t)}(x(t)))); `prefixTwo` uses `pairFactor` instead. Here (iota:\mathrm{Fin}\ M\hookrightarrow\mathrm{Fin}\ K) is the standard initial-segment embedding. |
| CD11 | `prefixMean := (N:ℝ)*prefixOne`; `tailCollision := prod_{j:\mathrm{Fin}\ K,,M\le j.val}sum_{a:\mathrm{Fin}\ k}\texttt{pairFactor}(N,n_j(a))`; `tailIndependentCollision` uses `singleFactor²` in that sum. All empty products are one. |

The two law definitions are uniform on their actual finite sample spaces.
No additional probability theory structure, measure-valued conditioning,
asymptotic exponent, or stable-block definition is required for this
inventory. In particular `shuffleLaw` is not a generic random-rows law
with the desired collision formula supplied as an extra hypothesis.

## 2. Exact theorem inventory to review before freezing

The following is a bounded inventory of **all proposed named auxiliary
lemmas in the recommended route**. If implementation needs another named
helper, it must return to review before adding it. Elementary local `have`
proofs are allowed within these statements; their role is described here.
Proposed names are not declarations of existing Lean theorems.

General uniform-law statements require the explicit finite nonempty types
specified below. Column statements use a fixed histogram (n) with
\(\sum n=N\). Matrix statements use CD05 and the histogram conditions for
every column. Prefix statements use (M\le K) and
(x:\mathrm{Fin}\ M\to\mathrm{Fin}\ k); set (X=\texttt{wordList}(x)).

| ID | Exact statement | Proof dependencies |
|---|---|---|
| C01 `uniform_probability_card` | For finite nonempty Ω and any predicate (A), (P_{\mathrm{uniform}}(A)=\#\{\omega:A\omega\}/\#\Omega), interpreted in ℝ. | CD01, finite indicator sum. |
| C02 `uniform_expectation_reindex` | For (e:\Omega\simeq\Omega) and any real (f), (E_{\mathrm{uniform}}(f\circ e)=E_{\mathrm{uniform}}f). The event version follows using frozen F08 or an indicator. | CD01, trusted sum reindexing. |
| C03 `uniform_pi_probability` | For finite (I), finite nonempty types (C_i), and events (A_i\subseteq C_i), the uniform law on (prod_i C_i) gives (P(\forall i,A_i(\omega_i))=\prod_iP_{\mathrm{uniform}(C_i)}(A_i)). This includes (I=\varnothing). | C01, cardinality of a finite product or `Fintype.prod_sum`. |
| C04 `fixedColumn_exists` | If (\sum_a n(a)=N), then `FixedColumn n` is nonempty. | Construct `Fin N ≃ Σ a, Fin (n a)` from its proved cardinality (N); take first coordinate. Prove each fiber cardinality is (n(a)). |
| C05 `columnHistogram_reindex` | For every column (c), digit (a), and permutation (e), (#\{i:c(ei)=a}=#\{i:c(i)=a}). | Direct finite-set bijection (i\mapsto e(i)). Defines CD04. |
| C06 `fixedColumn_probability_reindex` | Under the constructed uniform law on `FixedColumn n`, (P(A(c\circ e))=P(A(c))) for every event (A) and label permutation (e). | CD04, C02. |
| C07 `column_ordered_request_card` | For every `c : FixedColumn n` and digits (a,b), the number of ordered distinct label pairs ((i,j)) with (c(i)=a,c(j)=b) is (n(a)(n(a)-1)) if (a=b), and (n(a)n(b)) if (a\ne b). | Split equality of digits. Same digit: off-diagonal of one fiber. Different digits: product of disjoint fibers. |
| C08 `perm_maps_distinct_pair` | Given (i\ne j) and (u\ne v) in `Fin N`, there is a label permutation (e) with (e(i)=u) and (e(j)=v). | Two explicit swaps, as detailed in §3. |
| C09 `column_one_label_exchangeable` | For any labels (i,u) and digit (a), (P(c(i)=a)=P(c(u)=a)). | C06 and the swap of (i,u). |
| C10 `column_two_labels_exchangeable` | For (i\ne j), (u\ne v), and digits (a,b), (P(c(i)=a\land c(j)=b)=P(c(u)=a\land c(v)=b)). | C06, C08. |
| C11 `column_one_label_probability` | For (i:\mathrm{Fin}\ N) and (a:\mathrm{Fin}\ k), (P(c(i)=a)=n(a)/N) in ℝ. No separate positivity assumption: existence of (i) implies (N>0). | Frozen F12 applied to the fiber, C09, expected constant (n(a)), then divide by (N). |
| C12 `column_two_labels_probability` | For (i\ne j), (P(c(i)=a\land c(j)=b)=r_{a,b}/(N(N-1))), where the natural numerator (r_{a,b}) is (n(a)(n(a)-1)) if (a=b), and (n(a)n(b)) otherwise. Existence of the distinct pair implies (N\ge2). | Frozen F12 on ordered distinct pairs, C07 and C10; their total cardinality is (N(N-1)). |
| C13 `column_two_labels_equal_probability` | For (i\ne j), (P(c(i)=c(j))=\sum_a\texttt{pairFactor}(N,n(a))). | C12; disjoint union over the common digit, or F12 with the finite set of common digits. |
| C14 `wordList_eq_iff` | For (f,g:\mathrm{Fin}\ K\to\mathrm{Fin}\ k), `wordList f = wordList g` iff (\forall j,f(j)=g(j)). | List `ofFn`/index equality and injectivity of `Fin.val`; (K=0) included. |
| C15 `wordList_prefix_iff` | For (M\le K), `wordList x` prefixes `wordList f` iff (\forall t:\mathrm{Fin}\ M,f(\iota(t))=x(t)). | Fixed list lengths, initial-segment indexing; (M=0) and (M=K) included. |
| C16 `labelled_prefix_probability` | For any label (i:\mathrm{Fin}\ N), (P(X\preceq\mathrm{labelledWord}(\omega,i))=\texttt{prefixOne}). | C03, C11, C15, with unrestricted tail coordinates. |
| C17 `labelled_pair_collision_probability` | For distinct labels (i,j), (P(\mathrm{labelledWord}(\omega,i)=\mathrm{labelledWord}(\omega,j)\land X\preceq\mathrm{labelledWord}(\omega,i))=\texttt{prefixTwo}\cdot\texttt{tailCollision}). | Split the coordinate event into prescribed matching prefix digits and equal tail digits, then C03, C12, C13, C14–C15. |
| C18 `expected_labelled_occupancy` | (E[\mathrm{occupancyCount}(N,\mathrm{labelledRows}(\omega),X)]=\texttt{prefixMean}), all (N). | Frozen F12, C16; explicit empty-label case if (N=0). |
| C19 `expected_labelled_collisionPairs` | (E[\#\mathrm{collisionPairs}(N,\mathrm{labelledRows}(\omega),X)]={N\choose2}\,\texttt{prefixTwo}\,\texttt{tailCollision}), all (N), with the coefficient cast to ℝ. | Frozen F12, C17, and the cardinality of ({(i,j):i<j<N}). For (N<2), both sides are zero. |
| C20 `pairFactor_le_singleFactor_sq` | For naturals (0\le n\le N), (0\le\texttt{pairFactor}(N,n)\le\texttt{singleFactor}(N,n)^2). | Split (N=0), (N=1), (N\ge2); in the last case clear positive denominators and use (n\le N). All casts/subtractions are explicit. |
| C21 `tailCollision_le_independentCollision` | (0\le\texttt{tailCollision}\le\texttt{tailIndependentCollision}). | C20 and nonnegative finite sum/product monotonicity. No lower bound on the factors. |
| C22 `exists_sortingPerm` | For every (f:\mathrm{Fin}\ N\to\mathrm{List}\ \mathbb N), there exists (e:\operatorname{Perm}(\mathrm{Fin}\ N)) such that (f\circ e) is monotone in the usual lexicographic list order. | Sort the distinct label list and recover its permutation; see §4. Defines CD08. |
| C23 `sortedRows_monotone` | For (i\le j<N), `sortedRows ω i ≤ sortedRows ω j` in lexicographic order. | C22 and CD08. This proves that the deck supplied to frozen D4 is the source's sorted deck. |
| C24 `occupied_card_reindex` | For every (f:\mathrm{Fin}\ N\to\mathrm{List}\ \mathbb N), permutation (e), and list (X), the frozen occupied cardinality for `extendRows (f ∘ e)` equals that for `extendRows f`. | Finite-set bijection of occupied positions. |
| C25 `collisionPairs_card_reindex` | In the same domain, the frozen collision-pair cardinalities for `extendRows (f ∘ e)` and `extendRows f` are equal. | Reindex unordered label pairs, orienting them by minimum/maximum; all order cases explicit. |
| C26 `expected_sorted_counts` | For `sortedRows`, expected occupancy is `prefixMean`, and expected collision-pair count is the exact expression in C19. | C18–C19 and pointwise C24–C25 with the sample-dependent sorting permutation. |
| C27 `internal_density_le_sq_expected_edges` | For every existing finite law (w), (N), random natural-list rows (R), and list (X), the existing `edgeDensity w N R X` is at most ((E_w[\mathrm{edgeCount}(N,R,X)])^2). | Frozen F04/F12/F15 and trusted `Finset.sum_sq_le_sq_sum_of_nonneg`. No model assumptions. |
| C28 `shuffle_expected_internal_edges_le` | (E_{\mathrm{shuffleLaw}}[\mathrm{edgeCount}(N,\mathrm{sortedRows},X)]\le\texttt{prefixMean}^2\,\texttt{tailCollision}/2), all (N). | Frozen F24, C26, C20 and ({N\choose2}\le N^2/2). Nonnegativity is proved locally. |
| C29 `shuffle_internal_density_le` | (\mathrm{edgeDensity}(\mathrm{shuffleLaw},N,\mathrm{sortedRows},X)\le\texttt{prefixMean}^4\,\texttt{tailCollision}^2/4), all (N). | C27, C28 and nonnegativity, then ring arithmetic. |

C26 may be split into two named lemmas in the final inventory rather than
one conjunction, and CD08 may name its label-list implementation instead
of using choice. That organizational decision must be made at the review
stage. It does not change the required mathematical conclusions.

## 3. Finite exchangeability proofs: no factorial enumeration

C04 can be proved even for empty populations. The type
\(\Sigma_{a:\mathrm{Fin}\ k}\mathrm{Fin}(n(a))\) has cardinality
\(\sum_an(a)=N\). A cardinality equivalence with `Fin N` assigns each
position its digit (a). For fixed (a), the corresponding fiber is in
bijection with `Fin (n a)`. This proves the histogram and nonemptiness;
it does not assume an assignment with those counts.

For C08, let (s_1=\operatorname{swap}(i,u)), and put (z=s_1(j)).
Injectivity and (i\ne j) imply (z\ne u). Let

\[
 e=\operatorname{swap}(z,v)\circ s_1.
\]

The second swap fixes (u), since (z\ne u) and (v\ne u), so
(e(i)=u), while (e(j)=v). This includes (i=u), (z=v), and all
overlaps between the source and target label pairs. The swaps may be the
identity; no four-distinct-label condition is needed.

For C11, all (N) label probabilities have a common value (p) by
reindexing. Their sum is exactly (n(a)), since each column has exactly
that many occurrences of (a). Thus (Np=n(a)). For C12, the same
argument on the (N(N-1)) ordered distinct pairs gives

\[
 N(N-1)p_{a,b}=
 \begin{cases}
 n(a)(n(a)-1),&a=b,\\
 n(a)n(b),&a\ne b.
 \end{cases}
\]

The normalization arises from deterministic counts plus symmetry. It is
not an independence claim about two different rows. Indeed the
without-replacement correction is exactly the (n(a)-1) factor.

The proof of C03 can count product events as the product of their fiber
cardinalities, dividing by the product of sample-space cardinalities.
Alternatively, expand an indicator of (\forall j,A_j) as a product of
zero-one indicators and use `Fintype.prod_sum`. Both are exact even when
a coordinate event is empty or the coordinate index set is empty.

## 4. Sorting bridge without losing label identities

Sorting the list of row words directly creates duplicate values, which
makes reconstructing their original labels inconvenient. Instead start
with the distinct list `List.finRange N` and merge-sort it using the
relation

\[
 i\preceq_f j\quad\Longleftrightarrow\quad f(i)\le_{\rm lex}f(j).
\]

This relation is total and transitive. It need not be antisymmetric on
labels: different labels may carry identical words. **Use `List.mergeSort`,
not `Finset.sort` with this relation alone.** The inspected `Finset.sort`
interface requires antisymmetry; the merge-sort correctness theorem only
requires totality and transitivity. The sorted label list is a permutation
of `finRange N`, hence has length (N), is duplicate-free, and contains
every label. Its indexing function is therefore a permutation of `Fin N`.
By its sortedness property, the corresponding row-word list is
lexicographically sorted. No tie-breaking assumption is required.

For C25, take a pair ((i,j)) with (i<j), and map it under (e) to

\[
 (\min(e(i),e(j)),\max(e(i),e(j))).
\]

The images are distinct because (e) is injective. Equal row words make
the prefix condition valid at either endpoint, using frozen F19. Apply
the same construction with (e^{-1}) for the inverse. The verification
splits explicitly according to (e(i)<e(j)) or (e(j)<e(i)), and likewise
for the inverse orientation. The (N=0,1) cases are empty but do not
require a separate permutation-existence assumption.

Crucially, C25 holds for **every** permutation pointwise. In the shuffle
application, the sorting permutation depends on the entire matrix. No
claim that it is independently random, uniform, or independent of the
rows is needed. We calculate collision probabilities on original labels,
then transfer only the collision-pair cardinality to the sorted deck.
The source edge positions themselves stay the sorted positions.

## 5. Exact end-to-end calculation and degeneracies

For (i\ne j), the event that the two original rows are equal and extend
(x) is the intersection, over columns, of:

- at (t<M): both entries equal the specified digit (x(t));
- at (t\ge M): the entries equal one another, with their common digit
  unrestricted.

C03 and C12–C13 give its exact probability

\[
 a_xq_x,\qquad
 a_x=\prod_{t<M}\frac{n_t(x(t))(n_t(x(t))-1)}{N(N-1)},\qquad
 q_x=\prod_{t\ge M}\sum_a\frac{n_t(a)(n_t(a)-1)}{N(N-1)}.
\]

Summing over the ({N\choose2}) unordered original label pairs proves
C19. The sorting bridge and frozen F21/F24 then give

\[
 \mathbb E e_x\le {N\choose2}a_xq_x
 \le\frac{\mu_x^2q_x}{2},\qquad
 \mu_x=N\prod_{t<M}\frac{n_t(x(t))}{N}.
\]

For each fixed edge location (m), put (p_m=P(m\in\mathrm{internalEdges})).
Since all (p_m\ge0), C27 and C28 yield

\[
 \sum_m p_m^2\le\Big(\sum_m p_m\Big)^2
   =(\mathbb E e_x)^2\le\frac{\mu_x^4q_x^2}{4}.
\]

The following cases must stay explicit in the final contract and proofs:

- **(N=0):** no labels and no edges; all histograms are zero. Uniform
  column spaces remain inhabited. C11 is vacuous. The main bound is
  (0\le0).
- **(N=1):** no distinct label pairs and no edges. C12/C13 are vacuous;
  the main inequality is immediate. Do not cancel (N-1).
- **(K=0):** the matrix product has one element; every row is the empty
  word. If (M\le K), then (M=0). The empty products are one,
  (mu_x=N), collision-pair count is ({N\choose2}), and edge count is
  (N-1) with natural subtraction.
- **(M=0):** the prefix is empty, and `prefixOne = prefixTwo = 1`.
- **(M=K):** the tail product is one. The calculation is the exact
  second-factorial bound for one full word.
- **Zero requested pile:** the event is impossible. When an actual label
  exists, its one-label factor is zero; when distinct labels exist, the
  corresponding pair factor is zero. No legal-prefix positivity is
  necessary for these finite formulas.
- **Requested pile of size one:** two distinct labels cannot both carry
  that prescribed digit; the pair factor is zero.
- **Zero tail coincidence factor:** no distinct row pair can match the
  whole tail; the expected collision and edge counts are zero. Never
  divide by (q_x).
- **Repeated words and ties in sorting:** handled by sorting labels, then
  forgetting labels only in the row-word list.

No (o(1)), good-event loss, conditioning on an ambient block, or
endpoint anti-concentration appears. Translating (mu_x,q_x) into the
source exponents, or transporting this law through exploration
conditioning, is a later obligation and is not part of C01–C29.

## 6. Alternative decompositions if enumeration becomes cumbersome

The recommended route already avoids the two largest enumerations:
there is no calculation of (N!/\prod_a n(a)!), and no enumeration of
all sorted row-word lists. Finite cardinality, exchangeability, and a
label-sorting permutation suffice.

If an explicit **uniform-permutation sampling representation** is
required, it can be added as a separately reviewed optional inventory:

1. `fixedColumn_reindex_transitive`: for (c,d:\mathrm{FixedColumn}(n)),
   there exists (e:\operatorname{Perm}(\mathrm{Fin}\ N)) with
   (c\circ e=d). For each digit, equal-size fibers are equivalent;
   combine those equivalences with `Equiv.ofFiberEquiv`.
2. `uniform_permutation_column_assignment`: for deterministic
   (c:\mathrm{FixedColumn}(n)), uniformly random label permutation
   (sigma), and every (d:\mathrm{FixedColumn}(n)),
   (P(c\circ\sigma=d)=1/\#\mathrm{FixedColumn}(n)).
   Right-composition bijects the permutation fibers for any two outputs;
   all output probabilities are equal and sum to one. No factorial
   counts are needed.
3. `uniform_permutation_matrix_assignment`: independent uniform
   permutations, one per deterministic column, give every admissible
   matrix atom the product of the single-column atom probabilities;
   this equals the direct uniform `ShuffleColumns` weight. This follows
   from the generic product-law theorem C03.

These optional statements prove that representation rather than assuming
it. They are not prerequisites of the direct source-law route and should
not be silently counted as implemented if omitted from the final freeze.

If the sorting permutation construction is cumbersome, a second valid
route is to prove that collision-pair cardinality depends only on the
multiset of rows, using the sum of ({z_w\choose2}) over full words.
Then trusted `List.mergeSort_perm` transfers the multiset. That route
needs additional reviewed definitions and theorems for word occupancies
and the sum-of-binomial-coefficients identity, so the label-permutation
route appears smaller.

## 7. Trusted library ingredients checked

The following actual mathlib interfaces were located, without writing or
compiling project Lean code:

- `Fintype.equivOfCardEq`, `Fintype.card_pi`, finite sigma cardinality,
  and `Equiv.ofFiberEquiv` for finite histogram realizations and optional
  fiber equivalences.
- `Equiv.swap_apply_left`, `Equiv.swap_apply_right`, and
  `Equiv.swap_apply_of_ne_of_ne` for the explicit two-swap construction.
- `Fintype.prod_sum` in
  `Mathlib/Algebra/BigOperators/Ring/Finset.lean` for product-law
  factorization.
- `Finset.offDiag_card` and finite fiber/product cardinality formulas for
  ordered distinct requests.
- `List.mergeSort_perm` and `List.sorted_mergeSort'` in the list sorting
  interface. `Mathlib/Data/List/Lex.lean` supplies the list lexicographic
  linear order. `Equiv.Perm.ofFn_comp_perm` is available if a list-level
  reindexing bridge is convenient.
- `Finset.sum_sq_le_sq_sum_of_nonneg` in
  `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean` for C27.
- Frozen F12, F19, F21, and F24 already provide the expectation-of-count,
  prefix-transfer, and edge-to-collision components; their statements
  are preserved exactly.

The mathematical route is complete at the finite level. Implementation
should begin only after the root comparison chooses and freezes the
exact names, model definitions, prefix indexing, sorting representation,
and optional permutation representation. No missing concentration result
is needed to prove the final (mu_x^4q_x^2/4) inequality.

## 8. Cross-comparison verdict on the exact statement inventory

After finishing the independent reconstruction above, I read the complete
`collision_contract_statements.md` and compared **every C.D01–C.D14 and
every C.01–C.57, including both C.20a and C.20b**, against the finite
argument, the source model, and all empty and degenerate cases.

**Verdict: accept the complete core inventory. No mathematical correction
or additional assumption is required before its additive freeze.** Adopt
the statement report's names and representations in place of this
report's preliminary proposed names. In particular I accept its direct
`FixedColumn` and product `matrixLaw`, its general two-digit `pairFactor`,
and its concrete merge-sorted label list. None of this changes v1.

The exact definition comparison is:

| Accepted definitions | Comparison and case check |
|---|---|
| C.D01 | The uniform finite law exists on the stated finite nonempty domain; C.06 derives that condition in every column use. |
| C.D02 | A product of already normalized finite laws needs no extra nonempty-fiber assumption. Its normalization follows from the product-of-sums identity, including the empty coordinate type. |
| C.D03–C.D05 | Prescribed histograms, permutation reindexing, and the derived uniform column law match the source. Histogram invariance is proved by C.08. C.06 includes empty alphabets and populations. |
| C.D06 | The actual sample space is the finite family of prescribed columns, with constructed product weights. C.17 proves uniformity over matrices; no permutation-pushforward claim is being assumed. |
| C.D07–C.D08 | List words and natural-index adapters preserve frozen D2–D5. Values outside the deck cannot enter their count sets. Both adapter branches are covered by C.20a and C.20b. |
| C.D09–C.D11 | Merge-sort of distinct labels handles repeated words correctly. Its indexing equivalence is justified by length, duplicate-freeness and exhaustive membership. Only pointwise count invariance is subsequently used. |
| C.D12 | The general same/different-digit numerator is the exact ordered two-label count. Natural subtraction before casting correctly handles zero piles and populations of size at most one. |
| C.D13–C.D14 | The prefix embedding and suffix index set are disjoint and exhaustive when M≤K. Empty products are one. Equality of the defined mean to expected occupancy is subsequently proved. |

The statement-by-statement comparison is grouped only where the proofs
use the same finite mechanism. Every identifier in each row is accepted.

| Accepted statements | Mathematical verification |
|---|---|
| C.01, C.02 | Constant uniform weights give normalized event cardinalities and invariance under finite equivalences. |
| C.03, C.04 | Product indicators factor under the constructed product weights. Use the true event off a chosen coordinate subset; empty index sets give one. |
| C.05 | Its hypothesis says at most one index is active at each sample, so the union indicator equals the finite sum of individual indicators. Empty index types are included. |
| C.06, C.07, C.08 | A finite sigma-type cardinality equivalence realizes the histogram; every pile is bounded by the total; label permutations preserve every fiber count. |
| C.09, C.10 | There are N(N−1) ordered distinct labels. A same-digit fiber has n(a)(n(a)−1) ordered distinct pairs; different digit fibers are disjoint and have n(a)n(b) product pairs. |
| C.11, C.12 | The two-swap construction maps any distinct ordered pair to any other, including overlapping source and target labels. Reindexing preserves the actual uniform column law. |
| C.13, C.14 | Summing exchangeable one-label or distinct-pair events gives exact deterministic counts. A label proves N>0; a distinct pair proves N≥2. Every division used in deriving a probability therefore has a proved nonzero denominator. |
| C.15, C.16 | Common digits form disjoint alternatives, and a zero histogram fiber contains no label. No zero-count digit is discarded from the quantified domain. |
| C.17 | Product cardinality identifies product reciprocal column-space sizes with reciprocal matrix-space size, proving the source's uniform-matrix law. |
| C.18, C.19 | The `List.ofFn` lengths equal the finite coordinate counts. |
| C.20a, C.20b | The bounded adapter branch recovers its given label by proof irrelevance; the outside branch is the specified empty-list default. |
| C.21, C.22 | Fixed-length list prefix and equality are exactly the stated coordinate conditions; empty and full prefixes are included. |
| C.23 | Any list whose entries are below k has the required `Fin k` encoding. It makes no claim about out-of-alphabet lists or positive pile sizes. |
| C.24, C.25, C.26 | Merge-sort preserves the label list as a permutation, hence preserves length, duplicate-freeness and complete membership. The stated declaration order proves these properties before constructing the indexing permutation. |
| C.27 | Totality and transitivity of row comparison suffice for merge-sort; antisymmetry on labels is neither required nor claimed. |
| C.28, C.29 | Occupied labels are bijected under reindexing. Collision pairs are bijected after orienting each image by minimum and maximum; equal rows transfer the prefix condition if orientation reverses. |
| C.30, C.31 | Apply the deterministic cardinality identities to the sample-dependent sorting permutation. This does not assert adjacency or edge-location invariance. |
| C.32, C.33 | These concern original labels. Prefix events factor into prescribed one-label events; collision-and-prefix events factor into prescribed two-label prefix events and equal-digit tail events. |
| C.34, C.35 | Sum one-label indicators, then transport occupancy through sorting. The result is the defined prefixMean, including N=0. |
| C.36, C.37 | Frozen collision pairs lie among increasing pairs below N, and that index set has Nat.choose N 2 elements, including N=0,1. |
| C.38, C.39 | Sum the constant collision probability over increasing pairs. For N<2 the index set and binomial coefficient are zero, so no distinct-label formula is invoked. Sorting transfers the count pointwise. |
| C.40, C.41 | All real factors are nonnegative, since all numerators and denominators are casts of nonnegative naturals. Total division at zero remains nonnegative in both pair-factor branches. |
| C.42 | With N≥2, clearing positive denominators reduces the same-digit factor comparison to n(a)≤N. Splitting zero, one and larger pile sizes validates the natural-subtraction casts. |
| C.43, C.44 | Finite sums and products preserve nonnegativity. Empty products are one. Arbitrary M is harmless for the tail index set. |
| C.45, C.46 | Nonnegative finite sum/product monotonicity applies to C.42. The helper domain N≥2 suffices because the final all-size theorems explicitly split smaller populations. |
| C.47 | Nonnegative edge probabilities satisfy Σp²≤(Σp)²=(E e)². No independence, sorting or matrix assumption is needed. |
| C.48, C.49 | Zero or one position has no increasing pair; these follow directly from frozen collisionPairs. |
| C.50 | For N≥2, the exact coefficient after the pair-factor comparison is (N−1)/(2N): choose(N,2)·p²=((N−1)/(2N))·(Np)². For N=0,1 both sides are zero with the specified casts and total division. |
| C.51, C.52 | The nonnegative tight coefficient is at most 1/2; frozen F24 then passes from expected collision pairs to expected internal edges. N=0 is handled explicitly. |
| C.53, C.54 | All sides of the squared comparisons are nonnegative. C.53 retains the exact collision-factor square; C.54 gives μ⁴q²/4. Neither introduces a spatial cF factor. |
| C.55 | Frozen F23 plus exact expected occupancy bounds density by prefixMean for every prefix, including terminal ones. |
| C.56, C.57 | The full-length suffix set and zero-length prefix index type are empty, so the products are one and the empty prefix list is empty. |

These declarations construct and analyze the actual fixed-column matrix
law at source lines 388–392. The two-label formulas agree with the exact
two-request specialization of lines 4360–4373, without importing the later
asymptotic approximation or its large-pile hypotheses. Frozen F21/F24
supply the internal-edge comparison used at 1516–1523. The result is the
new finite collision bound, not the unsupported spatial cF estimate.

No remaining **mathematical** pre-freeze issue was found in the core.
Implementation checks concern type inference, finite enumeration,
natural-to-real casts and the concrete indexing equivalence. They must be
resolved by proofs within the reviewed signatures; they do not justify
adding assumptions or unreviewed named lemmas after freezing.

### Separate optional occupancy-slice review

I also mathematically checked O.D01–O.D02 and O.01–O.07. Their coordinate
split, expectation factorization, fixed-prefix-array collision formula,
and division-free occupancy-slice identities are valid, including null
slices and q>N. In O.05 the selected prefix label set is a subset of the
original N labels; the tail law stays on all N labels. This distinction
is preserved correctly. O.06–O.07 make no claim about arbitrary
exploration conditioning.

I accept that optional inventory mathematically **if it is explicitly
selected and included in the additive freeze after all required reviews**.
It remains outside the core by the statement report's own scope
declaration. This acceptance does not authorize implementing it unless it
is selected and frozen.

Final signature review: I also read the stable sections 8–9 of the
statement report. I accept the exact argument order, explicit population
N in numeric factors, `rawRow/rawRows/sortedRows n ω`, removal of unused
`hn` from purely algebraic and empty-product statements, module allocation,
and exclusion of the optional O inventory from this freeze. The selected
core C.D01–C.D14 and C.01–C.57 (including C.20a/C.20b) is accepted for
additive freezing with no remaining mathematical or signature issue. No
Lean implementation has been written during this review.
