# Independent reconstruction of the expectation interface

Reviewed source material: `time_inhomogeneous_riffle_shuffle_unified_article.tex`, especially the shuffle-matrix definition, the detailed ambient-block and side-piece definitions, and the labelled-row thinning paragraph; `2510.22783v1.pdf`, Section 2.2 (via its permitted derived text); and `2103.05068v3.pdf`, its shuffle-string construction and interval interpretation (via its permitted derived text). This report compares every P01–P08 item in `EXPECTATION_EXTENSION_DRAFT.md`. No implementation was performed during this review.

## Source reconstruction and model distinction

The unified article explicitly samples uniformly among all labelled N-by-K matrices with the prescribed count of each digit in each column. Section 2.2 of 2510 gives exactly this law, and then sorts the resulting row multiset. The later labelled-row paragraph of the unified article explicitly keeps the original row labels during thinning and distinguishes those labels from sorted positions. The older 2103 paper's independent row-string representation belongs to its multinomial-pile model and cannot be transferred as a row-independence premise to fixed column counts.

For a fixed column j, let Omega_j be the finite set of assignments of digits to the N labelled rows having the prescribed counts. There is a literal bijection between the source matrices and the finite product `Pi j, Omega_j`. Therefore uniform measure on that product is the source law. Factorization over columns follows from finite counting. It is not an independent scientific premise. By contrast, different labelled rows within one column are usually dependent.

The source ambient word is fixed when an expectation is taken. The associated random count is the number of global row labels whose words extend that fixed prefix. Accordingly its expected size is `N * product(prefix probabilities)`. A side piece adds the earlier extension digits and one left/right digit condition to this same global row predicate. This produces exactly the frozen `sideMass`. This is an unconditional expectation of a restricted row count, not a conditional expectation given the realized ambient size or the exploration sigma-field.

## P01 — Approved

Construct a column assignment using an equivalence between `Fin N` and the disjoint union over digits l of `Fin (cuts.count j l)`. Their finite cardinalities agree by `cuts.sum_count`. Projection to the digit coordinate has exactly the prescribed fiber cardinalities. This constructs nonemptiness from the existing data, without a canonical-array assumption, a feasibility field, or an additional axiom.

The construction covers N=0: every prescribed count must be zero, and the empty row assignment exists. It also covers empty column families. If k=0 and there is a column, the cuts equation forces N=0; when K=0 the product sample space is a singleton even if N is positive. Thus the statement for arbitrary natural k,N,K is consistent, including these degenerate cases.

Each sample's column-count assertion is part of the assignment subtype. If a row displays digit l, that fiber contains the row and hence the prescribed count is positive. For N>0 this gives positive normalized probability and the existing legality of every observed row prefix. The discrete finite measurable space makes every real function measurable and integrable, and uniform PMF gives an actual probability measure with arithmetic-average integral formula. These facts must be proved from finiteness and nonemptiness, as the draft requires.

Dependencies: only finite assignment/cardinality construction and trusted finite probability integration. Classification: finite and probabilistic, with measure-theoretic bookkeeping confined to a finite discrete space.

## P02 — Approved

Precomposition with a permutation of `Fin N` gives an equivalence of the fixed-count assignment type. It preserves each digit-fiber cardinality by bijectivity, and reindexes the uniform finite sum. Consequently the expectation of g at a labelled row is the same for every row.

For each sample assignment a, the exact counting identity is

    sum_i g(a_i) = sum_l cuts.count(j,l) * g(l).

Taking uniform averages and using exchangeability makes the left side N times the common single-row expectation. Dividing by N>0 yields the stated probability-weighted sum. This works for arbitrary real g, including signed functions; the sample space is finite. Indicator g gives the digit-event probability. The full-matrix version follows by summing the other column coordinates, or from P03 with every other factor equal to one.

The N>0 restriction is exactly the normalized-profile domain. No sorted-row assertion is made. For example, with N=2 and column counts (1,1), the first sorted digit is always zero, whereas a fixed labelled row has digit zero with probability one half. Distinct row indicators are negatively dependent in this same example. These observations confirm the importance of the draft's stated exclusions; they do not require a correction.

Dependencies: P01 plus finite permutation reindexing; full-matrix marginal may use P03. Classification: finite/probabilistic.

## P03 — Approved

The arithmetic-average proof is the finite product-of-sums identity

    sum_(omega in Pi j Omega_j) product_j F_j(omega_j)
      = product_j sum_(a in Omega_j) F_j(a),

divided by

    card(Pi j Omega_j) = product_j card(Omega_j).

Every denominator is nonzero because P01 proved nonemptiness. All integrability obligations follow from the finite discrete spaces. For K=0, both products equal one, and the unique empty matrix gives expectation one. Signed functions cause no problem.

Correct one-column marginal laws alone would not suffice: two identically coupled random balanced columns have the right individual marginals but a different two-column word probability. The source's concrete product sample space, rather than a marginal-only replacement law, supplies the needed joint distribution. The proposed proof uses that exact space and is faithful.

Dependencies: P01 and finite product-of-sums only. In particular it need not depend on P02, so the stated implementation order is acyclic. Classification: finite/probabilistic.

## P04 — Approved

For a fixed labelled row i, the box event indicator is the product over columns of the indicators that the displayed digit belongs to A_j. P03 factors its expectation across columns; P02 evaluates each factor as `sum_(l in A_j) prob(p_j,l)`. The count of rows in the box is the sum of these row indicators. Linearity of expectation, not independence between rows, now gives the factor N.

All edge cases are included: an empty allowed digit set makes the relevant factor and box count zero; zero piles contribute zero; an empty column family imposes no conditions, so every row is counted and the empty product is one. Impossible boxes therefore satisfy the formula without a legality premise.

Dependencies: P01–P03 and finite linearity. Classification: finite/probabilistic.

## P05 — Approved

Choose the allowed digit set in column j to be the singleton `{x_j}` when j.val<M and the full digit set otherwise. The later-column factors are one by the simplex sum. P04 reduces exactly to `N * product_(j in positions(0,M)) prob(p_j,x_j)`, which is the unchanged `prefixMass`. The ordered source domain M<=K is preserved even though the finite counting identity could be stated more generally. No legality assumption is needed for the mass equality; a zero factor means that no sampled row satisfies the prefix.

For the logarithmic statement, use the same N>=2, w<=M<=K and legality at M as in the existing exact cL identity. Prefix legality implies positivity of both expected counts. Substitute the mass equalities into that identity to get

    log(E prefixCount_M)/log N
      = cL(b,w,M) + (log(E prefixCount_w)/log N - b).

The term b is arbitrary. There is no reason to introduce b>=0 or to replace the actual ambient discrepancy by an equality to b.

Dependencies: P04 and existing D04 for the logarithmic corollary. Classification: finite/probabilistic, plus elementary real logarithm identities.

## P06 — Approved

For the left side at column j, use singleton allowed sets before j, the digit set `{l | l<x_j}` at j, and the full digit set afterwards. P04 yields

    N * product_(h<j) p_h(x_h) * sum_(l<x_j) p_j(l).

When w<=j.val, split the prefix product exactly into h<w and w<=h<j. The resulting expression is the frozen `sideMass N p x w leftProbability j`. The right side is identical with the strict inequality reversed. No legality or side-positivity condition is needed, including when one of the factors is zero. Later digits are unrestricted, precisely as the source side-piece definition requires.

The distinction from conditional expectation is substantive. With N=2, three columns each having counts (1,1), the ambient prefix 00 has expected size one half. Its side piece adding a third digit 0 has unconditional expected size one quarter. Conditional on the ambient prefix having realized size one, the expected side count is one half. P06 asserts the former, which matches `prefixMass` and the source's fixed-prefix deterministic expected-size exponent. It does not establish the separate conditioning-transfer lemma for random explored ambient blocks.

The source presents side pieces as families of legal prefixes of a longer length. Unrestricted later columns in the row predicate give the same realized row count: P01 guarantees that every observed row uses only positive-count digits. No extra constraint or factor from the later digits should appear.

Dependencies: P04 and the finite product split already used in the ambient layer. Classification: finite/probabilistic.

## P07 — Approved

For each column in `positions(w,v)`, its index is at least w, so P06 identifies its expected side cardinality with the existing side mass. Pointwise equality through the same finite supremum proves equality of side maxima. The same nonnegative-real coercion, square root, `logExponent`, and minimum then give literal equality with the existing WithBot-valued cF.

Empty position sets give maximum zero. Zero side expectations remain zero. Thus the bottom-valued and v=w cases require no positivity assumption and must not be excluded. The stated N>=2 domain is appropriate for the logarithmic normalization.

This is the square root of a maximum of expected side counts. It is neither an expected random maximum nor the expectation of a random logarithm. The independent first-column anti-concentration counterexample remains unaffected: deterministic positive side counts have positive expected mass but no random fluctuation. The draft correctly makes only the deterministic identity.

Dependencies: P06 and existing side maximum/cF definitions. Classification: finite/probabilistic plus real square-root/logarithm expressions; no concentration theorem.

## P08 — Approved

For a fixed sample and any permutation sigma of its labelled rows, the map i -> sigma(i) is a bijection between the two row-index sets satisfying a predicate on complete row words. Their finite cardinalities agree. This argument holds pointwise in the sample, so sigma may be chosen as an arbitrary function of that sample. Discrete finiteness supplies measurability for taking expectations afterward.

Applying the invariant predicate to a prefix, a left side piece, or a right side piece preserves the counted size. The P05/P06 identities therefore remain valid after a sorting permutation. This does not say that the sorted matrix has uniform law, that sorted rows have the P02 marginal, or that a sample-dependent reindexing preserves the full source measure. Only the counted cardinality is invariant. No ordering, graph-adjacency or endpoint localization theorem is hidden in this conclusion.

Dependencies: finite permutation/cardinality invariance; P05/P06 for the expectation corollaries. Classification: finite; probabilistic corollaries follow by equality of random variables.

## Final verdict and remaining obligations

Every definition and every P01–P08 item in the current draft is approved for freezing, with no required correction. The N>0 restriction on normalized profile and expectation statements, and N>=2 on logarithmic corollaries, are correctly placed. The finite nonemptiness, normalization, integrability and product-law facts are all mathematical conclusions to prove, not fields to assume.

The dependency graph is P01 -> column P02 and P03; column P02 plus P03 -> full-matrix P02 and P04; P04 -> P05/P06; P06 -> P07; finite permutation invariance plus P05/P06 -> P08. All are exact finite statements. There is no asymptotic error to quantify in this interface and no time-profile regularity or time measurability premise.

Proving this inventory will close the deterministic product-mass-to-unconditional-expectation bridge for the assigned cL and cF definitions. It will not close conditional exploration preservation, concentration or anti-concentration, the construction/truncation of stable boundary families, or the separate lower-bound profile-counting issues. In particular, it must not be cited as repairing the known false anti-concentration consequence merely because the expected-size interpretation of cF has become formal.

## Post-freeze P02–P04 implementation and audit

After the three independent approvals and the separate freeze of `EXPECTATION_CONTRACT.md`, I implemented P02–P04 in `RiffleTimeProfile/FixedCountMoments.lean`, importing the concrete P01 law from `FixedCountModel.lean`. It contains the row-permutation equivalence, invariance of finite uniform integrals, the exact labelled-row marginal on a column and on the full matrix, explicit real probabilities of individual digit events, arbitrary real column-product factorization, and `expected_box_count` with the agreed exact integral formula.

The column marginal proof uses exchangeability and the exact sum over labelled rows, then divides by the existing N>0 premise. The product factorization expands the actual uniform law as an arithmetic average and applies the finite product-of-sums/cardinality identities. The box count is a sum of row indicators; each row indicator is a product across columns. Thus the proof uses linearity over rows and factorization over columns, without an independent-rows assertion or any assumed expectation identity.

During elaboration, two equivalent finite decision procedures caused a type-matching failure for the box-count indicator identity. As required, I requested alternative finite abstractions from both the Lean-design and adversarial agents before resolving it. The final proof uses explicit equality between the two filtered finite sets and a pointwise Boolean-product identity. No hypothesis, law, definition, or frozen statement changed.

Both `FixedCountMoments.lean` and `FixedCountMomentsAudit.lean` compile without warnings. Its ten public theorems and the row-reindexing equivalence depend only on `[propext, Classical.choice, Quot.sound]`. The complete audit output is saved in `reviews/fixed_count_moments_axiom_audit.txt`. The dependent `ExpectedMass.lean` implementation has also successfully compiled against the published `expected_box_count` API, as reported by its independent owner.
