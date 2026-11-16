# Comparison before the additive collision freeze

The root compared the three independent reports `collision_contract_reconstruction.md`, `collision_contract_statements.md`, and `collision_contract_assumptions.md`. Each author had independently read the permitted proof sketch, including the preceding full-file reread. All three then reviewed the complete proposed inventory C.D01–C.D14 and C.01–C.57, with C.20 represented by two declarations C.20a and C.20b.

The selected inventory is the core in the statement-design report. The optional occupancy-conditioning inventory O.D01–O.D02/O.01–O.07 is not selected. It remains an outstanding proof obligation rather than an assumed conditional-law interface.

| Item | Independent comparison | Decision |
|---|---|---|
| Finite probability model | Both mathematical reviewers accept uniform sampling from the actual subtype of fixed-count columns, followed by a product of column laws. | Construct normalization, nonemptiness, and independence; no probabilistic fields or additional sampling assumptions. |
| Label marginals and pair requests | Reconstruction derives the formulas by row-permutation exchangeability and exact histogram counting. Hidden-case review checks zero and unit piles and distinct row labels. | Adopt the general two-digit C.14 and derive same-digit coincidence. The existence of distinct labels supplies the positive denominator. |
| Prefix representation | All reports require exact correspondence with list prefixes. | Use finite vectors with M ≤ K for matrix-prefix statements. C.23 itself also encodes overlong in-alphabet lists; it is the later application that needs the length bound. |
| Sorting | All reviewers accept sorting original labels rather than treating equal words as distinct values. | Construct the permutation using mergeSort and its proved length, membership, and absence of duplicate labels. |
| Reindexing counts | Both count proofs are pointwise under arbitrary row permutations. | Orient image pairs explicitly, retaining the factor of two. Do not assert edge-position or density invariance. |
| Exact expected collision count | All reports obtain choose(N,2) times prescribed-prefix pair factors times tail coincidence. | Prove the equality for all N with empty and one-row cases handled before any cancellation. |
| Arithmetic comparison | All reports derive pair factors ≤ squared one-row proportions from the given counts. | Use the reviewed N ≥ 2 helper only inside that branch; final bounds include all N. |
| Density bound | All reports obtain the square-of-expected-edge bound and then μ⁴q²/4. | Prove it as a new exact consequence, without changing any existing theorem or claiming the printed −cF factor. |
| Terminal estimate | Expected occupancy equals the explicitly defined mean under the constructed law. | Combine with the existing finite density bound; no small-mean or concentration premise. |

The statement-design report is the naming and quantifier authority for this addendum. Its final argument-convention section specifies any abbreviated displayed notation. In particular, numeric factors receive N explicitly; no omitted positive-size, legal-word, good-column, concentration, or conditional-independence assumption may be supplied during implementation.

This work implements a previously unimplemented matrix-law dependency expressly identified in frozen contract v1. It neither changes v1 nor replaces the stronger printed small non-singleton theorem. The old contract, its 33 theorem statements, and the three mathematical source files stay byte-identical. The source's unresolved stable localization, endpoint smoothing, large-block density, exponent translation, and exploration obligations remain part of the full goal.

Implementation begins only after the final statement-design report and both acceptance appendices have been saved and a separate hashed freeze has been recorded. Any subsequent proof difficulty must be solved within this inventory; new assumptions, unproved declarations, and silent statement changes are prohibited.
