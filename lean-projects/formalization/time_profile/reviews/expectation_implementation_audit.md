# Independent expectation implementation and assigned-scope audit

Reviewed the frozen expectation contract, `FixedCountModel.lean`, the current `RowReindex.lean`, `ExpectedMass.lean`, `SourceNumerical.lean`, and the full proof map. This report does not modify any Lean statement or contract.

## P08: row reindexing

**Semantic verdict: approved, with no required correction.** After the dependency modules became available, I independently ran `build.py RowReindex`; all six P08 declarations compiled successfully, including the expected prefix/side corollaries.

`rowCount_reindex` quantifies over every row matrix, every predicate on complete row words, and every permutation of the row labels. It proves only equality of cardinalities. Its finite-indicator-sum proof is the correct mathematical argument and includes empty decks/column families whenever the types admit data.

`sample_rowCount_reindex` substitutes an arbitrary sample-dependent permutation into this pointwise equality. It does not impose independence, measurability, or constancy on that choice. `expected_rowCount_reindex` then integrates an equality of the counted random variables; it does not claim that the reindexed sample itself still has the fixed-count uniform law. This distinction is essential for sorting.

The prefix corollary counts exactly the rows matching x before M and has the frozen domain N>0, M<=K. The left/right corollaries constrain all digits before j, require the strict inequality at j, and leave later digits free. Their w<=j.val assumption is explicit. Their conclusions are unconditional expectations of restricted row counts, equal to the old prefixMass/sideMass definitions. No expected-count identity has been replaced by a conditional-on-ambient-size statement.

These statements apply to a permutation used to sort a sample because they hold for every sample-dependent permutation. They do not construct a sorting algorithm or assert a sorted-row marginal, graph localization, or interval endpoint result. Those would be separate results.

While the expectation dependencies were being completed, I independently compiled the unchanged first three P08 declarations against `FixedCountModel` through the compiler's standard-input interface. The general cardinality, sample-dependent cardinality, and integral-equality proofs all passed. No root-owned source was edited for this check.

## P05–P07 cross-review

**Semantic verdict: approved, with no required correction.** I independently reviewed all six public theorems and all three expectation-based definitions in `ExpectedMass.lean` while its P04 dependency was being finished. The completed module was subsequently used by the successful full P08 check above.

* `expected_prefix_count` has no legality premise. Impossible cylinders have zero mass and remain covered by the box-occupancy formula. The explicit M<=K source domain is preserved.
* `cL_expected_mass_exponent` has exactly the old D04 ordered-length and legality hypotheses, N>=2, and arbitrary real b. It rewrites the actual prefix expectations at M and w and invokes the proved exact logarithmic identity. No extra positivity or b>=0 premise appears.
* The two side-count identities use the literal unrestricted-suffix side predicates and split the prefix product at the exact w. The necessary w<=j.val condition is present. There is no legality or positive-side premise.
* `expectedLeftMaximum` and `expectedRightMaximum` take the finite nonnegative-real supremum of the separate expected counts. They do not take an expected random maximum. Their empty-supremum and zero conventions agree with the existing sideMaximum.
* `expectedCF` uses the same square root, extended logExponent, and minimum as cF. The equality in `WithBot Real` consequently includes zero sides and empty position sets. No anti-concentration or concentration assertion is attached to it.

`FixedCountModel.lean` itself has already compiled, and its eleven exported P01/helper theorems passed a foundation audit using only propext, Classical.choice, and Quot.sound. Its law is the actual uniform law on the dependent product of finite count-constrained columns. Its sample-row legality is derived from exact prescribed counts, not included as a filtering condition or hypothesis.

## Numerical layer and genuine remaining boundaries

The current `SourceNumerical.lean` closes the formerly missing source-data numerical implication. Its large and small bounds derive a real F from Crossings and prove the appropriate stability/parent-crossing implications. The singleton theorem requires neither Crossings nor a finite F. Terminal exclusion has a positive delta, full terminal legality, Crossings, the ambient errors, and the terminal budget; it has no exceptional-allowance or stability premise.

`exists_uniform_source_margins` composes the parameter thresholds, C=1 regular-partition existence, actual source estimates, and numerical inequalities. The threshold N0 precedes cuts, the time law, ambient parameters, digit arrays, and time classifiers. The approximation budgets are discharged inside the proof. What remains in its conclusions is the original data condition—almost-likeness, ambient approximation, exceptional allowance, crossings, and the appropriate finite stopping predicate—not an assumed analytical estimate.

For the frozen assigned interface, once P02–P08 compile and the entry point/full audit include them, I find **no essential remaining mathematical gap** in the following list: simplex-valued pile profiles; time-cell membership; regular partitions and their existence; literal almost-time-profile-like cuts; ambient blocks and expected masses; good/exceptional digits; cL/cE/cF with bottom values; S/Q/R/H; and the numerical first-moment margin with explicit nested parameter choices.

The following are different interfaces and must not be reported as consequences of those results:

1. Existence of ordinary time integrals or the manuscript's two-sided quadrature identities. The literal arbitrary TimeLaw can fail measurability, and the supplied counterexample still applies. The proved one-sided route suffices for the assigned numerical margin and does not establish these stronger statements.
2. Boundary-family construction, unique stopping-prefix coverage, exceptional-profile truncation, and the entropy/cardinality count of admissible profile classes. The numerical theorem accepts the relevant finite crossing/allowance/stability data; proving those data for the exploration belongs to the boundary and first-moment argument shown in the map.
3. Hypergeometric concentration, conditional ambient laws, anti-concentration, endpoint localization, and edge-density bounds. In particular the source cF anti-concentration defect survives the new expectation identities; the identities merely prove the intended meaning of cF.
4. The probabilistic first-moment theorem for common graph edges, exponential-moment argument, total-variation/mixing upper bound, and the cold-set/lower-bound program. These are explicitly mapped external layers.
5. Random-pile mixing transfer. The randomized almost-like predicate is formalized, and the full proof map gives the upper transfer and its uniformity requirements. A random-pile mixing theorem requires the deterministic probabilistic upper bound, not just the numerical exponent theorem. No extra independence of random cut vectors should be introduced.

Two optional representation conveniences are not needed by the proved numerical theorem: constructing a TimeMesh of arbitrarily prescribed positive mesh bound, and adding a wrapper that instantiates the explicit ambient error budgets from a particular UniformlyVanishing family. The numerical theorem works for every finite time classifier, so it does not require a mesh-size hypothesis; the actual source cells are already available through the proved unique-cell classifier. The current explicit finite error-budget formulation already replaces the asymptotic shorthand. If either convenience is added, it should receive its own reviewed/frozen exact statement rather than being silently treated as already implemented.

## Documentation corrections required before final delivery

The inspected README still describes only the 80-theorem initial tranche and says the one-sided route is unfrozen/unimplemented and the integral/numerical bridge is blocked. Those statements are stale. It should list the analytic and expectation freezes/modules, the actual verified theorem count, the source-facing numerical result, and the precise surviving limitations above.

The last paragraph of the inspected proof map still lists expectation/product-mass identification as an obligation. Once P01–P08 compile, change that status to the implemented exact fixed-count identity. Retain ordinary integral existence, false two-sided quadrature, and downstream anti-concentration as separate unsupported claims. The whole upper/lower/random-pile architecture remains a dependency map, not a claim that all its nodes have been formalized.
