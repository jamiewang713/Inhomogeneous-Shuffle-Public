# Formalization coverage

The finite library is checked Lean code. The complete macroscopic profile-estimate
and bad-profile-reduction lemmas are **not yet formalized**. In particular,
compilation of a finite estimate does not discharge its shuffle-model,
time-integration, or ordered-limit applications.

The core results belong to the definitions and F01–F20 statements in
`FROZEN_FINITE_CONTRACT.md`. Their three independent reviews were compared
before that contract was frozen and before implementation. Its recorded
checksum has not changed. The separately frozen S01–S05 specialize those same
finite results to existing project definitions, without changing the core
assumptions. No source paper is treated as an imported Lean theorem.

## Assigned estimates

| Assigned item | Checked finite results | Remaining source obligation |
|---|---|---|
| Representative replacement | `cell_regrouping`, `cell_replacement`, `normalized_sum_error_bound` (F03, F06) | Construct the source cells and derive their empirical discrepancies; identify the representative target with the specified time integral. |
| Good and exceptional digits | `good_digit_bounds`, `exceptional_digit_bound` (F02) | Supply `RegularDigits` from the actual regular partition. These theorems project the frozen clauses; they do not prove existence of such a partition. |
| Interval blocking | `interval_blocking` (F07) | Construct the whole-grid-block and endpoint decomposition, including the lattice-count and target-mass bounds. The final finite error is explicit. |
| Decomposition of `c_L` | `good_exceptional_split`, `exceptional_cost_nonnegative`, `profile_cost_decomposition`, `length_exponent_split`, `length_exponent_profile` (F04–F05) | Connect the actual ambient/extension position sets and good-profile counts. No replacement of the actual ambient length by a rounded limiting time is made. |
| Tail estimate for `c_E` | `tail_cell_replacement` (F08) | Instantiate the power-sum observable and prove its integral approximation, including endpoint errors. |
| Maximal-pile estimates | `cost_antitone`, `maximal_pile_domination`, `maximal_pile_target` (F01, F09) | Derive maximal coordinate data, connect the prefix mass and `A(r,s)`, and perform the limiting error conversion. |
| Fluctuation comparison | `side_mass_ge_continuation`, `fluctuation_log_comparison` (F10–F11) | Prove the left/right cylinder and crossing identities in the source model, and identify the ambient exponent error. These results do not prove anti-concentration. |
| Entropy/KL estimates | `finite_gibbs_inequality`, `entropy_le_tilted_cost`, `profile_entropy_le`, `exceptional_cost_bounds`, `entropy_error_of_replacement` (F13–F15) | Connect raw profile counts to good-position sums and identify the integrated power-sum correction. The zero-total case is already proved. |
| Admissibility truncation | `tailWeight_le`, `badWordMass_le`, `badWordMass_le_tailWeight` and small-digit/scaling corollaries (F16, F18) | Boundary failures and actual matrix row expectations are connected by T01–T09 below. Sorted-edge comparison and ordered limits remain. |
| Exceptional-profile truncation | The same word-mass bounds with the exceptional-digit estimate (F02, F16, F18); `sum_edgeProbability_sq_le` | The actual exceptional-prefix event and matrix row expectation are connected by T06/T09 below. Graph edges and the source ordered-limit threshold remain. |
| Profile-class counting | `sparsePattern_card`, `sparsePattern_forget_image_card_le`, `boundaryDescriptor_card_le`, `profileDescriptor_card_le`, `lowCount_le` (F17, F19) | Actual admissible boundaries are encoded by T05 below. Full source profile images and the subpolynomial class-count limit remain. |

The auxiliary parent estimate `parent_crossing_good_cost` proves F12 from the
frozen parent and last-step inequalities. It does not construct the stopping
rule or prove those input inequalities for source words.

F20 is proved by `coarse_fibre_card_le`, `coarse_word_fibre_card_le`, and
`coarseProfile_not_injective`. It preserves the exceptional-label factor
`k^|E|`. A bound on each labelled fibre is still an input; no multinomial bound
for that fibre is claimed here.

## Checked source specializations

`SourceReplacement.lean` and `SourceFluctuation.lean` now discharge the
following finite connections in the table above. They use checked compatibility
copies of the existing `TimeProfile.Base` and `TimeProfile.Ambient` interfaces.

| Frozen specialization | Exported theorem | Connection now proved |
|---|---|---|
| S01 | `source_digitCost_eq_cost`, `source_regularDigits` | Exact cost convention and construction of `RegularDigits` from the existing source partition regularity. |
| S02 | `source_cE_replacement` | The actual source tail exponent satisfies the finite representative-target error, with every cell discrepancy retained. |
| S03 | `source_cL_maximal_target` | The actual source prefix exponent satisfies the finite maximal-pile target bound under legality. |
| S04 | `source_sideMaximum_ge_prefixMass` | An actual crossing witness gives the quantitative bound for the source side maximum, including the crossing factor in the continuation. |
| S05 | `source_fluctuation_comparison` | The existing extended-real `c_F` is bounded below by the exact `c_L` expression, including the ambient mass discrepancy and logarithmic threshold correction. |

Thus the regularity-to-finite interface and the deterministic mass-to-`c_F`
connection are no longer missing. The `S02` and `S03` target weights remain
finite data; their identification with time integrals is still unproved.
The `S04` crossing witnesses still need to be extracted from the actual
boundary families, while T08 now proves the stochastic expectation identity for the actual
fixed-column model. The independent first-column anti-concentration obstruction remains.

Both source-adapter modules were reviewed independently after implementation.
The dependency snapshots preserve all 33 prior theorem headers and all 54
other declarations. Their four compatibility changes are documented in
`vendor/time_profile/COMPATIBILITY.patch`; the original files are unchanged.

## Source issues that must remain visible

1. The time profile is not explicitly assumed measurable in the supplied
   sketch. No measurable-kernel assumption has been added to this contract.
2. The source coarse profile records exceptional positions without their digit
   labels. Its asserted single-type cardinality bound misses a possible
   `k^|E|` factor. Counting the number of coarse profiles and bounding the
   number of words in one coarse profile are different obligations.
3. The sketch's unweighted count of all high-exception choices is false. The
   checked weighted tail proof avoids that step and retains the factor `N`
   needed when converting a row probability to an expected row count.
4. Actual and limiting ambient lengths must be distinguished. A small error
   in the number of positions need not give a small error for unbounded
   selected-digit logarithmic costs.
5. The side-mass comparison does not repair the downstream deterministic
   first-column obstruction to the stated anti-concentration argument.

Detailed evidence and source locations are in `PROOF_STRUCTURE.md` and the
three reports under `reviews/`. None of these issues is hidden in an added
Lean premise.

## Validation and audit

`check_all.py` compiles every module with warnings treated as errors, checks
all three frozen contract checksums and the dependency snapshot hashes, scans for
forbidden proof escapes, and prints
the transitive axiom dependencies of every public theorem. The only permitted
foundational dependencies are Lean/mathlib's `propext`, `Classical.choice`,
and `Quot.sound`; no project axioms or placeholder proofs are accepted.
Only style linters are suppressed for prior dependency copies
(unusedVariables, unnecessarySimpa, unusedSectionVars, unnecessarySeqFocus).
Their original hypothesis binders and proof bodies remain unchanged; all newly
authored modules compile with warnings treated as errors and no such exemptions.

`VALIDATION.log` contains the actual final theorem count and compiler output.
The independent implementation audits check statement meaning and source
coverage separately from the compiler checks. A successful build certifies
the finite declarations, not the missing applications listed above.

## Checked actual boundary and matrix truncations

The separately frozen T01–T09 close these additional finite obligations:

| Contract | Connection proved |
| --- | --- |
| T01–T02 | Existing Model proportions form normalized simplex points; the original expectedCount equals its real product-word sum; included events inherit the weighted tail. |
| T03–T04 | Failure of the actual selected-boundary admissibility test implies at least floor(threshold)+1 small digits in the full word; both one-side and union functional bounds follow. |
| T05 | Actual admissible boundary lists inject into the exact relative descriptors. Both the admissible-word subtype and compatible pair subtype are proved finite, with the displayed cardinality bounds. |
| T06 | The literal exceptional-prefix filter has the finite tail bound, even with endpoints chosen as arbitrary functions of the whole word. |
| T07–T08 | Uniform fixed-column symmetry yields count/N marginals. Independent columns give the full row-word law and the exact expected number of rows in any word-set. |
| T09 | Actual matrix expectations satisfy the boundary and exceptional-prefix tail bounds, including the N and two-side factors. |

All three truncation reviews preceded the immutable T freeze. Independent
post-implementation audits cover all nine conclusions. A proof-elaboration
problem in the union corollary was separately sent to two agents and resolved
by normalizing the same set-union membership predicate, without changing its
statement.

Thus boundary exclusion, actual boundary descriptor encoding, exceptional
prefix exclusion, and the product-word-to-matrix expectation identity are no
longer missing. The required ordered-limit bounds are being reviewed separately
in ASYMPTOTIC_CANDIDATE.md; they are not included in the checked T statements.
The full source profile-class encoding, sorted graph-edge comparison, and
analytic integral applications remain distinct obligations.
