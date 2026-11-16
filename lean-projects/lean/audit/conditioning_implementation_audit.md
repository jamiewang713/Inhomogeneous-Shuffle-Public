# Conditioning and residual-sampling implementation audit

Reviewed against frozen contract v1, SHA256 `050b08407c8195360cc92c0ec502e865861384c7291040751b25c5bac136d839`.

Files reviewed: `Shuffle/Conditioning.lean` and `Shuffle/ResidualSampling.lean`. This final audit did not change their Lean source. Both files were recompiled successfully with `lean/check.sh` after their final edits. A source scan found no occurrences of `axiom`, `sorry`, `admit`, or `native_decide` in either file.

## Statement fidelity

| Frozen ID | Implementation | Finding |
|---|---|---|
| D2, F3 | `FiniteLaw.condition`, `condition_prob`, `condition_expect` | A conditional finite law requires strict positivity of the conditioning event. Its mass and all event probabilities are the exact normalized restrictions. |
| F3, null atoms | `mass_eq_zero_of_prob_eq_zero`, `prob_inter_eq_zero_of_prob_eq_zero`, `weighted_conditionalProb`, `weighted_conditionalExpect` | Null atoms are shown to contribute zero. The total quotient functions are never asserted to be probability laws at a null atom. |
| F3, uniform fibres | `uniform_prob_pos_iff`, `condition_uniform_mass`, `uniform_conditionalProb`, `uniform_conditional_point_of_fiber_equiv` | Nonempty uniform fibres have the exact uniform conditional masses. The nonempty outcome-type assumption for the unconditional uniform law is inherent in D1; it does not exclude empty labelled populations whose sample space contains the empty sample. |
| F4 | `total_probability`, `total_expectation`, `total_probability_bound` | Total finite sums include zero-weight null atoms. A numerical bound is assumed only at positive atoms. |
| F4, coarse conditioning | `coarse_total_probability`, `coarse_total_probability_bound`, `sum_conditional_atom_prob` | The coarse atom is positive, the coarse reveal is a function of the fine reveal, and the summation weights are conditional probabilities given the coarse atom. |
| F5 | `shifted_anticoncentration_transfer` | The shift is integer-valued and fixed on the fine atom; the count is natural-valued; the point bound is required only on positive good atoms; `b≥0` is retained. The selected event only needs containment in the good reveal set, not measurability in the reveal. Negative shifted target values are explicitly handled as empty events. |
| C1, feasibility | `sample_prescription_pos_iff` | Under the prescribed uniform sample law, positivity is equivalent to `|B|≤m` and `m−|B|≤|V\R|`, with the frozen set inclusions `B⊆R⊆V`. No positive residual-size hypothesis appears. |
| C1, residual uniformity | `residualSampleEquiv`, `sample_conditional_residual_mass` | The proof constructs the exact bijection between the prescribed sample fibre and residual samples using subtraction and union. Empty residual populations are included. |
| C1, hypergeometric variables | `sample_conditional_intersection_prob`, `sample_conditional_hypergeom_mass`, `sample_conditional_hypergeom_law` | The actual residual population is `|V\R|`, the marked size is `|A|`, and the draw count is `m−|B|`. Exact law equality is proved for every natural count, not just points in the support. |
| C3 | `conditional_uniform_sample_intersection_law` | The marked set is a function of the reveal atom and the conditional sample law is exactly the frozen uniform law on the full labelled population `V`. This is the atomwise form of C3; it does not replace the population by the previous survivors. |
| C4, generic transport | `conditional_expect_eq_of_count_law`, `conditional_prob_eq_of_count_law`, `conditional_variance_eq_of_count_law` | Exact count-law equality transfers arbitrary moments, events, and variance. No extra almost-sure or pointwise bound on the count is assumed; zero mass outside the finite target support is deduced from the law equality. Named hypergeometric specializations are owned by the separate `ConditionalHypergeometric.lean` implementation. |
| D2, C2 independence step | `product`, `product_prob_rectangle`, `product_prob_rectangle_pos`, `condition_product_rectangle` | Independent finite coordinates retain their product law under positive separate coordinate prescriptions. Dependent coordinate types and an empty coordinate index are included. No preservation claim is made for arbitrary exploration events. |

## Degenerate and conditioning checks

- At zero sample size, the sample subtype still contains the unique empty sample; its unconditional uniform law is valid.
- When all labels are revealed, feasibility forces zero residual draws, and the residual sample type again contains exactly the empty sample.
- Zero original or residual marked piles cause no divisions by those pile sizes.
- The only normalization divisions producing finite conditional laws are guarded by strictly positive event probabilities.
- Arbitrary natural counts above the possible sample size have probability zero, proved in `sample_intersection_law`; there is no unguarded natural-subtraction mass formula outside the support.
- C3's exact conditional-uniform law is the premise expressly present in the frozen C3 interface. The theorem does not pretend to derive that law for an arbitrary shuffle exploration.
- No version of the false ambient conditioning-transfer or non-exhaustion implication is introduced.

## Compiler notes and remaining integration

The successful compiler runs emit only three linter observations: the already-frozen finite coarse-reveal typeclass is not needed by one proof, one tactic sequencing expression can be shortened, and `hres` in the residual point-mass theorem is redundant once an actual residual sample `T` is supplied. The frozen hypotheses were retained rather than removed in response to these observations.

These files provide the probability-space interfaces, not a proof of the full shuffle graph exploration or ambient geometry. A concrete future exploration application must establish its conditional uniform-sampling law using the proved sampling/column constructions. Arbitrary conditioning is not covered. The original ambient claims remain false as documented by X1.

## Reviewed D2/D6 random-pile plan

The root's proposed finite mixture `Σθ p(θ)qθ(ω)` and joint mass `p(θ)qθ(ω)` are mathematically sound. The index marginal equals `p`, and conditioning on a positive index atom gives exactly `qθ`. Mapping each legal-column subtype to the common raw assignment space before taking the column product avoids dependent outcome-type difficulties. Arbitrary finite laws on complete feasible histogram arrays impose no independence on histogram coordinates. This approves that already-frozen interface plan; its separate Lean implementation must still be checked by its owner.

## Final read-only review of the implemented D2/D6 interface

Read `Shuffle/FiniteMixture.lean` and `Shuffle/RandomColumns.lean` after the root reported both compiled. **Approved: the implementation matches the plan and frozen D2/D6 encoding.** No Lean code was changed during this review. A source scan found no `axiom`, `sorry`, `admit`, or `native_decide` in these files.

- `mixture` and `joint` use exactly the frozen finite masses. Their normalization proofs sum the conditional laws; no independence of the mixing parameters is introduced.
- `joint_first_prob` identifies each index-atom probability as `p.mass θ`. Both conditional-law exports require the strict premise `0<p.mass θ`. There is no probability-law assertion for a null parameter atom.
- `joint_condition_second_map` proves equality of the complete conditional outcome law, not just equality of selected moments. `joint_second_map` proves that forgetting the latent index gives the mixture.
- `rawMatrixLaw` maps each uniform legal-column law to the common raw assignment type and takes its finite product. The rectangle theorem proves the intended column independence. Histogram feasibility is carried by `Histogram`; no further pile-size positivity is assumed.
- `randomMatrixLaw` accepts an arbitrary finite index law and an arbitrary index-dependent complete histogram array. In particular, histogram coordinates may be perfectly dependent. `conditional_randomMatrixLaw` and its rectangle theorem recover the product fixed-column law only after the positive complete-index atom is fixed.
- Empty column-index products are admitted and have the unique empty matrix outcome. Empty labelled populations and zero piles are inherited from the legal-column construction. No `Nonempty` assumption is added for a population or column index. As with every finite law, an actually empty mixing outcome type cannot carry masses summing to one.

The exported conditional theorem is stated on the latent index atom `θ`. This is an allowed representation of a finite law on complete histogram arrays: choose the index type to be those arrays themselves. The more general parameterization also allows duplicate array labels; its conditional raw law depends only on the selected array, so duplicates introduce no additional independence requirement. No theorem here claims to prove the asymptotic random-pile mixing-time extension; it supplies its frozen probability-space interface.
