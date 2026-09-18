# Independent final implementation review: ambient-relative coordinates

I independently read the complete frozen relative contract, all four current `Relative` implementation files, the full elaborated signature log, and the logical-dependency log. I also checked the actual earlier expected-edge and exponent inputs used by the new density proofs. This review is of the implementation verified at **2026-09-17 22:32:25 UTC**, after all modules compiled. No proof, mathematical source, prior implementation, or frozen report was changed during this review.

The implementation is accepted against exactly R.D01–03 and R.01–18. There is no additional named definition, instance, theorem, or helper, and no change to an explicit or implicit assumption. The generic and matrix statements retain their frozen quantifier order and domains. In particular, no relation between the law and an arbitrary shift is assumed.

## Verification record

`verify_relative.py` completed successfully with Lean 4.24.0 and the project's pinned mathlib revision `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. It checked the exact eighteen indexed declarations, the exact three definition names, their assigned files, the four-module file inventory, the build, and all declaration signatures and logical dependencies. It also checked the relative contract, index, four independent pre-code reports, five parent contracts, twenty-one parent implementation modules, and all three permitted mathematical sources against the freeze's hashes. All were unchanged.

The relative frozen contract remains SHA-256 `e5c6977f4b448a62ddd54e64893016c2fbfa83c8a9ab34532590db3012fb73f4`. The checked implementation hashes are:

| File | SHA-256 |
| --- | --- |
| `EdgeLocalization/Relative/Model.lean` | `6c1007fde849fbaed20505e4583cb3e66c184709855ed6ea495579980545822b` |
| `EdgeLocalization/Relative/Deck.lean` | `edd06dd450e248362feadca74887198f3dd4e90ec844eb5c7ab610209527d3a4` |
| `EdgeLocalization/Relative/Density.lean` | `774163841c68a9da6de8f5f0a27c1d03a09c18302b7e251a1e4625acbab93637` |
| `EdgeLocalization/Relative/Estimates.lean` | `10df361c6a48b88bad4595aca97460eedd86af9b9c62f052ec52e932de348a40` |

The full build completed successfully. Every new theorem and definition depends only on `propext`, `Classical.choice`, and `Quot.sound`; no additional axiom or incomplete proof dependency occurs. The implementation contains no prohibited proof tokens. Its source hashes were checked again after the build and signature/dependency checks, so the verification and this review refer to the same source snapshot.

The machine verification records and logs are `relative_verification.json`, `relative_build.log`, `relative_signatures.log`, and `relative_logical_dependencies.log`. The printed signatures supplement, rather than replace, the manual comparison below: the source was inspected for the proof parameters suppressed by Lean's ordinary pretty printer.

## Definition audit

- **R.D01 `relativeInternalEdges`:** the value is exactly the filter of `range (N-1)` by membership of `i+s` in the existing absolute internal-edge set. Both the finite support and the direction of translation agree with the freeze. There is no truncated subtraction in this definition and no implicit assertion that an arbitrary shift retains all edges.
- **R.D02 `relativeEdgeDensity`:** the value is exactly the sum of squares of relative membership probabilities over that same global support. The generic law has only its existing `Fintype` requirement. The shift is the frozen function of the complete single outcome, evaluated inside the same event as the row array.
- **R.D03 `ambientLeft`:** the value is exactly the cardinality of the filter of `range N` by strict lexicographic comparison `rows i < wList`. `Mathlib.Data.List.Lex` is imported, matching the order used by the existing sorted-row construction. The strict comparison and zero-based cardinality implement the source offset `ι_w-1`, including the insertion cut of an absent word.

The argument order, namespace, codomains, and definition bodies are unchanged. No ambient probability law, random population, relative-density alias, or independent shift variable was introduced.

## Deterministic statement and proof audit

| Frozen item | Exact-domain and actual-proof review |
| --- | --- |
| R.01 `relativeInternalEdges_subset_range` | All `N`, row maps, words, and natural shifts remain quantified. Membership is projected directly from the defining filter. |
| R.02 `relativeInternalEdges_zero_shift` | The equality is only for shift zero, exactly as frozen. Both containments use addition by zero; the reverse containment uses the previously proved absolute-edge support. |
| R.03 `relativeInternalEdges_card_le` | The proof maps each relative edge `i` to `i+s`, uses defining membership for the target, and proves injectivity with natural right-add cancellation. No sorting, size, or shift bound is assumed. |
| R.04 `ambientLeft_le_deck_size` | The strict-below filter is contained in `range N`, whose cardinality is `N`. No sortedness is required. |
| R.05 `ambientLeft_nil` | The proof converts strict list comparison to `List.Lex` and uses `List.not_lex_nil`. This proves the filtered set empty without an assumed endpoint convention. |
| R.06 `matrix_ambientLeft_le_internal_edge` | Its only premises after the actual fixed matrix and arbitrary list words are the list-prefix relation and the internal-edge membership. There is no `hn`, selected-digit legality, common length, or assumed sortedness. Edge support proves the `Fin N` bound for `i`; each counted `j` gets its bound from the deck filter. Prefix transitivity gives an ambient prefix of row `i`; the actual proof splits its append suffix into empty/nonempty cases and obtains the weak lexicographic inequality using `List.Lex.append_left`. The existing sort monotonicity contradicts a counted `j≥i`. Thus the counted set is contained in `range i`. |
| R.07 `matrix_relativeInternalEdges_card_eq` | The upper cardinal bound is R.03. For the reverse injection the proof maps each absolute edge `j` to `j-s`, with `s` equal to the actual computed ambient cut. R.06 proves `s≤j` before cancellation is used. The relative-support bound follows from `j-s≤j<N-1`; membership and injectivity follow from adding back `s`. This establishes count preservation for every source edge, without equating sets at different coordinates or any densities. |

R.06 and R.07 apply to arbitrary list words related by a prefix. The vector-prefix relation used in the exponent statements is a valid specialization, as established in the pre-code argument. No vector-to-list adapter is silently assumed by a proof: the scalar wrappers use the independently valid arbitrary-shift bounds, while these two deterministic theorems provide the exact list-level source-recentering guarantee.

## Generic and actual-matrix density audit

| Frozen item | Exact-domain and actual-proof review |
| --- | --- |
| R.08 `relative_density_le_sq_expected_absolute_edges` | The law may be nonuniform, and `shift : Ω → ℕ` is unrestricted. The proof bounds the sum of squares by the square of the sum using probability nonnegativity. The existing finite expected-cardinality identity identifies that sum with the expected relative count. R.03 and expectation monotonicity give domination by the expected **absolute** count. The required nonnegativity before squaring is proved locally. |
| R.09 `relative_density_le_expected_occupancy` | The existing probability-square/cardinality inequality is applied to the relative edge function on the proved support. A pointwise chain through R.03 and the existing absolute edge-cardinality/occupancy bound gives the expected occupancy conclusion. There is no endpoint or spatial probability hypothesis. |
| R.10 `relativeEdgeDensity_zero_shift` | Unfolding the two density definitions and applying R.02 proves exactly the zero-shift equality. No equality for a varying or nonzero shift is claimed. |
| R.11 `relativeEdgeDensity_eq_expected_shared_internal_edges` | The proof specializes the previously constructed independent-product intersection formula to the two relative edge functions, with R.01 proving each support condition. Each copy uses its own shift value `shift z.1` or `shift z.2`. `pow_two` identifies the two equal membership probabilities. This is the overlap at matching relative coordinates, not at matching original coordinates. |
| R.12 `matrix_relative_density_le_mean_tail_fourth` | The exact existing `matrixLaw n hn`, full population `N`, prefix data, and arbitrary matrix-dependent shift are retained. The proof begins with R.08 and the already proved bound on expected absolute internal edges, then squares the nonnegative inequality and normalizes the real polynomial. It obtains the frozen factor `prefixMean^4 * tailCollisionFactor^2 / 4` for all `N`. It does not use an absolute-density upper bound as a bound on relative density. |
| R.13 `matrix_relative_density_le_prefixMean` | R.09 and the existing exact expected sorted-occupancy formula give the result. There is no additional legality, lower-population, smallness, or nonterminality premise. |

The actual proofs require no independence of different edge positions within one graph and no independence between a graph and its own shift. Product independence in R.11 is supplied entirely by the earlier constructed `FiniteLaw.prod` for two complete outcomes. There is no probability division or conditioning event in this addendum.

## Exponent statement and proof audit

All five exponent wrappers use the exact computed shift `fun ω => ambientLeft N (sortedRows n ω) (prefixWord w)`. R.14–17 retain the frozen X.09–12 vector domains: the same full count array and `hn`, `hM : M≤K`, `hAM : A≤M`, coordinate prefix equality, real `b`, `N≥2`, and legality of the selected child prefix. R.15–16 append the same real `δ` and strict cutoff on `ambientSizeExponent`, not on the actual mean exponent. R.18 retains the exact X.14 full-word domain. The ambient length proof in the nonterminal error is literally `hAM.trans hM`; the terminal error uses `hA`.

Write `L`, `ε`, and `E` only as display abbreviations for the already frozen size exponent, signed ambient mean error, and tail exponent. The checked conclusions are:

| Frozen item | Exact conclusion and proof |
| --- | --- |
| R.14 `matrix_relative_density_le_ambient_tail_exponent` | `Drel ≤ N^(4(L+ε)+2E)/4`. The proof specializes R.12, invokes the proved mean-power identity and tail-factor comparison, proves the relevant tail and mean nonnegativity, and applies trusted real-power identities. It imports the Mean and Tail modules and uses no absolute-density theorem. |
| R.15 `matrix_relative_density_le_small_coarse_exponent` | `Drel ≤ N^(2E+8δ+4ε)/4`. From `L<2δ`, real linear arithmetic proves the needed exponent comparison; `N≥2` supplies the base condition for power monotonicity. |
| R.16 `matrix_relative_density_le_small_singleton_exponent` | `Drel ≤ N^(2L+2E+4δ+4ε)/4`. The same cutoff gives the corresponding comparison from R.14. No stable-family or singleton predicate is added. |
| R.17 `matrix_relative_density_le_ambient_size_exponent` | `Drel ≤ N^(L+ε)`. R.13 and the existing exact mean-power identity prove it directly. There is no smallness condition. |
| R.18 `matrix_relative_density_terminal_exponent` | The same mean-power upper bound at `M=K`, with the full-word legality and original ambient proof. The proof specializes R.17 at `Nat.le_refl K`; Lean discharges equality of length-proof arguments by proof irrelevance. It needs no small-mean premise. The existing tail-exponent-zero theorem remains available but is not unnecessarily required for this mean bound. |

The signs and coefficients of the unrestricted error `ε` are preserved. No limit notation, assumed small error, altered definition of `L`, or new asymptotic-rate hypothesis occurs. Every scalar proof condition comes from a frozen premise or a previously proved lemma.

## Boundary cases and limits of the result

- For `N=0` and `N=1`, the fixed edge support is empty. R.01–13 keep these domains. The deterministic injections and finite-sum proofs do not divide by `N` or exclude these cases. In R.06 an edge membership would force `i<N-1`, so an invalid finite index cannot arise. The inherited expected-edge estimate already proves its own exceptional population cases. R.14–18 retain their explicit earlier `N≥2` log/power domain.
- A shift can exceed the population, depend on all columns, or occur on a zero-weight outcome. The generic results continue to hold for their defined subgraph. For the actual ambient shift, R.06–07 supply the stronger no-loss result. An empty ambient cylinder has a defined insertion cut; the proof never chooses a first occupied ambient row.
- Empty words, empty columns, zero piles, and an empty alphabet whenever the original data exist are not ruled out by new assumptions. R.05 and R.10 give the exact root normalization. The finite matrix statements retain illegal selected digits as zero-mass cases; only the existing exponent domain imposes selected-prefix legality.
- Prefix-as-append case analysis explicitly covers equality with the ambient word and strict extension. Sort monotonicity applies with ties, and counted rows satisfy a strict comparison, so equality creates no missing ordering case.
- Cardinality preservation under the source recentering does not imply equality of absolute and relative densities. The implementation makes no such claim. Likewise, the independent-relative-copy overlap identity does not identify that quantity with the manuscript's whole-deck absolute first moment. A future aggregation or coordinate-transfer argument remains a separate obligation.

This addendum completes its exact finite coordinate, count, overlap, and density inventory. It does not complete the original goal's negative-`c_F` improvement, per-edge stable localization, stable-block count, concentration and endpoint windows, or exploration-conditioned argument. No source claim or earlier frozen theorem was replaced by one of these finite results.
