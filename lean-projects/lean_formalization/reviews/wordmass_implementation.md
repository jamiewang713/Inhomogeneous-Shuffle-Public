# WordMass implementation review

Implemented file: `RiffleProfiles/WordMass.lean`.

The implementation follows frozen F18 and F20, after independent reconstruction, representation, and adversarial reviews were compared by the root agent. This module has no dependency on unpublished project probability lemmas and introduces no extra model assumptions.

## Definitions

- `wordWeight p x`: product over the finite position type of the selected coordinate weights.
- `badPositions bad x`: the finite positions where the selected digit lies in the prescribed bad-digit set.
- `badCount bad x`: its cardinality.
- `badWordMass p bad h`: the sum of product weights of all words with at least `h` bad positions.
- `oneCellCoarseProfile good x`: the source coarse data specialized to one time/simplex cell, namely the good-digit count vector and the exceptional-position set. It deliberately does not record exceptional digit labels.

These use finite types and finite sums only. The coordinate probabilities and prescribed digit sets may depend on the position; there is no time-homogeneity assumption.

## Declaration coverage

| Frozen clause | Checked declarations | Exact coverage |
| --- | --- | --- |
| F18 normalized product words | `wordWeight_nonneg`, `wordWeight_sum` | Nonnegative coordinate weights give nonnegative word weights; coordinate normalization gives total word mass one. |
| F18 finite generating argument | `badCount_generating_product`, `wordWeight_generating`, `coordinate_generating`, `wordWeight_generating_le` | Factorization of the bad-count generating sum and its bound by `(1+a*(z-1))^(card positions)`. |
| F18 bad-count tail | `badWordMass_le` | The frozen Chernoff form with `a>=0`, coordinate nonnegativity and normalization, bad-coordinate mass at most `a`, and `z>=1`. All natural thresholds `h` are allowed. |
| F18 union-tail alternative | `box_word_mass`, `exact_badPositions_mass_le`, `sum_badSet_weights`, `badWordMass_le_tailWeight` | Partition by the exact bad-position set; bound each fibre by `a^(card set)`; group sets by cardinality to obtain `tailWeight`. The representation agent independently reconstructed the same argument. |
| F18 small-digit input | `badDigitMass_le`, `badWordMass_smallDigits_le` | If each prescribed bad digit has weight at most positive `chi`, use `a=(card alphabet)*chi`. No bound on the number of bad digits stronger than the alphabet size is assumed. |
| F18 small-digit union tail | `badWordMass_smallDigits_le_tailWeight` | The same per-digit input for the union-tail alternative. |
| F18 deck-size multiplication | `scaled_badWordMass_le`, `scaled_badWordMass_le_tailWeight` | Multiplication by a natural `N` of both already proved finite word-mass inequalities. It does not identify this number with a shuffle expectation. |
| F18 edge squares | `sum_edgeProbability_sq_le` | For finite edge values in `[0,1]`, the sum of their squares is at most their sum. |
| F20 coarse fibre | `coarse_fibre_card_le` | A finite class partitioned by functions `E -> Fin k` has cardinality at most `k^(card E)*B` if each labelled fibre has cardinality at most `B`. |
| F20 actual exceptional restriction | `coarse_word_fibre_card_le` | The preceding theorem applied to word restrictions to a finite exceptional-position set. |
| F20 concrete collision | `coarseProfile_not_injective` | Constant words `0` and `1` of length one over two symbols have identical coarse data when every position is exceptional; Lean proves the words are distinct. |

The nonnegative `a` premise is retained in the main exported F18 theorem as `_ha`, although the finite generating argument can actually deduce the bound without using that premise. The underscore does not remove the premise from the theorem type.

## Boundary cases

No proof assumes nonempty position or alphabet types, `h<=K`, `a>0`, or `z>1`. For an empty position type the empty word has product weight one, as required. For an impossible threshold the filtered word sum is empty. The coarse fibre argument covers zero `B`, empty fibres, an empty exceptional set, and even an empty digit type whenever the labelling function exists. The main F20 statement uses a uniform fibre bound, with no partial maximum over an empty family.

## Validation

The command

`python3 lean_formalization/check_lean.py lean_formalization/RiffleProfiles/WordMass.lean`

passed with warnings treated as errors using the pinned Lean 4.19.0 / mathlib runtime. No forbidden proof escape keywords occur in the file.

Kernel dependency checks for `badWordMass_le`, `badWordMass_smallDigits_le`, `scaled_badWordMass_le`, `badWordMass_le_tailWeight`, `badWordMass_smallDigits_le_tailWeight`, `scaled_badWordMass_le_tailWeight`, `sum_edgeProbability_sq_le`, `coarse_fibre_card_le`, `coarse_word_fibre_card_le`, and `coarseProfile_not_injective` report only the standard foundations `propext`, `Classical.choice`, and `Quot.sound`. No custom or placeholder assumptions occur.

The representation agent independently audited the compiled exact-set/factorization proof of the union-tail alternative and confirmed its coverage of empty positions, thresholds above the length, and `a=0`.

## Explicit gaps

- Both finite F18 alternatives are complete. The separate F16 generating-function bound on `tailWeight`, used only through its definition here, belongs to `Counting.lean`.
- No statement identifies finite product weights with shuffle-matrix row marginals or `N` times word mass with expected interval mass.
- No shuffle-graph event is identified with the abstract edge values. The finite edge inequality alone is proved.
- The module does not perform the ordered `chi -> 0`, `N -> infinity` asymptotic substitutions.
- F20 bounds a coarse fibre using an explicitly given bound on each labelled fibre. It does not claim that a labelled fibre's multinomial/entropy bound is already proved, nor erase the `k^|E|` factor.
- The concrete finite coarse collision is distinct from the stronger stable/admissible asymptotic counterexample in `reviews/counterexamples.md`; no stable-block or integral bridge is assumed here.

This module therefore certifies the specified finite word-mass and fibre estimates, not the complete assigned macroscopic profile reduction.
