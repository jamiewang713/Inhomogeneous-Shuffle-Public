# Independent audit of finite counting and word mass

Read-only audit by the representation reviewer after implementation. I read
both complete Lean modules, the frozen F16–F20 contract, and the two
implementation coverage reports. I did not edit either Lean module. The
coordinator is separately performing the combined kernel dependency audit;
this review concerns mathematical content, representations, and coverage.

Audited source hashes:

- `Counting.lean`: `f211d8799943aede21e2ca36395b96d8cec349f3c2d34cfa7087423eaa555797`
- `WordMass.lean`: `d7cebbc71fb68bc6e186576c90e13494d91c252c819f48b8c4c02c8590a4331b`

## Result

The implemented finite estimates match their stated mathematical domains.
I found no strengthened model assumption, invalid treatment of zero or
empty cases, full-support assumption, row-independence assumption, or claim
that source boundary families have already been injected into descriptors.
No forbidden proof escape or added axiom declaration occurs in either file.

The initial audit identified the missing alternative inequality
`badWordMass <= tailWeight` inside frozen F18. The implementer subsequently
proved it, using independently discussed finite product/sum arguments. I
read the complete new proof and approve it. Both the MGF and union-tail
alternatives are now implemented, closing that finite-contract coverage gap.

## Contract-by-contract check

| Frozen clause | Audit result |
|---|---|
| F16 | `tailWeight_le` has exactly nonnegative `a`, `z>=1`, and natural `K,h`. It compares `z^h` with `z^q` on the selected tail and sums nonnegative terms. |
| F17 | `lowCount_le` has exactly `0<z<=1` and natural `K,h,k`. Power monotonicity is reversed in the correct direction on `q<=h`. |
| F18 normalization | `wordWeight_nonneg` and `wordWeight_sum` prove nonnegativity and normalization of the finite product weights. The latter needs normalization only because it is an algebraic identity; no nonnegative-coordinate hypothesis was replaced by a conclusion. |
| F18 MGF bound | `wordWeight_generating` and `coordinate_generating` prove the finite factorization, then `badWordMass_le` proves the frozen MGF tail. It retains `a>=0`, coordinate nonnegativity and normalization, per-coordinate bad mass at most `a`, and `z>=1`. |
| F18 small digits | `badDigitMass_le` bounds the number of possible bad labels by the whole alphabet cardinal, not by an unproved smaller count. `badWordMass_smallDigits_le` uses the source's positive `chi`. |
| F18 scaling | `scaled_badWordMass_le` multiplies the finite inequality by natural `N`. Its comment expressly declines to identify this with a shuffle expectation. |
| F18 edge squares | `sum_edgeProbability_sq_le` requires precisely values in `[0,1]` and proves the finite sum inequality. No random graph identification is claimed. |
| F18 alternative union tail | `badWordMass_le_tailWeight` retains the frozen normalization, nonnegativity, and bad-coordinate bound. It partitions words by their exact bad-position sets, bounds each fibre by `a^(card S)`, and groups subsets by cardinality. `WordMass.lean` now imports `Counting.lean` for the frozen `tailWeight` definition. |
| F18 final union-tail wrappers | `badWordMass_smallDigits_le_tailWeight` substitutes the proved bad-coordinate bound `(card alphabet)*chi`, with the frozen positive `chi`; `scaled_badWordMass_le_tailWeight` multiplies by nonnegative natural `N`. Neither introduces a source-model or expectation assertion. |
| F19 sparse labels | `sparsePattern_card` proves the exact dependent-label cardinality, with all natural parameters permitted. The forgetful-image theorem counts the image, as frozen, rather than pretending it contains every unlabelled set when the alphabet is empty. |
| F19 boundary/profile descriptors | Both cardinal bounds retain the frozen source premise `2<=k`. The descriptor space uses final digits, including terminal records, and the raw count array has `D` entries in `{0,...,K}`. No source-family injection is claimed. |
| F20 fibres | `coarse_fibre_card_le` sums cardinalities over all functions `E -> Fin k` and uses the given uniform bound `B`. `coarse_word_fibre_card_le` specializes to actual restrictions of words. Neither assumes a nonempty fibre or a maximum attained in an empty family. |
| F20 collision | `coarseProfile_not_injective` proves the frozen finite collision of distinct one-letter words with the same exceptional-position set and zero good counts. It does not claim a stable/admissible source counterexample or a difference of actual logarithmic costs. |

## Dependent sparse labels and zero alphabet

`SparsePattern K h k` is a sigma type over a finite subset `s` of `Fin K`
with `s.card<=h`; its second coordinate is a function from the subtype of
elements of exactly that subset to `Fin k`. It is not a function on all
`K` positions, so the cardinal contribution is correctly `k^(s.card)`,
not `k^K`.

When `k=0`, only the empty domain admits a labelling. The empty pattern has
one empty function, consistently with `0^0=1`; nonempty domains contribute
zero. Thus the exact sparse cardinality remains valid. The forgetful-image
bound also remains valid: its image is then just the empty subset, rather
than every subset of permitted cardinality.

`BoundaryDescriptor` uses the condition `j.val+1<length`. With zero-based
positions and length equal to the number of positions, this means that
recorded deviations occur strictly before the final position. The empty
record requires final digit zero. The frozen `k>=2` condition supplies the
source domain in which that default is available. The proof of its
cardinality is a subtype bound and does not need to assume that all raw
descriptors occur in the source.

## Threshold and empty-space cases

Both `lowCount` and `tailWeight` filter the range `0,...,K`. If `h>K`, the
tail filter is empty and the low-count filter contains the entire range.
Neither theorem introduces `h<=K`. For `K=0`, the sole binomial term is
the empty choice. Both generating estimates include `z=1`; the denominator
is positive from the frozen bound on `z`.

The finite word type is the full function type from positions to the
alphabet. Empty positions give one empty word with product weight one.
If the alphabet is empty but positions are nonempty, the coordinate
normalization hypothesis cannot hold; the theorem does not assert such
weights exist. If both are empty, the normalization hypothesis is vacuous
and the single empty word is handled correctly.

The fibre theorem also permits `k=0`. When the exceptional domain is empty,
there is one empty labelling, so `k^0=1`. When it is nonempty, a labelling
map into the empty function type can exist only on an empty ambient class;
the finite fibre-sum identity enforces the corresponding cardinality zero.
The stated theorem requires no added nonemptiness hypothesis.

## Additional union-tail proof review

`box_word_mass` proves the exact product law for prescribed allowed digit
sets by rewriting the universal membership indicator as a product and
applying finite product/sum distributivity. This identity requires neither
positivity nor normalization and makes no stochastic assertion.

`exact_badPositions_mass_le` uses the bad digit set at selected positions
and its complement elsewhere. Coordinate nonnegativity permits multiplying
inequalities. The selected factors are at most `a`; complementary factors
are at most one by the frozen normalization. Consequently the exact-set
fibre has weight at most `a^(card S)`. The auxiliary statement does not need
an explicit `a>=0`: the coordinate bounds imply it whenever there is a
coordinate; when there are none, the claimed power is `a^0=1`. The main
exported theorem retains the frozen explicit nonnegative-`a` premise.

`sum_badSet_weights` is an exact finite identity obtained by partitioning
the powerset by subset cardinality. It automatically gives zero on both
sides for `h` larger than the number of positions. The final theorem uses
the fibrewise finite-sum identity for the exact bad-position map, so no
union has been counted without accounting for multiplicity.

The final two wrappers were reviewed separately. Removing exactly their
source text recovers the previously audited `WordMass.lean` hash
`d0bd9857afa76137fe4342737fc330c459b931489f2600bb221b9a1388057a83`.
Thus the remaining audited code is unchanged. Both wrappers are direct
applications of already reviewed theorems and preserve all frozen premises;
they also cover empty spaces, impossible thresholds, and `N=0`.

## Explicit boundaries of completion

The finite product law is the law of a single abstract word. Showing that
it is a row marginal of the fixed-column shuffle remains separate; there
is no assumption that different rows are independent.

The boundary and profile descriptor counts are counts of explicit finite
types. A source proof must still construct an injective encoding of each
actual source family, respecting its ambient indexing, stopping rule,
terminal fallback, and admissibility threshold. The modules and their
coverage reports expressly say that this has not been implemented.

The F20 fibre bound takes the labelled-fibre bound as its explicit input.
It does not prove a multinomial/entropy bound on each such fibre, and it
does not discard the required exceptional factor `k^|E|`.

The implementation reports correctly refrain from claiming the ordered
`chi -> 0`, `N -> infinity` limits, the `N^epsilon` class-count conclusion,
or the complete bad-profile reduction. Their completion statements are
appropriately limited to the finite declarations. The earlier union-tail
omission is now resolved; the source-family, model, and asymptotic gaps
listed above remain.
