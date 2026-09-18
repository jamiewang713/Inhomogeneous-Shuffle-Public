# Independent exact statement audit: profile normalization

Reviewed the complete proposed `audit/PROFILE_NORMALIZATION_STATEMENTS.md`, with SHA-256 `73ad2a8eed5d8938daab619c740891b806cb1ff48c01ec028d8d0774bf641f7d`.

**Decision: approve without corrections.** This approves exactly the two proposed definitions and PN1–PN8 for the root agent's separate freeze procedure. It does not freeze or implement them. No normalization Lean code was written.

For this audit I independently reread the authorized unified TeX's space-time digit profile and its within-class entropy statement, then inspected the actual `TimeProfile.Digits`, first-moment count/vector/fibre declarations, and the now-proved stable numerical adapters. The source profile counts are natural counts divided by `log N`, and the existing Lean entropy uses the same zero-aware positive-count convention. No additional mathematical source was used.

## Definitions, binders and index order

`sourceCell` has explicit model and partition data, an implicit natural `R`, and the exact finite map `Fin D.K → Fin (R * P.cellCount)`. `P.classify (asProfile D j)` has type `Fin P.cellCount`, so `finProdFinEquiv (timeClass j, P.classify (asProfile D j))` has the proposed type. The subsequent digit index has not yet been flattened at this stage. Thus the existing full profile key has count-vector dimension **`(R * P.cellCount) * D.k`**, matching the proposal exactly.

`sourceGood` has explicit `D`, `P`, and real `chi`, and no time-class parameter. The existential bound `ha : a < D.k` creates precisely the needed `Fin D.k` digit. It does not assume any positivity of the actual pile or representative, and the choice of proof `ha` does not affect the digit. The finite identities are valid for arbitrary real `chi`; setting it to `A.chi` is a later source specialization, not a premise needed by these identities.

The actual time-profile digit triple is right-associated:

```text
Fin R × (Fin P.cellCount × Fin D.k)
a.1    : Fin R
a.2.1  : Fin P.cellCount
a.2.2  : Fin D.k
```

This is exactly the type of `TimeProfile.digitKey` and the final binder of `TimeProfile.digitCount`. The corresponding outer entropy index is the pair `Fin R × Fin P.cellCount`. The proposal uses the correct flattening for each; it does not identify differently associated `Fin` products without an equivalence.

The displayed document abbreviations `cell`, `good`, `Xp`, `vp`, `np` and `keyp` introduce no exported definitions. They must be expanded exactly as specified. In particular the legal proof for the actual word is derived as

```text
(Riffle.stable_desc (Riffle.admissiblePair_rawPair p.property.1)
  p.property.2.1).1
```

Here `p.property.1` is the admissible pair, `p.property.2.1` is stable membership, and `p.property.2.2` is the literal real exceptional cutoff. No legality field or integer-budget condition is added to the domain.

## Exact theorem checks

| Interface | Audit result |
| --- | --- |
| PN1 `sourceGood_fin_iff` | The explicit data are exactly `D P chi j l`. The forward existential digit and `l` have the same natural value, hence are equal by `Fin.ext`; the reverse witness is `l.isLt`. There is no model/setup/time-class hypothesis missing. |
| PN2 `exceptionalPositions_source_eq` | Both sides are finsets of `Fin D.K`. On either filter's included interval, `j.val < x.length` allows the proved `legalVector_digit` to identify the two digits. The lower endpoint is the same join length on both sides. No prefix relationship between `y,z,x` is needed; inconsistent interval endpoints simply give empty filters. |
| PN3 `digitCount_source_eq` | The time-profile count is a real number, not a natural count. The numerator on the right is correctly cast to `ℝ` and divided by `Real.log (D.N : ℝ)`. `goodDigitCount` takes a joint-cell index and then a digit; `(finProdFinEquiv (a.1,a.2.1))` and `a.2.2` have those exact types. Equality of triple keys is equivalent to equality of all three coordinates. |
| PN4 `profileR_source_eq` | `TimeProfile.profileR` takes `N p X P chi v M`, with no time-class argument. The proposal has exactly that order and the correct real-cast exceptional cardinal. It follows immediately from PN2 and `TimeProfile.logScale`. |
| PN5 `profileH_source_eq` | Partially applying `goodDigitCount` as shown produces `Fin (R * P.cellCount) → Fin D.k → ℕ`, exactly the input required by the existing `typeEntropy`. The left uses the same `P`, `timeClass`, `chi`, join length and word length as PN3. The natural-count entropy is divided by a single `log N`, as required. |
| PN6 `profileWord_profileR_le` | There is no `timeClass`, route or extra legality binder. PN4 applies using the displayed derived stable-word legality proof. Dividing the unchanged real cutoff by positive `log N` gives the exact conclusion even for arbitrary real `alpha`; no nonnegativity premise on `alpha` is needed. |
| PN7 `profileWord_profileH_key` | The route has precisely the same actual `ProfileWord A (sourceGood D P chi) alpha` domain as the encoder. The key's natural counts are read with `c := R * P.cellCount`. `profileKeyCounts_encode` then gives exactly PN5's count function, with no count-compatibility hypothesis. |
| PN8 `profileFibre_card_le_rpow_profileH` | The `ProfileFibre` uses the actual realized encoder key and the same cell, goodness, cutoff and route data. The existing `profileFibre_card_le_rpow_entropy` supplies its cardinal bound without a finite-type premise. PN7 rewrites the exponent to the exact displayed `TimeProfile.profileH`. The base has type `ℝ`, so the exponentiation is real power. |

Unused section variables must not become accidental binders: PN1 has no setup or `R`; PN2 and PN4 have no `R`/time class; PN6 has neither `R`/time class nor route. This is already specified by the proposal and requires no correction.

## Zero-aware entropy calculation

The proposed proof-local identity is valid for arbitrary natural counts and `L > 0`, including empty index types. For one cell, write `t = ∑ l, n l`. If `n l > 0`, then `t > 0`, cancellation of `L` is justified, and the summand is

```text
(n l / L) * log(t / n l)
  = (n l * log t - n l * log(n l)) / L.
```

If `n l = 0`, the source conditional contributes zero and both weighted terms on the right are zero. Summing gives `(t * log t - ∑ l, n l * log(n l))/L`. A cell with `t=0` has every count zero; no invalid positive-total assertion is used there. Reindexing the outer pair sum by `finProdFinEquiv` yields precisely the existing `typeEntropy` on flattened joint-cell indices.

The required `L = log N > 0` follows from `D.one_lt_N`. No separate logarithm, positive-count, regular-partition, support, entropy-sign or compatible-count assumption is needed. The route's arbitrary subdivision of a fibre has no role in this algebra.

The existing `TimeProfile.profileH_source_formula` is not needed as an extra premise or as a means to import its regularity hypotheses. PN5 can use the literal definition of `TimeProfile.profileH`, PN3, and the reviewed finite algebra above. Its source meaning is consistent with the old sketch's positive-total/positive-count formula.

## Scope preserved

The source interval is exactly the extension after the boundary join, not merely after the ambient prefix. Empty extensions give zero counts, zero entropy and the previously proved fibre bound of at most one. Negative cutoffs are handled by the unchanged actual domain; no floor replacement is made. Zero-probability coordinates after the legal prefix do not enter any filter.

PN7 makes entropy constant on an encoded profile fibre through exact count equality. It does not make the exact size exponent `cL` constant, nor does it identify any edge-density quantity. No horizon, time-law, ambient approximation, error budget or stochastic premise is added. All earlier frozen definitions and theorem interfaces remain unchanged.

The proposed two-definition/eight-theorem batch is ready for the remaining independent approvals and separate freeze.
