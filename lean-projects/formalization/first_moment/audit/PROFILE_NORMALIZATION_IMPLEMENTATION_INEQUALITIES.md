# Profile normalization implementation: independent adversarial review

**Approve without corrections.** The implementation preserves the two definitions and all eight PN1–PN8 interfaces in the frozen contract. I found no premise drift, hidden positivity/regularity assumption, change to the real exceptional cutoff, or count/entropy normalization error.

Reviewed files:

```
FirstMomentModel/ProfileNormalization.lean
SHA-256 9bc0039bbdbe5f970ad07bdcf8063c5c2bb46067a80d35fd53e9f60c64f73971

PROFILE_NORMALIZATION_CONTRACT.md
SHA-256 a8e994b8628e96ceae51a10dd8fc30bb7c771b16f4c14429acc01807a781c49c
```

The implementation hash agrees with the completed module identified by the root agent. The root independently reports successful verification of both definitions and all eight theorems; this report is a source/interface audit, not a duplicate kernel-verification claim. I did not edit the module, contract, or earlier reviews.

## Exact inventory and interfaces

The module contains exactly two exported definitions and eight exported theorems, all in `InhomogeneousShuffle.FirstMoment.Model`. Its normalized-count helper is a proof-local `have` within PN5. No unreviewed exported helper, typeclass assumption, axiom, placeholder, or unsafe declaration appears.

| Item | Implementation check |
|---|---|
| `sourceCell` | Exact reviewed map `j ↦ finProdFinEquiv (timeClass j, P.classify (asProfile D j))`, into `Fin (R * P.cellCount)`. |
| `sourceGood` | Exact existential natural-digit bound and corresponding `P.IsGoodDigit` predicate. The real threshold remains arbitrary data. |
| PN1 `sourceGood_fin_iff` | Only explicit `D P chi j l`. The forward use of `hh` relies on proof irrelevance for the same finite digit; no hypothesis equating two different digits is inserted. |
| PN2 `exceptionalPositions_source_eq` | Exact `A P chi y z x hx` interface. Neither raw-pair nor prefix/stable membership is added. The proof splits on `j.val < x.length`, so no padded coordinate is identified with a list digit. |
| PN3 `digitCount_source_eq` | Exact additional `timeClass` and right-associated triple `a`. It proves equality of the literal counting filters, with the natural count divided by `Real.log D.N`. |
| PN4 `profileR_source_eq` | Exact PN2 data; a direct cardinality rewrite, with no alpha or time-cell argument. |
| PN5 `profileH_source_eq` | Exact PN3 data without `a`; right side is the original natural `typeEntropy` divided by `log D.N`. No regularity, sign-of-chi, positive-count, or compatible-count premise appears. |
| PN6 `profileWord_profileR_le` | Exact `A P chi alpha p`; no time-cell or route data. Its vector legality proof is literally derived from `stable_desc (admissiblePair_rawPair p.property.1) p.property.2.1`. |
| PN7 `profileWord_profileH_key` | Exact actual word, derived legality, route, and encoder data. It rewrites the existing exact key-count equality and PN5. |
| PN8 `profileFibre_card_le_rpow_profileH` | Exact actual realized fibre, real cast of `Nat.card`, and actual TimeProfile entropy exponent. No `Finite` assumption or fabricated word-to-key injection is introduced. |

## Finite index and filter checks

PN3 first proves a pointwise equivalence between the joint-cell equality and the conjunction of the time/simplex cell equalities using injectivity of `finProdFinEquiv`. It separately identifies the finite digit with its natural value using `Fin.ext_iff` and `legalVector_digit`. The displayed triple is exactly `(timeClass j, P.classify (asProfile D j), legalVector x hx j)`, with the right-associated product matching `TimeProfile.digitKey`.

Only coordinates satisfying `join.length <= j.val < x.length` contribute. The proof remains valid when the lower endpoint exceeds the upper endpoint; both filters are then empty. Arbitrary incompatible boundary words in PN2–PN5 are therefore harmless. No prefix relation is smuggled into the statements or proofs.

The PN5 outer sum is reindexed explicitly by

```
finProdFinEquiv : Fin R × Fin P.cellCount ≃ Fin (R * P.cellCount).
```

The digit index remains separate. The proof never silently identifies differently associated products such as `Fin ((R*m)*k)` and `Fin (R*(m*k))`.

## Zero-aware entropy normalization

The local `hnormalized` statement is precisely the reviewed schema for arbitrary natural counts and a positive real scale `L`. In the `n a l = 0` branch both weighted expressions simplify to zero before any logarithm quotient law is used. In the other branch, `hnpos` is obtained from the positive natural count and `htotal` follows by including that summand in the nonnegative cell total. Thus `Real.log_div` is applied only with nonzero numerator and denominator.

The normalization factor cancels through `div_div_div_cancel_right₀`, justified by `L > 0`. Finite distributivity then turns the weighted total-log term into `total * log total`, giving exactly

```
typeEntropy n / L.
```

There is no omitted `log L` contribution, factor of `log N`, or count-versus-frequency substitution. `L > 0` is derived for the actual application using `D.one_lt_N` and `Real.log_pos`. It is not a new theorem premise. Empty cell totals, empty outer dimensions, and the generic helper's empty alphabet case are all covered by the zero branches or empty sums.

## Real cutoff, fibre, and adversarial cases

PN6 divides the existing **real** cutoff `p.property.2.2` by the positive logarithm. It never introduces a natural-floor cutoff or assumes `alpha >= 0`. If alpha is negative the actual profile-word type is empty, so a theorem universally quantified over an element of it remains valid. Zero exceptional positions at alpha zero are handled without a special premise.

Arbitrary real chi is preserved. Goodness can depend on the digit and can classify zero representative probabilities as good for some threshold values; these identities only count positions and normalize count entropy, so they do not require a logarithm of a representative probability. No analytic regularity theorem is used in PN1–PN8.

PN7 and PN8 use the same fixed cell map, good predicate, alpha, route, and actual word in every occurrence. Route data are arbitrary, as frozen; no claim about the stochastic meaning of the four route values is made. The already proved PF4 supplies finite fibre cardinality with exceptional locations **and values** fixed. PN8 does not infer finiteness from `Nat.card = 0`, nor claim that all words inject into a coarse key. Empty/unrealized keys remain handled by the earlier fibre theorem; PN8 deliberately specializes to the key of its supplied actual word.

Terminal/stopped-root profiles have an empty continuation interval, so these same identities give zero entropy and zero exceptional proportion. Empty horizon or an empty time-cell codomain causes no failure; existence of the required time-class map already expresses the possible degenerate cases. No padded suffix digit enters any filter.

The module makes no new assertion that exact `cL` is constant in a class, that the horizon equals the time-profile floor, or that a stochastic density/localization estimate holds. Those obligations remain outside the frozen PN identity layer, as required.
