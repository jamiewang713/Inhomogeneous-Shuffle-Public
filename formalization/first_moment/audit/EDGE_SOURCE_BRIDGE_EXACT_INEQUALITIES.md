# Exact Edge-to-source identity candidate: adversarial sign-off

**Approve the single definition, ES1–ES10, and all five proof-local schemas without corrections.**

Reviewed exact candidate:

```
audit/EDGE_SOURCE_BRIDGE_STATEMENTS.md
SHA-256 a94791b91adafcc3ed3f2b347a7cdfa8d4fcc770ff69c0b9ad11f6243fb751ed
```

This review follows the independent definition-level reconstruction in `EDGE_SOURCE_BRIDGE_INEQUALITIES.md` and a comparison with the actual Edge Collision/Exponent, TimeProfile and stable numerical bridge declarations and authorized TeX finite block definitions. No implementation or new freeze was made by this audit, and no existing file was changed apart from this new report.

## Exact definition and interfaces

| Item | Decision and check |
|---|---|
| `prefixVector` | Approve. The literal restriction `legalVector x hx (Fin.castLE hx.1 t)` has the printed domain `Fin x.length` and codomain `Fin D.k`. It never reads the padded suffix. No new model field or bound is needed. |
| ES1 `prefixVector_digit` | Approve. `legalVector_digit` applies at the cast coordinate because its value is t.val and `t.isLt` gives `t.val<x.length`. |
| ES2 `prefixVector_word` | Approve. Edge prefixWord is `List.ofFn` of these natural digit values. Its length and every valid list entry equal those of x. This is actual list equality, including x=[]. |
| ES3 `prefixVector_legal` | Approve. The count array is exactly `(asCuts D).count`; after ES1 and the finite-coordinate value reduction, its positivity is precisely the corresponding field of hx. No full legal extension or positive zero-padding premise is added. |
| ES4 `prefixVector_ambient` | Approve. The actual prefix relation is printed and gives the required finite length cast. `digit_prefix` and ES1 equate the two natural digits; finite proof fields do not affect equality. Ambient legality is taken from `A.w_legal`. |
| ES5 `edge_ambientSizeExponent_eq` | Approve. Both sums range over exactly `A.w.length <= i < x.length`, use the same counts and selected digits, and preserve free `A.b`. No prefix relation is needed for this literal identity. |
| ES6 `edge_prefixMean_source_eq` | Approve. Both sides are N times the same product; this identifies Edge **prefixMean**, not Edge prefixMass, with the TimeProfile population mass. |
| ES7 `edge_prefixMean_expectedCount_eq` | Approve. ES6 and the existing `expectedCount_cylinder_eq` at the reflexive prefix give exactly the printed real cast of the actual weighted expected count. |
| ES8 `edge_ambientMeanError_eq` | Approve. Unfolding the signed error and rewriting ES7 at the actual ambient word yields the literal discrepancy. A.b remains arbitrary; neither positivity nor vanishing of the discrepancy is assumed. |
| ES9 `edge_columnPsiTwo_eq` | Approve. D is explicitly bound as specified. Each normalized count agrees with the profile probability, and real power two agrees with the natural square, including zero coordinates. |
| ES10 `edge_tailEdgeExponent_eq` | Approve. D and M are explicit, and no `M<=D.K` premise is needed. The extra upper bound in TimeProfile.positions follows from the finite column index itself. Both tails vanish when M>=D.K. |

All proposed common/explicit binders have the required types. In particular, ES9 and ES10 explicitly bind D and do not require a second implicit model. The count array is always the existing `(asCuts D).count`; no unrelated array, column-total axiom, or new normalization definition is introduced.

## Five local schemas

1. **Restriction and reconstruction — approve.** Fin.castLE preserves values. Every selected coordinate is within the actual legal list, so the old `legalVector_digit` theorem is sufficient. List.ofFn extensionality reconstructs exactly the list, and hx supplies only the required in-prefix positive counts.

2. **Prefix comparison and finite cL sum — approve.** ES4 uses `A.w <+: x`, rather than only its length inequality. In ES5, reindexing the filtered Fin x.length by its value gives `Finset.Ico A.w.length x.length` bijectively. Each summand is the same `Real.log ((D.N:ℝ)/(D.n i (digit x i):ℝ))`; no log splitting or unproved positive logarithm argument is needed.

3. **Product means and expected count — approve.** The map `t ↦ Fin.castLE hx.1 t` bijects Fin x.length with `positions D.K 0 x.length`. The one-column factor equals the existing source probability at the same coordinate and finite digit. N multiplies both sides exactly once. The old cylinder theorem already deals with the Full/Legal condition in `Riffle.Cylinder`; this supplement does not erase that condition or assume a probability-law identity.

4. **Natural square and real power — approve.** ES9 compares the whole sums of squares using the standard real-power identity at natural exponent two. It does not take logarithms of individual zero probabilities. Applying the same negated logarithm to equal sums requires no new positivity premise.

5. **Tail filter — approve.** For each j:Fin D.K, `j.val<D.K` is automatic. Hence the Edge filter and TimeProfile.positions agree for every natural M, and the source logarithmic denominator is exactly the same Real.log. This compares square-sum exponents; it does not turn the separate factorial collision-factor inequality into equality.

## Adversarial cases

- **Empty x:** the vector has empty domain and prefixWord returns []; both means in ES6 are N. This rules out the erroneous probability-versus-mean identification while confirming the stated one.
- **Empty horizon:** legal words necessarily have length zero. All tail sums are empty, and a column theorem with j:Fin 0 is vacuous. No positive K assumption is needed.
- **M>K:** ES10 remains true because both finite filters are empty. It never accesses the natural count array outside the horizon.
- **Zero piles:** hx guarantees positive counts only at selected prefix digits; zero counts elsewhere remain allowed in every theorem. The psi identity includes zero-square terms without any full-support hypothesis.
- **Different finite proof fields:** composed casts from ambient length to word length to horizon and the direct ambient-to-horizon cast have the same values. `Fin.ext` and proof irrelevance suffice; equality of those lengths is not required.
- **Ambient longer than x:** ES5 still holds with both sums empty and value A.b. The candidate correctly omits an unnecessary prefix premise there, while retaining the essential prefix premise in ES4.
- **Free b:** with empty ambient word, ES8 evaluates to `1-A.b`. Nothing forces b to equal the exact population exponent.
- **Weighted expectation:** ES7 is an equality of already defined deterministic finite quantities. It does not assert that a new graph law has that expectation or assume independent rows.

No scientific assumption has been added: the statements require no horizon-floor relation, source regularity, AlmostLike condition, profile cutoff, fluctuation bound, Gamma membership, source margin, density estimate, or graph-law equivalence. The intended later small-block application must still supply its own ambient prefix, signed-error bound, horizon transport, and graph semantics. Those integration obligations are accurately kept outside the ten proposed identities.

The exact candidate at the hash above is ready for freeze after comparison with the other independent reviews. I request no correction.
