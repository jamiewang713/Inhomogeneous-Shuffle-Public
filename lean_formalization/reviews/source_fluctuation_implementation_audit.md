# Independent S04–S05 implementation audit

Verdict: **approved**. `RiffleProfiles/SourceFluctuation.lean` implements
the exact S04 and S05 statements in `FROZEN_SOURCE_ADAPTERS.md`, using
F10/F11 and the existing, checked TimeProfile definitions. I found no
added premise, weakened conclusion, omitted crossing factor, invalid
zero/log conversion, or discarded ambient error.

Audited file SHA256:
`625487cf482a35c6d1f23ed2f1323bbca21ba53324de8d2e7ee3d98bd495c17e`.

This was a read-only source audit. The coordinator had already reported
successful compilation with warnings treated as errors and is handling
the combined library/kernel dependency audit. I did not edit Lean code
or repeat that build. The declaration and proof checks below are my
independent audit, not a substituted compilation claim.

## Frozen statement correspondence

| Frozen item | Declaration | Frozen premises preserved |
|---|---|---|
| S04 / F10 | `source_sideMaximum_ge_prefixMass` (line 39) | `2 ≤ N`, `0 < chi`, `w ≤ v`, `v ≤ K`, `LegalPrefix p x v`, a member `j` of `positions K w v`, and `chi ≤ side (p j) (x j)` |
| S05 / F11 | `source_fluctuation_comparison` (line 84) | `2 ≤ N`, `0 < chi`, `w ≤ v`, `v ≤ K`, `LegalPrefix p x v`, and `Crossings p x w v chi`; `b` remains arbitrary real |

The underscored S04 binder names `_hwv` and `_hvK` retain their frozen
propositions even though the witness already supplies the ordering
needed in its proof. The arbitrary `side` function is not restricted by
global nonnegativity, an upper bound, or any relation to the selected
digit mass. There is no new assumption on the alphabet size, no full
support requirement, and no extra ambient approximation hypothesis.

Both conclusions match the frozen expressions exactly. S05 coerces the
entire real expression, after division by two, into `WithBot ℝ`.
Its ambient discrepancy remains
`Real.log (prefixMass N p x w) / logScale N - b`.

## Product factorization and S04

The private helper `prefix_mass_split` (line 20) is the product identity
already included in the independently reviewed S04 proof plan. For
`a ≤ b`, it proves that positions `0..b` are the disjoint union of
`0..a` and `a..b`, applies the finite product-over-union identity, and
reassociates the natural scaling factor `N`. It introduces no new model
definition or axiom and needs neither legality nor `b ≤ K`.

For the witness `j`, set
`earlier = prefixMass N p x j.val`. Position membership gives
`w ≤ j.val < v`. Splitting at `w` identifies the defined side mass with
`earlier * side (p j) (x j)`. Multiplication of the crossing bound by
this earlier mass gives the exact F10 side premise.

The continuation split is at `j.val`, and its product ranges over
`positions K j.val v`. The source definition is
`j.val ≤ i.val ∧ i.val < v`; therefore **the selected factor at the
crossing column itself is included**. This is the exact remaining
prefix product. Each selected factor is in `[0,1]` by simplex membership.
The invocation of `side_mass_ge_continuation` therefore yields
`chi * prefixMass N p x v ≤ sideMass N p x w side j`.

The proof derives positivity before any clipping conversion:

- legality up to `v` restricts to legality before `j.val`, giving
  positive `earlier` from `N ≥ 2`;
- legality up to `v` gives positive full prefix mass;
- positive `chi` makes the lower bound strictly positive, hence the
  witness side mass is strictly positive;
- only then is `Real.coe_toNNReal` applied, with its nonnegativity proof,
  to identify the clipped witness mass with the original real mass.

`Finset.le_sup` uses the same witness membership to place that mass
under the existing finite `sideMaximum`. Negative side values at other
positions are irrelevant: they may be clipped by the definition without
affecting domination of this positive witness. The proof does not assume
all side values are nonnegative.

## Positivity, square roots, and S05

The existing `Crossings` conjunction supplies the left and right
witnesses. S04 is applied separately with `leftProbability` and
`rightProbability`; no distinctness of the witnesses is imposed.
Legality and `N ≥ 2` give positive terminal prefix mass. Its positive
multiple by `chi` is below each side maximum, so both maxima are
strictly positive.

The private helper `logExponent_sqrt_of_pos` (line 76) is the reviewed
square-root/log conversion. Its positive argument guarantees
`Real.sqrt z > 0`, selects the nonzero branch of `logExponent`, and
uses `Real.log_sqrt`. The resulting real value is
`Real.log z / (2 * logScale N)`. It does not evaluate the zero branch as
a finite number or assume away a possible bottom value without proof.
The helper does not require positive `logScale N` because it is an
identity of totalized real divisions; the inequality uses positivity
of that scale separately from `logScale_pos hN`.

With all five real positivity conditions established, the call to
`fluctuation_log_comparison` is precisely frozen F11. Rewriting the
existing `cF` by the two helper identities gives the minimum of two
real coercions. `WithBot.coe_min` and `WithBot.coe_le_coe` transport the
real inequality through the order-preserving real embedding, preserving
the intended order and the outer coercion.

Finally, `TimeProfile.cL_exact_mass_exponent` is instantiated with
terminal depth `v` and ambient depth `w`, using the original `hN`,
`hwv`, `hvK`, and `hlegal`. Its exact identity rewrites the left side;
ordinary real arithmetic gives the displayed S05 expression. The proof
never replaces the ambient discrepancy by zero or bounds it by an
unstated approximation. The parameter `b` cancels only through that
exact identity.

## Edge cases, dependencies, and scope

Empty crossing ranges and `w = v` cannot supply the S04 witness or
S05 crossings, so the statements correctly remain conditional in those
cases. At `j.val = 0`, the earlier product is empty and has mass `N`,
as required. A witness at the last allowed column still contributes its
selected factor to the continuation. Zero probabilities outside the
selected legal prefix are allowed throughout.

The implementation depends on the existing finite F10/F11 proofs,
simplex coordinate bounds, positive legal prefix masses, the exact
ambient mass-exponent identity, and trusted finite-sum/product, order,
square-root, and logarithm facts. No `axiom`, `sorry`, or `admit` command
occurs in the audited file. No model definition is redefined.

This audit uses the compatible Ambient dependency with SHA256
`329493e3ef2d0b03a12c1beba07117e93383cbe572984bf79f323866b7c507d2`,
whose source declaration preservation was separately verified. The
approved result is a deterministic prefix-mass and defined exponent
comparison. It does not establish a shuffle expectation, variance,
anti-concentration result, asymptotic estimate, or missing analytic
bridge, and the module documentation does not claim any of those.
