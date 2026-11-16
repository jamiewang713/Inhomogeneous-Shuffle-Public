# Edge exponent to actual source data: independent adversarial design review

**Verdict:** the proposed finite identity layer is valid with the existing model assumptions. The one proposed definition is sound. The prefix-coordinate and ambient-mean comparison with a longer word require a genuine list-prefix relation; the ambient-size identity itself does not. The factor of N must distinguish Edge prefix probability from expected count. The tail-exponent identity is valid for every natural starting length, including lengths beyond K. No graph-law or density identity follows from these scalar identities.

This is a read-only pre-freeze review. I read the authorized TeX definitions of the ambient block, cL and cE (around lines 491–527), the actual Edge Collision/Exponent definitions and elementary conversion proofs, and the existing stable/numerical adapters. No code, statement, contract or definition was changed. Names suggested below are descriptive only; this report does not freeze new interfaces.

## The proposed definition

For the existing `D : Riffle.Model`, legal list `x` and `hx : Riffle.Legal D x`, define exactly

```
prefixVector x hx : Fin x.length -> Fin D.k :=
  fun t => legalVector x hx (Fin.castLE hx.1 t).
```

Equivalently, this is the composition specified by the parent. The proof `hx.1` is precisely `x.length <= D.K`. Every selected coordinate is before x.length, so `legalVector_digit` shows

```
(prefixVector x hx t).val = Riffle.digit x t.val.
```

No padded suffix digit enters this vector. Different proofs of legality or of the natural length inequality do not alter its values. The existing alphabet bound in hx justifies every finite digit; no all-piles-positive premise is necessary.

Throughout the identities below, use the **existing** count array

```
nD = (asCuts D).count,
nD j a = D.n j.val a.val.
```

No additional count-array definition is needed. `asCuts D` already carries the exact column-sum proof used by Edge estimates. No values of the unbounded natural function `D.n` outside `j<D.K` or `a<D.k` are used.

## Valid identity shapes and their exact premises

### 1. List reconstruction and legality

For arbitrary `x` and `hx : Legal D x`,

```
EdgeLocalization.prefixWord (prefixVector x hx) = x;
EdgeLocalization.legalPrefix nD hx.1 (prefixVector x hx).
```

The first is equality of actual lists of natural digits, not equality of padded full words. Prove equal lengths and equal entries using the finite digit identity above. The second follows from `(hx.2 t.val t.isLt).2` after the same digit rewrite. No source setup, ambient approximation, pair, retention, Gamma, stability, partition, or horizon-floor condition is relevant to these identities.

### 2. Actual ambient coordinate prefix

For `A : Riffle.Setup D`, legal x, and the **actual** prefix premise `hprefix : A.w <+: x`, the required statement is

```
forall t : Fin A.w.length,
  prefixVector x hx (Fin.castLE hprefix.length_le t) =
    prefixVector A.w A.w_legal t.
```

The cast to `Fin x.length` uses `hprefix.length_le`. On the left, prefixVector makes a second cast to `Fin D.K`; on the right, its cast uses `A.w_legal.1`. Equality of their natural values and proof irrelevance identify these finite coordinates. `Riffle.digit_prefix hprefix t.isLt` then identifies the digits.

This is the exact `hprefix` premise required by `EdgeLocalization.prefixMean_eq_rpow_ambientSizeExponent` and the coarse exponent bounds. A length inequality alone is insufficient. An equivalent interface can take `hx : x in Desc D A.w`, using its two fields, but should not treat Desc membership as mere legality.

### 3. Ambient-size exponent

For `A : Riffle.Setup D` and arbitrary legal x,

```
EdgeLocalization.ambientSizeExponent D.N nD hx.1
  A.w.length A.b (prefixVector x hx)
  = Riffle.cL A x.
```

No ambient-prefix premise is needed for this equality between the literal definitions. The Edge sum over `t : Fin x.length` with `A.w.length <= t.val` bijects with `Finset.Ico A.w.length x.length`. The summands are exactly `log(D.N / D.n t.val (digit x t.val))`; both sides retain the same free `A.b` and divide by `Real.log D.N`.

If `A.w.length > x.length`, both index sets are empty and both expressions equal A.b. Adding an ambient-prefix premise is unnecessary for this identity, although the later probabilistic exponent conversion separately needs it. Composing with the existing `cL_prefix_eq A x hx x List.prefix_rfl` yields the corresponding TimeProfile cL identity, with the same free b.

### 4. Prefix probability versus expected prefix count

For legal x, the exact equalities are

```
EdgeLocalization.prefixMass D.N nD hx.1 (prefixVector x hx)
  = TimeProfile.prefixWeight (asProfile D) (legalVector x hx) x.length;

EdgeLocalization.prefixMean D.N nD hx.1 (prefixVector x hx)
  = TimeProfile.prefixMass D.N (asProfile D) (legalVector x hx) x.length;

EdgeLocalization.prefixMean D.N nD hx.1 (prefixVector x hx)
  = (Riffle.expectedCount D (Riffle.Cylinder D x) : ℝ).
```

Only the latter two quantities include the factor D.N. Reindex the prefix product by `t ↦ Fin.castLE hx.1 t`; the target finite set is `TimeProfile.positions D.K 0 x.length`. Equality of one-column factors is a direct consequence of `asProfile_prob`, `Riffle.prob`, and `EdgeLocalization.singleFactor`, or directly `Cuts.profile_prob` and `asCuts`.

The third equality is already obtained from the second and the existing proved theorem

```
expectedCount_cylinder_eq x hx x List.prefix_rfl.
```

That existing theorem handles the legal full-word support in the cylinder definition. It is not permissible simply to erase the `Full` condition from `Riffle.Cylinder`; full words using zero piles have zero weight, and that fact has already been addressed by the proved adapter. No identification of the Edge finite probability law is required to equate these deterministic products and the already defined weighted expected count.

### 5. Signed ambient-mean error

For A alone, the valid literal identity is

```
EdgeLocalization.ambientMeanError D.N nD A.w_legal.1
  (prefixVector A.w A.w_legal) A.b
  = log((Riffle.expectedCount D (Riffle.Cylinder D A.w) : ℝ)) /
      log(D.N : ℝ) - A.b.
```

The same statement can be made for an arbitrary legal w and free real b without mentioning A. No mass approximation is needed for this equality, and no exact-size hypothesis should be added.

If one instead wants the right side written with `TimeProfile.prefixMass` of `legalVector x hx` at `A.w.length`, then `A.w <+: x` is needed. The existing `expectedCount_cylinder_eq x hx A.w hprefix` gives exactly that rewrite. With this prefix premise, the mass component of `AmbientApproximation` subsequently yields

```
abs(ambientMeanError) <= eb,
ambientMeanError <= eb.
```

The error is signed. It need not be nonnegative and is not generally zero. In particular, the combination with the coarse small exponent must retain `4*eb` after using this inequality.

### 6. Column psi and the complete tail

For each `j : Fin D.K`,

```
EdgeLocalization.columnPsiTwo D.N (nD j)
  = TimeProfile.psi (asProfile D j) 2.
```

Both sides are negative logarithms of the same sum of squared pile proportions. TimeProfile uses real powers at the real exponent 2, while Edge uses the natural power 2; the ordinary `Real.rpow_natCast` conversion identifies them, including a base of zero. No individual pile probability is assumed positive. Column normalization and D.N>1 ensure that at least one pile has positive probability when a semantic positivity fact is later needed, but equality of the logarithm arguments itself needs no newly stated support premise.

For **every** `M : ℕ`, with no condition `M<=D.K`,

```
EdgeLocalization.tailEdgeExponent D.N nD M
  = TimeProfile.cE D.N (asProfile D) M.
```

The Edge filter is `M <= j.val`; the TimeProfile filter additionally says `j.val < D.K`, which is already true because j belongs to `Fin D.K`. The column identity then rewrites every summand, and `TimeProfile.logScale` is exactly `Real.log D.N`. No legal word or padded vector is involved in this tail identity.

## Three invalid shortcuts, with concrete obstructions

1. **Dropping the factor N:** at the empty prefix, Edge prefixMass is 1, whereas Edge prefixMean, TimeProfile prefixMass, and the actual expected row count are D.N. Since the model has D.N>1, `Edge.prefixMass = TimeProfile.prefixMass` is false even at the root.

2. **Setting the ambient error to zero:** for the empty ambient word and arbitrary free b, prefixMean is D.N, so the signed ambientMeanError is `1-b`. Taking b=0 gives error 1. The source gives an approximate exponent, not an exact identity `b=log_N(expectedCount)`; the bridge must retain the discrepancy.

3. **Replacing prefix membership by a length bound:** take N=10, K=1, k=2 with column counts (6,4), ambient w=[0], and x=[1]. Both words are legal and have the same length. Their coordinate-prefix equality fails. Moreover cL(x)=b because the extension interval is empty, but `N^(cL(x)+ambientMeanError(w))=6` while the mean of x is 4. The actual prefix premise is therefore essential in the ambient mean/exponent conversion.

## Degenerate and dependent-index cases

- **Empty word:** prefixVector has empty domain, prefixWord returns [], prefixMass is 1, prefixMean is N, and the fixed lower endpoint in cL is handled by the finite empty range.
- **Empty horizon:** every legal word has length zero; all tail sums vanish and the prefix identities retain the same factors as above. A theorem quantified over a column `j : Fin 0` is vacuous; no positive-horizon premise should be inserted.
- **M=K or M>K:** both tail filters are empty, hence both tail exponents equal zero. Do not add an unnecessary bound on M to the tail identity, and do not read `D.n` beyond its modeled horizon.
- **Zero piles:** zero counts outside the legal prefix remain allowed. Legality guarantees positive counts only at the selected prefix digits. The column and tail identities include all zero-pile terms without logarithmic division by a selected zero mass.
- **Proof-dependent casts:** `Fin.castLE` compositions and differing proofs of `w.length<=D.K` may require `Fin.ext` or proof irrelevance. No equality of the natural lengths themselves is necessary. The finite coordinate value, not its proof field, determines the count-array entry.
- **Free ambient b and arbitrary A.w length:** the size identity preserves A.b even if A.w is not a prefix of x. The later coordinate or ambient mean identity must supply the separate prefix relation where needed.
- **No time horizon premise:** these are finite identities for arbitrary D.K. The equality `D.K=horizonDepth D.N T` belongs to the later source estimate application and is not required or supplied here.

## Integration boundary

These identities can make the already proved Edge scalar exponent bounds use the same cL, cE and signed mean discrepancy as the source numerical layer. They do not equate Edge's finite matrix sample space with another package's sample space, identify its finite law with `TimeProfile.fixedCountMeasure`, identify sorted-row graph definitions, or reconcile global versus ambient-recentered edge locations. Such assertions must be proved separately if the final density theorem is stated through a different graph/law interface. No graph-law equality, row independence, or anti-concentration premise is assumed in this proposed identity layer.

## Read source hashes

```
Edge Collision/Model.lean
43c19b97e925dee9186d496560cdf143c89b76279ba4f36420e84401a4b4e3dd

Edge Exponent/Model.lean
db39dbcc02675a03461380ce8afdbc2c798268285ceb52e9f2401fbd55869106

FirstMomentModel/StableNumericalBridge.lean
a1485441183054eba94a887919725e6da0bba49f549500a540c24526d4b3de7f

TimeProfile/Ambient.lean
75d4558ff24fa1fc18cd09b0b1c2d0ea33140195317686e963b36038226eeea8
```
