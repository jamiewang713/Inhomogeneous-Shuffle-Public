# Actual profile normalization: independent algebra reconstruction

This is a pre-freeze proposal, not an implementation or a modification of any existing contract. It compares the authorized unified TeX's space-time profile definition (lines 700–754) and the class aggregation passage (lines 1872–1876) with the current `ProfileClasses`, `ProfileFibreEntropy`, `FirstMoment.Entropy`, and `TimeProfile.Digits` definitions. The frozen stable/numerical adapters are used with their existing interfaces.

## Outcome

The required identities are exact. No regularity hypothesis, approximation error, positivity premise on `alpha`, positive cell-total assumption, or assumed count compatibility is needed. Positivity of the scale `log N` is already a consequence of `Riffle.Model.one_lt_N`.

Two new adapter definitions suffice. A compact public interface can consist of the seven results below; the scalar entropy normalization and finite reindexing facts can remain proof-local. Some of the seven are short composition corollaries, but keeping the actual-word cutoff, encoded entropy, and fibre bound explicit avoids leaving an integration assertion informal.

## Exact adapters

Work in `InhomogeneousShuffle.FirstMoment.Model`, with implicit `{D : Riffle.Model}` and `{R : ℕ}`.

**D1. `sourceCell`**

```lean
(P : TimeProfile.BorelPartition D.k) (timeClass : Fin D.K → Fin R) :
  Fin D.K → Fin (R * P.cellCount)
```

Its exact value is

```lean
fun j => finProdFinEquiv (timeClass j, P.classify (asProfile D j))
```

**D2. `sourceGood`**

```lean
(A : Riffle.Setup D) (P : TimeProfile.BorelPartition D.k) :
  Fin D.K → ℕ → Prop
```

Its exact value is

```lean
fun j a => ∃ ha : a < D.k,
  P.IsGoodDigit A.chi (asProfile D j) ⟨a, ha⟩
```

The existential proof is needed only to pass a natural digit to the existing `Fin D.k` predicate. It does not change goodness of an actual legal digit; invalid natural digits are not good. No new partition, representative, or alternate threshold is introduced: `IsGoodDigit` is literally the source test `2 * A.chi < prob (P.rep (P.classify ...)) digit`.

The joint cell is `Fin (R * P.cellCount)`. Consequently the existing profile-key count dimension is **`(R * P.cellCount) * D.k`**. The outer cell flattening and the later cell/digit flattening are separate applications of `finProdFinEquiv`. One must not identify different flattened triple encodings by definitional equality or silently swap the time and simplex indices.

## The finite comparison

Fix arbitrary words `y,z`, a legal word `x`, and write `v = (Riffle.join y z).length`, `M = x.length`, `X = legalVector x hx`, and `L = Real.log (D.N : ℝ)`. Here `L > 0` is derived from `D.one_lt_N`.

For every `j : Fin D.K` with `j.val < M`, frozen SN2 gives `(X j).val = Riffle.digit x j.val`. Therefore

`sourceGood A P j (Riffle.digit x j.val) ↔ P.IsGoodDigit A.chi (asProfile D j) (X j)`.

To prove the forward direction, the existential `Fin` witness and `X j` have equal values, hence are equal by `Fin.ext`. For the reverse direction use the actual alphabet bound from `hx` and the same equality. The proof term in the `Fin` constructor is immaterial.

Both exceptional-support definitions now filter exactly the same set:

`{j : Fin K | v ≤ j.val ∧ j.val < M ∧ not good(j,X j)}`.

The time-profile side expresses this as a filter of `positions K v M`; the model side is one filter of `Finset.univ`. Extensionality and the good-digit equivalence identify them. No assumption that `y,z` are boundaries, or even that their join prefixes `x`, is necessary for this literal identity. If `v > M`, both supports are empty.

For the good count in a fixed `(q,i,l)`, membership on the time-profile side is the same range and goodness conjunction plus

`timeClass j = q`, `P.classify (asProfile D j) = i`, and `X j = l`.

On the model side the first two equalities are equivalent to

`sourceCell P timeClass j = finProdFinEquiv (q,i)`

by injectivity of the equivalence; the third is equivalent to the equality of their natural values. Hence the two finite filters have identical cardinalities. The only distinction between `digitCount` and `goodDigitCount` is division of that natural cardinality by `L`.

This is precisely the zero-based form of the source's `s log N < j ≤ u log N`: the interval here is `[join.length,x.length)`. It does not extend the count to the ambient prefix or the exceptional digits.

## Zero-aware entropy normalization

The required scalar helper is a finite algebraic identity. It can stay local to the entropy proof:

For any natural `k`, natural counts `n : Fin k → ℕ`, real `L > 0`, and `S = ∑ l, n l`,

```text
∑ l, if 0 < (n l : ℝ) / L then
       ((n l : ℝ) / L) *
         log (((S : ℝ) / L) / ((n l : ℝ) / L))
     else 0
 = ((S : ℝ) * log (S : ℝ) - ∑ l, (n l : ℝ) * log (n l : ℝ)) / L.
```

No total-count compatibility or nonempty alphabet is assumed. A Lean-shaped helper interface, if a public helper is desired before freezing, is:

```lean
{k : ℕ} (n : Fin k → ℕ) (L : ℝ) (hL : 0 < L) :
  (∑ l : Fin k,
    if 0 < (n l : ℝ) / L then
      ((n l : ℝ) / L) *
        Real.log (((((∑ m : Fin k, n m) : ℕ) : ℝ) / L) /
          ((n l : ℝ) / L))
    else 0) =
    (((((∑ m : Fin k, n m) : ℕ) : ℝ) *
        Real.log (((∑ m : Fin k, n m) : ℕ) : ℝ) -
      ∑ l : Fin k, (n l : ℝ) * Real.log (n l : ℝ)) / L)
```

The reconstruction is as follows.

1. If `n l = 0`, the guarded term is zero, as are the two terms in `(n l) * log S - (n l) * log (n l)`. No logarithmic quotient expansion is used in this case.
2. If `n l > 0`, then `S ≥ n l > 0`. Both logarithm arguments needed for `log(S/n l) = log S - log(n l)` are nonzero. Cancel the common nonzero `L` in the ratio and expand. The term is exactly `((n l) * log S - (n l) * log(n l)) / L`.
3. Sum over all digits; distribute the finite sum and factor the common `log S` and `1/L`. Cast the natural sum into the real sum. This yields the displayed formula.

Thus the all-zero cell contributes zero on both sides. In particular `k=0`, `S=0`, and arbitrary zero entries require no extra premise. The helper's positive-scale premise is a derived fact in every model application, not an added scientific hypothesis. Allowing an arbitrary negative scale would make the positive-count guards wrong, so cancellation alone is not sufficient without recording the derived sign.

For each joint cell `a = (q,i)`, PN2 below gives `digitTotal(a) = (∑ l, n_a,l) / L`. Applying the helper to that cell and reindexing the outer sum through `finProdFinEquiv : Fin R × Fin P.cellCount ≃ Fin (R * P.cellCount)` gives

`profileH = typeEntropy(goodDigitCount) / L`.

The source definition's total-weighted Shannon entropy agrees with this expression, including zero cells. The already proved `TimeProfile.profileH_source_formula` is useful documentation of that interpretation, but its exported signature carries regularity and legality premises that are unnecessary here. Use the literal zero-aware `profileH` definition and the elementary identity above, rather than introducing those premises solely to invoke that theorem.

## Proposed seven public theorem interfaces

The names below are proposals. Their displayed binders and conclusions are the exact proposed content; no new declaration has been added.

### PN1. `exceptionalPositions_source_eq`

```lean
(A : Riffle.Setup D) (P : TimeProfile.BorelPartition D.k)
(y z x : Riffle.Word) (hx : Riffle.Legal D x) :
  exceptionalPositions A (sourceGood A P) y z x =
    TimeProfile.exceptionalPositions (asProfile D) (legalVector x hx)
      P A.chi (Riffle.join y z).length x.length
```

This is the filter equality proved above. It retains the actual positions rather than only their cardinality.

### PN2. `digitCount_source_eq`

```lean
(A : Riffle.Setup D) (P : TimeProfile.BorelPartition D.k)
(timeClass : Fin D.K → Fin R) (y z x : Riffle.Word)
(hx : Riffle.Legal D x) (q : Fin R) (i : Fin P.cellCount)
(l : Fin D.k) :
  TimeProfile.digitCount D.N (asProfile D) (legalVector x hx)
      P timeClass A.chi (Riffle.join y z).length x.length (q, i, l) =
    (goodDigitCount A (sourceCell P timeClass) (sourceGood A P)
      y z x (finProdFinEquiv (q, i)) l : ℝ) / Real.log (D.N : ℝ)
```

This identifies the exact source normalized count. The finite cell-total identity needed for entropy is then a proof-local finite-sum consequence.

### PN3. `profileH_source_eq_typeEntropy`

```lean
(A : Riffle.Setup D) (P : TimeProfile.BorelPartition D.k)
(timeClass : Fin D.K → Fin R) (y z x : Riffle.Word)
(hx : Riffle.Legal D x) :
  TimeProfile.profileH D.N (asProfile D) (legalVector x hx)
      P timeClass A.chi (Riffle.join y z).length x.length =
    typeEntropy
      (goodDigitCount A (sourceCell P timeClass) (sourceGood A P) y z x) /
      Real.log (D.N : ℝ)
```

PN2, the scalar normalization, and outer joint-cell reindexing prove this equality. No approximation or entropy inequality is involved.

### PN4. `profileR_source_le_iff`

```lean
(A : Riffle.Setup D) (P : TimeProfile.BorelPartition D.k)
(y z x : Riffle.Word) (hx : Riffle.Legal D x) (alpha : ℝ) :
  TimeProfile.profileR D.N (asProfile D) (legalVector x hx)
      P A.chi (Riffle.join y z).length x.length ≤ alpha ↔
    ((exceptionalPositions A (sourceGood A P) y z x).card : ℝ) ≤
      alpha * Real.log (D.N : ℝ)
```

Unfold `profileR`, use PN1, and apply division by positive `L`. This works for arbitrary real `alpha`. It is the source real cutoff itself, not an equivalence with the rounded natural budget. If `alpha < 0`, the two inequalities both fail, even for empty exceptional support.

For the last three statements write the following only as **local notation in their explanations**, not as additional adapter definitions:

```text
cell = sourceCell P timeClass
good = sourceGood A P
hx(p) = (Riffle.stable_desc
           (Riffle.admissiblePair_rawPair p.property.1)
           p.property.2.1).1
H(p) = TimeProfile.profileH D.N (asProfile D)
         (legalVector p.val.2.2 hx(p)) P timeClass A.chi
         (Riffle.join p.val.1 p.val.2.1).length p.val.2.2.length
```

The exact types may introduce `hx(p)` with a `let` expression. It is a proof derived from the actual `ProfileWord`, not an extra argument.

### PN5. `profileH_encode_eq_typeEntropy`

```lean
(A : Riffle.Setup D) (P : TimeProfile.BorelPartition D.k)
(timeClass : Fin D.K → Fin R) (alpha : ℝ)
(route : ProfileWord A (sourceGood A P) alpha → Fin 4)
(p : ProfileWord A (sourceGood A P) alpha) :
  let hx : Riffle.Legal D p.val.2.2 :=
    (Riffle.stable_desc (Riffle.admissiblePair_rawPair p.property.1)
      p.property.2.1).1
  TimeProfile.profileH D.N (asProfile D) (legalVector p.val.2.2 hx)
      P timeClass A.chi (Riffle.join p.val.1 p.val.2.1).length
      p.val.2.2.length =
    typeEntropy (profileKeyCounts (c := R * P.cellCount)
      (encodeProfile A (sourceCell P timeClass) (sourceGood A P)
        alpha route p)) / Real.log (D.N : ℝ)
```

Apply PN3 and the already proved `profileKeyCounts_encode`. This shows exactly how the previously frozen key entropy is the numerical source entropy. Neither the route nor exceptional labels add a free entropy term.

### PN6. `profileWord_sourceR_le`

```lean
(A : Riffle.Setup D) (P : TimeProfile.BorelPartition D.k)
(alpha : ℝ) (p : ProfileWord A (sourceGood A P) alpha) :
  let hx : Riffle.Legal D p.val.2.2 :=
    (Riffle.stable_desc (Riffle.admissiblePair_rawPair p.property.1)
      p.property.2.1).1
  TimeProfile.profileR D.N (asProfile D) (legalVector p.val.2.2 hx)
      P A.chi (Riffle.join p.val.1 p.val.2.1).length p.val.2.2.length ≤ alpha
```

PN4 converts `p.property.2.2` directly. The real cutoff must not be replaced by the integer floor bound. When an actual `p` exists, `alpha ≥ 0` can be derived later from this inequality and the nonnegative cardinal; it is not a hypothesis of the theorem.

### PN7. `profileFibre_card_le_sourceH`

```lean
(A : Riffle.Setup D) (P : TimeProfile.BorelPartition D.k)
(timeClass : Fin D.K → Fin R) (alpha : ℝ)
(route : ProfileWord A (sourceGood A P) alpha → Fin 4)
(p : ProfileWord A (sourceGood A P) alpha) :
  let hx : Riffle.Legal D p.val.2.2 :=
    (Riffle.stable_desc (Riffle.admissiblePair_rawPair p.property.1)
      p.property.2.1).1
  (Nat.card (ProfileFibre A (sourceCell P timeClass) (sourceGood A P)
      alpha route
      (encodeProfile A (sourceCell P timeClass) (sourceGood A P)
        alpha route p)) : ℝ) ≤
    (D.N : ℝ) ^
      (TimeProfile.profileH D.N (asProfile D) (legalVector p.val.2.2 hx)
        P timeClass A.chi (Riffle.join p.val.1 p.val.2.1).length
        p.val.2.2.length)
```

Apply the existing `profileFibre_card_le_rpow_entropy` to this exact encoded key and rewrite the exponent using PN5. The existing `profileFibre_finite` already proves that this is an actual finite cardinality, without a caller-supplied finite-domain instance.

An equally valid formulation can take an arbitrary key and a representative `p : ProfileFibre ... key`, then rewrite by `p.property`; it is slightly heavier in dependent notation. No actual source `H(p)` can be assigned to an unrealized key without choosing a nonexistent representative. Such keys remain fully covered by the already frozen arbitrary-key entropy bound and have empty fibres. The proposed PN7 is exactly the realized class estimate needed in aggregation.

## Edge cases and proof boundaries

- A zero good count contributes zero even if its representative probability is zero. The normalization uses only counts and never logs a representative probability.
- An empty extension, including a terminal singleton with `x = join y z`, has zero counts and zero exceptional support. Then `profileH = 0`, and PN7 bounds its realized fibre by `N^0 = 1`, consistent with fixed boundaries and fixed length.
- `K=0` is covered by empty finite filters. `R=0` needs no additional exclusion: a function `Fin K → Fin 0` can exist only in the corresponding empty-domain case. The equivalence and finite sums handle empty types. No `R>0` or `P.cellCount>0` premise is needed.
- No boundary assumptions on `y,z` are needed in PN1–PN4. They occur only in the already existing actual `ProfileWord` of PN5–PN7, from which legality is derived rather than assumed again.
- Time labels may be any given `timeClass`. Matching them to the source mesh is the caller's choice of that map; these identities do not need a horizon relation, mesh regularity, or measurability in time.
- The existing refined encoder fixes exceptional **positions and digit values**. PN7 uses that precise fibre. Replacing it by the fibre of coarse normalized counts or exceptional positions alone would invalidate the already proved restriction injection and require an additional combinatorial factor.
- The identity proves constancy of `profileH` on an actual encoded fibre. It does not assert constancy of exact `cL`, exceptional costs, or other quantities not fixed by the descriptor.
- None of these finite identities supplies edge density, endpoint localization, an AlmostLike comparison, or a conditional shuffle law. Their role is to attach the established exact profile-fibre bound to the same `H` and exceptional cutoff used by the numerical theorems.

No obstruction was found. The minimum genuine proof ingredients are guarded actual-digit agreement, finite filter extensionality, the two finite product-index equivalences, finite-sum normalization, and the zero-aware logarithmic identity. They introduce no new model assumptions.
