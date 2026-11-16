# Profile normalization: adversarial analysis and proposed finite interfaces

This is an independent pre-freeze review of the authorized article's space-time profile definition and class-entropy passage, together with the current `TimeProfile.Digits`, `DigitEstimates`, `FirstMoment.Entropy`, `ProfileClasses`, and `ProfileFibreEntropy` definitions. No Lean implementation, assumption, or frozen contract was changed.

**Conclusion:** the exact identification is valid. The needed bridge is finite counting and real algebra. It requires no regularity, AlmostLike, time-mesh, variational-margin, count-compatibility, nonempty-cell, or full-word-positivity premise. Legality of the list word suffices for its digit-vector comparison; the model already provides `log N>0`. The joint cell map and the original real exceptional cutoff must be preserved exactly.

## Literal quantities being identified

For one joint time/simplex cell `a=(q,i)`, let `m[a,l]` be its natural number of good positions carrying digit `l`, let `M[a]=sum_l m[a,l]`, and put `L=log(D.N)>0`. The current definitions give

- `TimeProfile.digitCount ... (q,i,l) = m[a,l]/L`;
- `TimeProfile.digitTotal ... (q,i) = M[a]/L`;
- `TimeProfile.profileR ... = (#exceptional positions)/L`;
- `TimeProfile.profileH ... = sum_a sum_l, if m[a,l]/L>0 then (m[a,l]/L)*log((M[a]/L)/(m[a,l]/L)) else 0`.

The existing natural-count entropy is

`typeEntropy m = sum_a (M[a]*log(M[a]) - sum_l m[a,l]*log(m[a,l]))`.

Consequently the exact result is `profileH = typeEntropy m / log(D.N)`, and PF4's power becomes exactly `(D.N : ℝ)^profileH`. There is no additive error, extra exceptional-digit factor, or extra logarithmic term.

## Two proposed definitions

The names below are suggestions in `InhomogeneousShuffle.FirstMoment.Model`. They use the already reviewed stable/numerical adapter definitions `asProfile` and `legalVector`, without changing them.

**N-D1: joint cell map.**

```lean
sourceProfileCell {D : Riffle.Model} {R : ℕ}
    (P : TimeProfile.BorelPartition D.k)
    (timeClass : Fin D.K → Fin R) : Fin D.K → Fin (R * P.cellCount) :=
  fun j => finProdFinEquiv (timeClass j, P.classify (asProfile D j))
```

**N-D2: natural-digit good predicate.**

```lean
sourceProfileGood {D : Riffle.Model}
    (A : Riffle.Setup D) (P : TimeProfile.BorelPartition D.k) :
    Fin D.K → ℕ → Prop :=
  fun j a => ∃ ha : a < D.k,
    P.IsGoodDigit A.chi (asProfile D j) ⟨a, ha⟩
```

For `l : Fin D.k`, the proof-local identity

`sourceProfileGood A P j l.val ↔ P.IsGoodDigit A.chi (asProfile D j) l`

uses the witness `l.isLt` and `Fin.ext`; the choice of a proof of the bound is irrelevant. On list positions below their legal length, `legalVector_digit` makes this precisely the source predicate. Values `a≥D.k` give false in N-D2, but no such digit occurs at a counted position of a legal word. There is no assertion that goodness is independent of the selected digit.

## Four core exact interfaces

Below `{D : Riffle.Model}` and, where used, `{R : ℕ}` are implicit. `A`, `P`, `timeClass`, the three words, and the legal-word proof are the only data. The words `y,z` need not themselves be legal, compatible, or boundary words for these literal identities: only their join length appears, and a reversed/empty interval contributes zero. Actual ProfileWord applications supply the stronger source facts automatically.

**N1: exact exceptional support.**

```lean
sourceExceptionalPositions_eq
    (A : Riffle.Setup D) (P : TimeProfile.BorelPartition D.k)
    (y z x : Riffle.Word) (hx : Riffle.Legal D x) :
  exceptionalPositions A (sourceProfileGood A P) y z x =
    TimeProfile.exceptionalPositions (asProfile D) (legalVector x hx)
      P A.chi (Riffle.join y z).length x.length
```

This is filter extensionality on the same `Fin D.K` positions. No natural-to-Fin interval cardinality theorem or positivity of a cell count is needed.

**N2: exact normalized digit count.**

```lean
sourceDigitCount_eq
    (A : Riffle.Setup D) (P : TimeProfile.BorelPartition D.k)
    (timeClass : Fin D.K → Fin R)
    (y z x : Riffle.Word) (hx : Riffle.Legal D x)
    (q : Fin R) (i : Fin P.cellCount) (l : Fin D.k) :
  TimeProfile.digitCount D.N (asProfile D) (legalVector x hx)
      P timeClass A.chi (Riffle.join y z).length x.length (q, i, l) =
    (goodDigitCount A (sourceProfileCell P timeClass) (sourceProfileGood A P)
      y z x (finProdFinEquiv (q, i)) l : ℝ) / Real.log (D.N : ℝ)
```

The equality of the counted sets is stronger than equality of the normalized cardinalities and can be proved locally. In `TimeProfile.digitKey`, the triple is right-associated: `Fin R × (Fin P.cellCount × Fin D.k)`. In the profile key the cell is first compressed to `Fin (R*P.cellCount)`, then paired with the digit. Use the stated nested equivalences rather than treating triple products as definitionally equal.

**N3: exact real cutoff equivalence.**

```lean
sourceProfileR_le_iff
    (A : Riffle.Setup D) (P : TimeProfile.BorelPartition D.k)
    (y z x : Riffle.Word) (hx : Riffle.Legal D x) (alpha : ℝ) :
  TimeProfile.profileR D.N (asProfile D) (legalVector x hx)
      P A.chi (Riffle.join y z).length x.length ≤ alpha ↔
    ((exceptionalPositions A (sourceProfileGood A P) y z x).card : ℝ) ≤
      alpha * Real.log (D.N : ℝ)
```

N1 and the existing definition immediately give the exact `profileR = card/log N` identity inside this proof. Division by positive `log N` yields N3 for **every real alpha**, without adding `0≤alpha`. Applying its reverse implication to `p.property.2.2` supplies the actual `profileR≤alpha` input for a `ProfileWord`.

**N4: natural-count entropy normalization.**

```lean
sourceProfileH_eq_typeEntropy
    (A : Riffle.Setup D) (P : TimeProfile.BorelPartition D.k)
    (timeClass : Fin D.K → Fin R)
    (y z x : Riffle.Word) (hx : Riffle.Legal D x) :
  TimeProfile.profileH D.N (asProfile D) (legalVector x hx)
      P timeClass A.chi (Riffle.join y z).length x.length =
    typeEntropy
      (goodDigitCount A (sourceProfileCell P timeClass) (sourceProfileGood A P)
        y z x) / Real.log (D.N : ℝ)
```

No `P.IsRegular`, entropy-sign, positive-count, cell-occupancy, or compatibility assumption belongs in N4. The model's positive logarithm and nonnegative natural counts suffice. The following algebraic identity can stay proof-local; a separate public normalization abstraction is unnecessary.

## Minimal normalization algebra

For arbitrary natural counts `m : Fin c → Fin k → ℕ` and a real `L>0`, prove

```lean
(∑ a : Fin c, ∑ l : Fin k,
  if 0 < (m a l : ℝ) / L then
    ((m a l : ℝ) / L) *
      Real.log (((∑ h : Fin k, (m a h : ℝ)) / L) /
        ((m a l : ℝ) / L))
  else 0) = typeEntropy m / L
```

There is no assumption that these counts are realized by any word. For each cell, put `M=sum_l m_l`.

1. A count is positive after division exactly when `m_l>0`.
2. In that branch `M≥m_l>0`, so both logarithm arguments needed for the expansion are positive. Cancel `L` in the ratio and use `log(M/m_l)=log M-log m_l`.
3. If `m_l=0`, the source branch is zero and the corresponding `m_l log m_l` term is zero. If `M=0`, all natural counts are zero, so the entire cell contributes zero on both sides.
4. Sum over digits, using `sum_l m_l=M`, then over cells, and reindex the cell sum by `finProdFinEquiv`.

The positive-scale premise in this local algebra is essential if the scale is generalized to arbitrary reals: with counts `(1,1)` and `L=-1`, the left side is zero because all normalized counts are negative, whereas the right side is `-2 log 2`. In the model, `D.one_lt_N` already gives `L>0`, so no new scientific hypothesis is introduced.

`TimeProfile.profileH_source_formula` is not needed to prove N4. Its existing interface has regularity, positive-chi, and legality premises which its zero-aware formula proof does not fundamentally require. Requiring those extra premises merely to reuse it would obscure this simpler exact normalization route. It also does not perform the raw-count or joint-cell conversion by itself.

## Two direct application corollaries, if exported

The four core results already suffice. If the final assembly benefits from named corollaries, the following two interfaces are valid without further definitions or model hypotheses and should be reviewed/frozen explicitly with the same batch.

For the common data

```lean
(A : Riffle.Setup D) (P : TimeProfile.BorelPartition D.k)
(timeClass : Fin D.K → Fin R) (alpha : ℝ)
(route : ProfileWord A (sourceProfileGood A P) alpha → Fin 4)
(p : ProfileWord A (sourceProfileGood A P) alpha)
```

write, **only as proof/statement-local abbreviations**,

```lean
cell := sourceProfileCell P timeClass
good := sourceProfileGood A P
key := encodeProfile A cell good alpha route p
hx := (Riffle.stable_desc (Riffle.admissiblePair_rawPair p.property.1)
  p.property.2.1).1
H := TimeProfile.profileH D.N (asProfile D) (legalVector p.val.2.2 hx)
  P timeClass A.chi (Riffle.join p.val.1 p.val.2.1).length p.val.2.2.length
```

**N5 `sourceProfileH_encode`:** with exactly the data above, conclude

`H = typeEntropy (profileKeyCounts (c := R*P.cellCount) key) / Real.log (D.N : ℝ)`.

Proof: N4 and the previously proved `profileKeyCounts_encode`. No separate legality argument is added to the theorem: `hx` is derived from actual domain membership.

**N6 `sourceProfileFibre_card_le_rpow_profileH`:** with exactly the same data, conclude

`(Nat.card (ProfileFibre A cell good alpha route key) : ℝ) ≤ (D.N : ℝ)^H`.

Proof: the already proved PF4 `profileFibre_card_le_rpow_entropy`, followed by N5. `Finite (ProfileFibre ...)` remains a proved fact from PF2, not a new typeclass premise. The arbitrary route can only subdivide fibres and needs no probabilistic correctness property for this cardinality theorem.

These formulations deliberately use an **encoded realized key**. One can equivalently take an arbitrary key and a member of its fibre, but an arbitrary unrealized key has no corresponding source word or source entropy. PF3/PF4 already handle such empty fibres with the natural-count key entropy. Do not introduce a purported source representative for every arbitrary key.

## Adversarial checks and traps

- **Do not omit the joint cell index.** Suppose two good positions have the same time cell but different simplex cells, with one digit zero and the other digit one. The correct two pure cell histograms have entropy zero. Combining them into the single time-cell histogram produces natural entropy `2 log 2`. Thus the proposed exact equality fails if only time or only simplex cells are used. N-D1 retains both.
- **Do not reassociate Fin products silently.** The key count vector has length `(R*P.cellCount)*D.k`. `Fin ((R*P.cellCount)*D.k)` and `Fin (R*(P.cellCount*D.k))` are not an identification supplied by the types alone. Use `finProdFinEquiv(q,i)` followed by the existing cell/digit flattening, or prove any alternate reindexing explicitly.
- **Goodness is representative-based.** It is the literal strict test `2*A.chi < prob(P.rep(P.classify(asProfile D j))) digit`. Replacing it by a test on the actual pile probability, or by `≤`/`≥` at the threshold, changes the counted sets. No approximation is part of this identity.
- **Good positions depend on the word.** N1–N4 compare each word with its own selected digits. A fibre has a common free-position set only because equal encoded exceptional supports and endpoints were proved earlier. The new bridge must not declare that set fixed for arbitrary words.
- **The source entropy is not `-sum c log c`.** The normalized counts do not generally sum to one, even within one cell. The `c_total log c_total` term is required. For raw counts `(1,1)` and `L=2`, the actual normalized entropy is `log 2`, exactly half of the natural entropy `2 log 2`.
- **Zero cells require no positive-total assumption.** All their counts vanish. Terms with zero count are omitted in TimeProfile and multiplied by zero in `typeEntropy`. Expand logarithms only in positive-count branches; do not use a division-log identity at zero without its actual premises.
- **Negative alpha is included.** Since `log N>0`, a negative-alpha real cutoff is impossible even when the exceptional set is empty. The natural floor budget becomes zero and is only a consequence of the real cutoff, not an equivalent replacement. N3 preserves the real predicate.
- **Empty continuation and terminal singleton.** If `join.length=x.length`, both supports and all counts are empty, so `profileR=profileH=0`. No finite fluctuation or nonterminal premise is relevant. If the literal join length exceeds the legal word length, the proposed raw identities still reduce to the same empty interval.
- **Zero time-cell count and empty horizon.** A map `Fin K→Fin 0` can exist only when the domain is empty. No `0<R` assumption is needed: the data itself handles impossibility, while `K=0` gives empty counts and entropy zero. Similarly, no extra positive partition-cell premise is required.
- **Padding is never counted.** All relevant filters require `j.val<x.length`. The possibly illegal zero suffix of `legalVector` is absent from every normalization sum. Do not normalize a padded full-horizon word instead.
- **Entropy constancy does not imply exact cost constancy.** N5 makes H the same for members of a given fixed key; N1 and the key support make R the same. Actual column costs may vary inside a regular simplex cell, so the previous counterexample to constant exact `cL` remains unaffected.

## Source and final-assembly scope

The article's `def:space-time-digit-profile` has precisely the normalized counts and zero-aware entropy above. Its proof uses `N^{H_x}` as the within-class cardinality factor. The existing first-moment encoder refines the printed profile by storing exceptional values as well as locations; fixing these values makes PF4 valid without a new entropy factor. The present identities preserve the same good counts and H, so they identify that refined fibre's actual cardinality bound with the source numerical entropy.

An arbitrary fixed `timeClass` is sufficient for all finite identities. Choosing it from the source time mesh is a separate instantiation of the same function, not an extra premise of normalization. No horizon relation, limiting argument, homogeneous cutoff, variance estimate, or density bound enters this batch. The still-missing large-block stochastic argument is not resolved by this normalization bridge.

