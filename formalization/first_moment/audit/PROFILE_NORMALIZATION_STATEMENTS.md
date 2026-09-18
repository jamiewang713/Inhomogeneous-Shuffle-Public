# Actual profile normalization: statement-design proposal

Status: proposed, not frozen or implemented. The primary agent is the statement designer for this batch; the algebra and adversarial agents independently reconstruct and audit it. Mathematical sources remain the three authorized files. The exact finite profile and entropy definitions in the existing project are used unchanged.

Suggested implementation: `FirstMomentModel/ProfileNormalization.lean`, namespace `InhomogeneousShuffle.FirstMoment.Model`, on the common Lean 4.33.1 runtime. Imports will include the separately frozen `StableNumericalBridge`, `ProfileFibreEntropy` and `RiffleTimeProfile.Digits`.

There are exactly two proposed definitions and eight exported theorem interfaces. All finite reindexings, natural-count entropy identities and proof irrelevance facts described below may be local to proofs. No extra scientific premise, regularity assumption or nonempty-count hypothesis is permitted.

## Definitions

With explicit `D : Riffle.Model`, `P : TimeProfile.BorelPartition D.k` and implicit natural `R`:

1. `sourceCell (D) (P) (timeClass : Fin D.K → Fin R) : Fin D.K → Fin (R * P.cellCount)` is exactly

   `fun j => finProdFinEquiv (timeClass j, P.classify (asProfile D j))`.

2. `sourceGood (D) (P) (chi : ℝ) : Fin D.K → ℕ → Prop` is exactly

   `fun j a => ∃ ha : a < D.k, P.IsGoodDigit chi (asProfile D j) ⟨a, ha⟩`.

The threshold `chi` is arbitrary real data in this identity layer. The eventual source application sets it to `A.chi`; the identities do not assert regularity. The joint cell is flattened before appending its digit, so keys have dimension `(R * P.cellCount) * D.k`. No unproved reassociation of dependent finite indices is used.

## Common variables and notation for exact interfaces

The following is notation for this document, not additional definitions or hypotheses:

```lean
{D : Riffle.Model} {R : ℕ}
(A : Riffle.Setup D) (P : TimeProfile.BorelPartition D.k)
(timeClass : Fin D.K → Fin R) (chi : ℝ)
```

Write `cell` for `sourceCell D P timeClass`, `good` for `sourceGood D P chi`, and `X x hx` for `legalVector x hx`. These abbreviations are expanded in the implementation. For actual profile word

```lean
(alpha : ℝ) (p : ProfileWord A (sourceGood D P chi) alpha)
```

the displayed notation `hpLegal` means exactly the derived proof term

```lean
(Riffle.stable_desc (Riffle.admissiblePair_rawPair p.property.1)
  p.property.2.1).1
```

and `Xp` means `legalVector p.val.2.2 hpLegal`. It is not a new legality binder. Write `vp` for `(Riffle.join p.val.1 p.val.2.1).length`, `np` for `p.val.2.2.length`, and `keyp` for `encodeProfile A cell good alpha route p`. In all interfaces the source time-profile argument is exactly `asProfile D`.

## Exhaustive theorem interfaces

**PN1. `sourceGood_fin_iff`** has explicit `D P chi`, `j : Fin D.K`, `l : Fin D.k`, and no other variables or premises:

```lean
sourceGood D P chi j l.val ↔ P.IsGoodDigit chi (asProfile D j) l
```

**PN2. `exceptionalPositions_source_eq`** has `A P chi`, arbitrary `y z x : Riffle.Word`, and `hx : Riffle.Legal D x`:

```lean
exceptionalPositions A (sourceGood D P chi) y z x =
  TimeProfile.exceptionalPositions (asProfile D) (legalVector x hx) P chi
    (Riffle.join y z).length x.length
```

No prefix, raw-pair or stable membership premise is needed for this identity between the literal filters. Included positions are before `x.length`, where the vector digit agrees with the list digit; when the lower endpoint exceeds the upper one both filters are empty.

**PN3. `digitCount_source_eq`** has `A P timeClass chi`, arbitrary `y z x`, `hx : Riffle.Legal D x`, and `a : Fin R × Fin P.cellCount × Fin D.k`:

```lean
TimeProfile.digitCount D.N (asProfile D) (legalVector x hx) P timeClass chi
    (Riffle.join y z).length x.length a =
  (goodDigitCount A (sourceCell D P timeClass) (sourceGood D P chi)
    y z x (finProdFinEquiv (a.1, a.2.1)) a.2.2 : ℝ) /
      Real.log (D.N : ℝ)
```

The triple is right-associated, exactly as in `TimeProfile.digitKey`. The conclusion is pointwise equality for every joint cell and digit, not just an equality of totals.

**PN4. `profileR_source_eq`** has exactly `A P chi y z x hx` as in PN2:

```lean
TimeProfile.profileR D.N (asProfile D) (legalVector x hx) P chi
    (Riffle.join y z).length x.length =
  ((exceptionalPositions A (sourceGood D P chi) y z x).card : ℝ) /
    Real.log (D.N : ℝ)
```

**PN5. `profileH_source_eq`** has exactly `A P timeClass chi y z x hx` as in PN3, without its final `a`:

```lean
TimeProfile.profileH D.N (asProfile D) (legalVector x hx) P timeClass chi
    (Riffle.join y z).length x.length =
  typeEntropy (goodDigitCount A (sourceCell D P timeClass)
    (sourceGood D P chi) y z x) / Real.log (D.N : ℝ)
```

This is an equality with the existing natural-count entropy. It needs no positive-count, compatible-count, regular-partition, sign-of-chi, ambient approximation or exact-size premise.

**PN6. `profileWord_profileR_le`** has `A P chi alpha` and `p : ProfileWord A good alpha`. It has no `timeClass` or route argument:

```lean
TimeProfile.profileR D.N (asProfile D) Xp P chi vp np ≤ alpha
```

Here `Xp`, `vp`, `np`, and the derived proof inside `Xp` expand exactly as specified above. The original real exceptional cutoff in `p.property.2.2`, PN4 and the positive logarithm give the result. There is no new `0 ≤ alpha` premise, and no replacement of the real cutoff by its natural floor.

**PN7. `profileWord_profileH_key`** has `A P timeClass chi alpha`,

```lean
(route : ProfileWord A (sourceGood D P chi) alpha → Fin 4)
(p : ProfileWord A (sourceGood D P chi) alpha)
```

and concludes

```lean
TimeProfile.profileH D.N (asProfile D) Xp P timeClass chi vp np =
  typeEntropy (profileKeyCounts (c := R * P.cellCount) keyp) /
    Real.log (D.N : ℝ)
```

The route is arbitrary fixed data of the existing profile encoder. Its probabilistic correctness is not required for this counting identity. Apply PN5 and the already proved `profileKeyCounts_encode`.

**PN8. `profileFibre_card_le_rpow_profileH`** has exactly the binders of PN7 and concludes

```lean
(Nat.card (ProfileFibre A (sourceCell D P timeClass) (sourceGood D P chi)
  alpha route keyp) : ℝ) ≤
    (D.N : ℝ) ^ (TimeProfile.profileH D.N (asProfile D) Xp P timeClass chi vp np)
```

This specializes the existing exact fibre bound to an actual realized profile and rewrites its entropy using PN7. No `Finite` instance is assumed, and no individual word is claimed to inject into the class key. Exact `cL` is not claimed constant on the fibre.

## Proof-local helper schemas

All helpers must be instances of these reviewed finite identities, not new assumptions on PN1–PN8:

1. Alphabet proof irrelevance and `legalVector_digit` identify goodness of the natural digit with goodness of its `Fin` coordinate before the actual word length. Filter extensionality gives PN2. Empty intervals and zero piles outside the legal prefix remain included.
2. For a pair `a : Fin R × Fin P.cellCount`, injectivity of `finProdFinEquiv` identifies the joint cell; digit equality follows from `Fin.ext_iff`. Reordering conjunctions in the good-position filter gives equality of natural cardinalities and hence PN3.
3. For arbitrary natural counts `n : Fin d → Fin k → ℕ` and real `L > 0`, the zero-aware normalized sum satisfies

   ```text
   ∑ a, ∑ l,
     if 0 < (n a l : ℝ)/L then
       ((n a l : ℝ)/L) * log ((∑ q, (n a q : ℝ)/L) / ((n a l : ℝ)/L))
     else 0
   = typeEntropy n / L.
   ```

   When `n a l > 0`, its cell total is positive, cancellation of `L` and the logarithm quotient law are justified. When it is zero, both corresponding weighted terms vanish. A zero cell total forces all counts in it to be zero; no logarithm positivity assertion is made there. Finite distributivity then yields the original total-log-total minus sum-count-log-count formula. This uses no extra assumption on counts and includes `d=0` or `k=0`.
4. The equivalence `finProdFinEquiv : Fin R × Fin P.cellCount ≃ Fin (R * P.cellCount)` reindexes the outer finite sum in PN5. `D.one_lt_N` gives `L = log N > 0`; it is derived, not assumed anew.
5. Division by the same positive logarithm turns the existing real cutoff into PN6, for arbitrary real alpha. The existing key-count identity and existing fibre entropy theorem give PN7–PN8 by exact rewriting.

These statements only identify already defined finite data. The horizon relation, source error budgets, bad-edge reduction, localization and valid stochastic density estimates remain separate obligations. The proposed identities do not alter any earlier freeze.
