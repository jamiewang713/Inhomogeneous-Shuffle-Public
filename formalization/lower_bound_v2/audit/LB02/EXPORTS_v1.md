# LB02 exact compiled export inventory

All declarations below are checked theorems in the pinned Lean environment. Frozen target definitions retain the exact bodies in `Contracts/v1/EXPORTS.md`; the seven assignment checks in `Thinning/Check.lean` compile. Every generic input in the concrete exported results is discharged.

## RiffleLowerV2.Thinning.successiveThinning

```lean
RiffleLowerV2.Thinning.successiveThinning :
RiffleLowerV2.Targets.SuccessiveThinning
```

## RiffleLowerV2.Thinning.prefixTails

```lean
RiffleLowerV2.Thinning.prefixTails :
RiffleLowerV2.Targets.PrefixTails
```

## RiffleLowerV2.Thinning.allPrefixConcentration

```lean
RiffleLowerV2.Thinning.allPrefixConcentration :
RiffleLowerV2.Targets.AllPrefixConcentration
```

## RiffleLowerV2.Thinning.prefixFailureUniform

```lean
RiffleLowerV2.Thinning.prefixFailureUniform :
RiffleLowerV2.Targets.PrefixFailureUniform
```

## RiffleLowerV2.Thinning.residualLaw

```lean
RiffleLowerV2.Thinning.residualLaw :
RiffleLowerV2.Targets.ResidualLaw
```

## RiffleLowerV2.Thinning.hypergeometricTransform

```lean
RiffleLowerV2.Thinning.hypergeometricTransform :
RiffleLowerV2.Targets.HypergeometricTransform
```

## RiffleLowerV2.Thinning.maximalMeanIdentity

```lean
RiffleLowerV2.Thinning.maximalMeanIdentity :
RiffleLowerV2.Targets.MaximalMeanIdentity
```

## RiffleLowerV2.Thinning.Compat.HypergeomParams.expect_pow_le_all

```lean
RiffleLowerV2.Thinning.Compat.HypergeomParams.expect_pow_le_all :
∀ (p : RiffleLowerV2.Thinning.Compat.HypergeomParams) {s : ℝ},
  0 < s →
    (p.law.expect fun (q : Fin (p.draws + 1)) => s ^ ↑q) ≤
      (1 - ↑p.draws / ↑p.population + ↑p.draws / ↑p.population * s) ^ p.marked
```

## RiffleLowerV2.Thinning.Compat.sample_expect_pow_intersection_le

```lean
RiffleLowerV2.Thinning.Compat.sample_expect_pow_intersection_le :
∀ {α : Type u_1} [inst : DecidableEq α] (V A : Finset α) (m : ℕ) (hm : m ≤ V.card),
  A ⊆ V →
    ∀ {s : ℝ},
      0 < s →
        ((RiffleLowerV2.Thinning.Compat.sampleLaw V m hm).expect fun (S : RiffleLowerV2.Thinning.Compat.Sample V m) =>
            s ^ (A ∩ ↑S).card) ≤
          (1 - ↑m / ↑V.card + ↑m / ↑V.card * s) ^ A.card
```

## RiffleLowerV2.Thinning.permutation_subset_expect

```lean
RiffleLowerV2.Thinning.permutation_subset_expect :
∀ {M : ℕ} (B : Finset (Fin M)) (f : RiffleLowerV2.Thinning.Compat.Sample Finset.univ B.card → ℝ),
  (RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation M) fun (σ : RiffleLowerV2.Permutation M) =>
      f (RiffleLowerV2.Thinning.permSubset B σ)) =
    (RiffleLowerV2.Thinning.Compat.sampleLaw Finset.univ B.card ⋯).expect f
```

## RiffleLowerV2.Thinning.permutation_intersection_transform

```lean
RiffleLowerV2.Thinning.permutation_intersection_transform :
∀ {M : ℕ} (A B : Finset (Fin M)) {s : ℝ},
  0 < s →
    (RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation M) fun (σ : RiffleLowerV2.Permutation M) =>
        s ^ (A ∩ Finset.map (Equiv.toEmbedding σ) B).card) ≤
      (1 - ↑B.card / ↑M + ↑B.card / ↑M * s) ^ A.card
```

## RiffleLowerV2.Thinning.column_subset_expect

```lean
RiffleLowerV2.Thinning.column_subset_expect :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (j : Fin K) (a : Fin k)
  (f : RiffleLowerV2.Thinning.Compat.Sample Finset.univ (cuts.count j a) → ℝ),
  (RiffleLowerV2.expect (TimeProfile.columnPMF cuts j) fun (c : TimeProfile.ColumnAssignments cuts j) =>
      f (RiffleLowerV2.Thinning.columnDigitSubset a c)) =
    (RiffleLowerV2.Thinning.Compat.sampleLaw Finset.univ (cuts.count j a) ⋯).expect f
```

## RiffleLowerV2.Thinning.column_intersection_transform

```lean
RiffleLowerV2.Thinning.column_intersection_transform :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (j : Fin K) (a : Fin k) (A : Finset (Fin N)) {s : ℝ},
  0 < s →
    (RiffleLowerV2.expect (TimeProfile.columnPMF cuts j) fun (c : TimeProfile.ColumnAssignments cuts j) =>
        s ^ (A ∩ {i : Fin N | ↑c i = a}).card) ≤
      (1 - ↑(cuts.count j a) / ↑N + ↑(cuts.count j a) / ↑N * s) ^ A.card
```

## RiffleLowerV2.Thinning.independent_intersection_transform

```lean
RiffleLowerV2.Thinning.independent_intersection_transform :
∀ (M d : ℕ) (Ω : Fin d → Type u_1) [inst : (j : Fin d) → Fintype (Ω j)] [inst_1 : ∀ (j : Fin d), Nonempty (Ω j)]
  (S : (j : Fin d) → Ω j → Finset (Fin M)) (q : Fin d → ℝ),
  (∀ (j : Fin d), 0 ≤ q j ∧ q j ≤ 1) →
    (∀ (j : Fin d) (A : Finset (Fin M)) (s : ℝ),
        0 < s →
          (RiffleLowerV2.expect (PMF.uniformOfFintype (Ω j)) fun (ω : Ω j) => s ^ (A ∩ S j ω).card) ≤
            (1 - q j + q j * s) ^ A.card) →
      ∀ (A : Finset (Fin M)) (s : ℝ),
        0 < s →
          (RiffleLowerV2.expect (PMF.uniformOfFintype ((j : Fin d) → Ω j)) fun (ω : (j : Fin d) → Ω j) =>
              s ^ (RiffleLowerV2.Thinning.intersectionWithin A S ω).card) ≤
            (1 - ∏ j : Fin d, q j + (∏ j : Fin d, q j) * s) ^ A.card
```

## RiffleLowerV2.Thinning.thinningTails

```lean
RiffleLowerV2.Thinning.thinningTails :
∀ (M d : ℕ),
  0 < M →
    ∀ (m : Fin d → ℕ),
      (∀ (j : Fin d), m j ≤ M) →
        (∀ (t : ℝ),
            0 < t →
              (RiffleLowerV2.probability (PMF.uniformOfFintype (Fin d → RiffleLowerV2.Permutation M))
                  fun (ω : Fin d → RiffleLowerV2.Permutation M) =>
                  t ≤ |↑(RiffleLowerV2.Targets.thinningCount m ω) - ↑M * RiffleLowerV2.Targets.thinningQ M m|) ≤
                2 * Real.exp (-t ^ 2 / (4 * (↑M * RiffleLowerV2.Targets.thinningQ M m + t)))) ∧
          (RiffleLowerV2.probability (PMF.uniformOfFintype (Fin d → RiffleLowerV2.Permutation M))
                fun (ω : Fin d → RiffleLowerV2.Permutation M) =>
                ↑(RiffleLowerV2.Targets.thinningCount m ω) ≤ ↑M * RiffleLowerV2.Targets.thinningQ M m / 2) ≤
              Real.exp (-RiffleLowerV2.chernoffConstant * (↑M * RiffleLowerV2.Targets.thinningQ M m)) ∧
            (RiffleLowerV2.probability (PMF.uniformOfFintype (Fin d → RiffleLowerV2.Permutation M))
                fun (ω : Fin d → RiffleLowerV2.Permutation M) => RiffleLowerV2.Targets.thinningCount m ω < 2) ≤
              2 * Real.exp (-(↑M * RiffleLowerV2.Targets.thinningQ M m) / 2)
```

## RiffleLowerV2.Thinning.prefixTransform

```lean
RiffleLowerV2.Thinning.prefixTransform :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  0 < N →
    ∀ (w : RiffleLowerV2.Prefix k K) (s : ℝ),
      0 < s →
        (RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) fun (ω : TimeProfile.ShuffleSample cuts) =>
              s ^ RiffleLowerV2.prefixCount w ω) ≤
            (1 - RiffleLowerV2.prefixMass cuts w + RiffleLowerV2.prefixMass cuts w * s) ^ N ∧
          (1 - RiffleLowerV2.prefixMass cuts w + RiffleLowerV2.prefixMass cuts w * s) ^ N ≤
            Real.exp (RiffleLowerV2.prefixMean cuts w * (s - 1))
```

## RiffleLowerV2.Thinning.prefixCount_eq_zero_of_mass_zero

```lean
RiffleLowerV2.Thinning.prefixCount_eq_zero_of_mass_zero :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  0 < N →
    ∀ (w : RiffleLowerV2.Prefix k K),
      RiffleLowerV2.prefixMass cuts w = 0 → ∀ (ω : RiffleLowerV2.Sample cuts), RiffleLowerV2.prefixCount w ω = 0
```

## RiffleLowerV2.Thinning.residualConditionalExpect

```lean
RiffleLowerV2.Thinning.residualConditionalExpect :
∀ {k N K b : ℕ} (cuts : TimeProfile.Cuts k N K) (r : RiffleLowerV2.RowPrescription N k K b),
  Function.Injective r.row →
    0 < RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts) (RiffleLowerV2.prescriptionEvent r) →
      ∃ (residual : TimeProfile.Cuts k (N - b) K),
        (∀ (j : Fin K) (a : Fin k), residual.count j a = cuts.count j a - RiffleLowerV2.usedCount r j a) ∧
          ∀ (e : Fin (N - b) → Fin N),
            Function.Injective e →
              (∀ (i : Fin N), (∃ (q : Fin (N - b)), e q = i) ↔ ¬∃ (q : Fin b), r.row q = i) →
                ∀ (F : (Fin (N - b) → Fin K → Fin k) → ℝ),
                  RiffleLowerV2.conditionalExpect (TimeProfile.fixedCountPMF cuts)
                      (fun (ω : TimeProfile.ShuffleSample cuts) =>
                        F fun (q : Fin (N - b)) (j : Fin K) => TimeProfile.sampleEntry ω (e q) j)
                      (RiffleLowerV2.prescriptionEvent r) =
                    RiffleLowerV2.expect (TimeProfile.fixedCountPMF residual)
                      fun (η : TimeProfile.ShuffleSample residual) => F (TimeProfile.sampleRow η)
```

## RiffleLowerV2.Thinning.residualConditionalProbability

```lean
RiffleLowerV2.Thinning.residualConditionalProbability :
∀ {k N K b : ℕ} (cuts : TimeProfile.Cuts k N K) (r : RiffleLowerV2.RowPrescription N k K b),
  Function.Injective r.row →
    0 < RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts) (RiffleLowerV2.prescriptionEvent r) →
      ∃ (residual : TimeProfile.Cuts k (N - b) K),
        (∀ (j : Fin K) (a : Fin k), residual.count j a = cuts.count j a - RiffleLowerV2.usedCount r j a) ∧
          ∀ (e : Fin (N - b) → Fin N),
            Function.Injective e →
              (∀ (i : Fin N), (∃ (q : Fin (N - b)), e q = i) ↔ ¬∃ (q : Fin b), r.row q = i) →
                ∀ (A : (Fin (N - b) → Fin K → Fin k) → Prop),
                  RiffleLowerV2.conditionalProbability (TimeProfile.fixedCountPMF cuts)
                      (fun (ω : TimeProfile.ShuffleSample cuts) =>
                        A fun (q : Fin (N - b)) (j : Fin K) => TimeProfile.sampleEntry ω (e q) j)
                      (RiffleLowerV2.prescriptionEvent r) =
                    RiffleLowerV2.probability (TimeProfile.fixedCountPMF residual)
                      fun (η : TimeProfile.ShuffleSample residual) => A (TimeProfile.sampleRow η)
```

## RiffleLowerV2.Thinning.residualColumnIndependence

```lean
RiffleLowerV2.Thinning.residualColumnIndependence :
∀ {k N K b : ℕ} (cuts : TimeProfile.Cuts k N K) (r : RiffleLowerV2.RowPrescription N k K b),
  b < N →
    Function.Injective r.row →
      0 < RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts) (RiffleLowerV2.prescriptionEvent r) →
        ∃ (residual : TimeProfile.Cuts k (N - b) K),
          (∀ (j : Fin K) (a : Fin k), residual.count j a = cuts.count j a - RiffleLowerV2.usedCount r j a) ∧
            ∀ (e : Fin (N - b) → Fin N),
              Function.Injective e →
                (∀ (i : Fin N), (∃ (q : Fin (N - b)), e q = i) ↔ ¬∃ (q : Fin b), r.row q = i) →
                  ∀ (f : Fin K → (Fin (N - b) → Fin k) → ℝ),
                    RiffleLowerV2.conditionalExpect (TimeProfile.fixedCountPMF cuts)
                        (fun (ω : TimeProfile.ShuffleSample cuts) =>
                          ∏ j : Fin K, f j fun (q : Fin (N - b)) => TimeProfile.sampleEntry ω (e q) j)
                        (RiffleLowerV2.prescriptionEvent r) =
                      ∏ j : Fin K,
                        RiffleLowerV2.expect (TimeProfile.columnPMF residual j)
                          fun (c : TimeProfile.ColumnAssignments residual j) => f j ↑c
```

## RiffleLowerV2.Thinning.residualPrefixCount_eq_restriction

```lean
RiffleLowerV2.Thinning.residualPrefixCount_eq_restriction :
∀ {N k K b : ℕ} {cuts : TimeProfile.Cuts k N K} (r : RiffleLowerV2.RowPrescription N k K b),
  Function.Injective r.row →
    ∀ (e : Fin (N - b) → Fin N),
      Function.Injective e →
        (∀ (i : Fin N), (∃ (q : Fin (N - b)), e q = i) ↔ ¬∃ (q : Fin b), r.row q = i) →
          ∀ (w : RiffleLowerV2.Prefix k K) (ω : RiffleLowerV2.Sample cuts),
            RiffleLowerV2.prescriptionEvent r ω →
              RiffleLowerV2.Thinning.residualPrefixCount r w ω =
                RiffleLowerV2.Thinning.rowArrayPrefixCount w fun (q : Fin (N - b)) (j : Fin K) =>
                  TimeProfile.sampleEntry ω (e q) j
```

## RiffleLowerV2.Thinning.residualPrefixMass_eq

```lean
RiffleLowerV2.Thinning.residualPrefixMass_eq :
∀ {N k K b : ℕ} (cuts : TimeProfile.Cuts k N K) (r : RiffleLowerV2.RowPrescription N k K b)
  (residual : TimeProfile.Cuts k (N - b) K),
  (∀ (j : Fin K) (a : Fin k), residual.count j a = cuts.count j a - RiffleLowerV2.usedCount r j a) →
    ∀ (w : RiffleLowerV2.Prefix k K),
      RiffleLowerV2.prefixMass residual w = RiffleLowerV2.Thinning.residualPrefixMass cuts r w
```

## RiffleLowerV2.Thinning.residualPrefixMean_eq

```lean
RiffleLowerV2.Thinning.residualPrefixMean_eq :
∀ {N k K b : ℕ} (cuts : TimeProfile.Cuts k N K) (r : RiffleLowerV2.RowPrescription N k K b)
  (residual : TimeProfile.Cuts k (N - b) K),
  (∀ (j : Fin K) (a : Fin k), residual.count j a = cuts.count j a - RiffleLowerV2.usedCount r j a) →
    ∀ (w : RiffleLowerV2.Prefix k K),
      RiffleLowerV2.prefixMean residual w = RiffleLowerV2.Thinning.residualPrefixMean cuts r w
```

## RiffleLowerV2.Thinning.residualPrefixTransform

```lean
RiffleLowerV2.Thinning.residualPrefixTransform :
∀ {N k K b : ℕ} (cuts : TimeProfile.Cuts k N K) (r : RiffleLowerV2.RowPrescription N k K b),
  b < N →
    Function.Injective r.row →
      0 < RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts) (RiffleLowerV2.prescriptionEvent r) →
        ∀ (w : RiffleLowerV2.Prefix k K) (s : ℝ),
          0 < s →
            RiffleLowerV2.conditionalExpect (TimeProfile.fixedCountPMF cuts)
                  (fun (ω : TimeProfile.ShuffleSample cuts) => s ^ RiffleLowerV2.Thinning.residualPrefixCount r w ω)
                  (RiffleLowerV2.prescriptionEvent r) ≤
                (1 - RiffleLowerV2.Thinning.residualPrefixMass cuts r w +
                    RiffleLowerV2.Thinning.residualPrefixMass cuts r w * s) ^
                  (N - b) ∧
              (1 - RiffleLowerV2.Thinning.residualPrefixMass cuts r w +
                    RiffleLowerV2.Thinning.residualPrefixMass cuts r w * s) ^
                  (N - b) ≤
                Real.exp (RiffleLowerV2.Thinning.residualPrefixMean cuts r w * (s - 1))
```

## RiffleLowerV2.Thinning.residualPrefixTails

```lean
RiffleLowerV2.Thinning.residualPrefixTails :
∀ {N k K b : ℕ} (cuts : TimeProfile.Cuts k N K) (r : RiffleLowerV2.RowPrescription N k K b),
  b < N →
    Function.Injective r.row →
      0 < RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts) (RiffleLowerV2.prescriptionEvent r) →
        ∀ (w : RiffleLowerV2.Prefix k K),
          (∀ (t : ℝ),
              0 < t →
                RiffleLowerV2.conditionalProbability (TimeProfile.fixedCountPMF cuts)
                    (fun (ω : TimeProfile.ShuffleSample cuts) =>
                      t ≤
                        |↑(RiffleLowerV2.Thinning.residualPrefixCount r w ω) -
                            RiffleLowerV2.Thinning.residualPrefixMean cuts r w|)
                    (RiffleLowerV2.prescriptionEvent r) ≤
                  2 * Real.exp (-t ^ 2 / (4 * (RiffleLowerV2.Thinning.residualPrefixMean cuts r w + t)))) ∧
            RiffleLowerV2.conditionalProbability (TimeProfile.fixedCountPMF cuts)
                  (fun (ω : TimeProfile.ShuffleSample cuts) =>
                    ↑(RiffleLowerV2.Thinning.residualPrefixCount r w ω) ≤
                      RiffleLowerV2.Thinning.residualPrefixMean cuts r w / 2)
                  (RiffleLowerV2.prescriptionEvent r) ≤
                Real.exp (-RiffleLowerV2.chernoffConstant * RiffleLowerV2.Thinning.residualPrefixMean cuts r w) ∧
              RiffleLowerV2.conditionalProbability (TimeProfile.fixedCountPMF cuts)
                  (fun (ω : TimeProfile.ShuffleSample cuts) => RiffleLowerV2.Thinning.residualPrefixCount r w ω < 2)
                  (RiffleLowerV2.prescriptionEvent r) ≤
                2 * Real.exp (-RiffleLowerV2.Thinning.residualPrefixMean cuts r w / 2)
```

## RiffleLowerV2.Thinning.maximalWordTail

```lean
RiffleLowerV2.Thinning.maximalWordTail :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N),
  ∃ (w : RiffleLowerV2.Word k K),
    RiffleLowerV2.IsCanonicalMaxWord cuts w ∧
      RiffleLowerV2.wordMass cuts w * ↑N = RiffleLowerV2.maximalMean cuts hN ∧
        ∀ (m : ℕ),
          ↑m ≤ RiffleLowerV2.maximalMean cuts hN / 2 →
            (RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts) fun (ω : TimeProfile.ShuffleSample cuts) =>
                RiffleLowerV2.wordCount w ω < m) ≤
              Real.exp (-RiffleLowerV2.chernoffConstant * RiffleLowerV2.maximalMean cuts hN)
```

## RiffleLowerV2.Thinning.chernoffConstant_pos

```lean
RiffleLowerV2.Thinning.chernoffConstant_pos :
0 < RiffleLowerV2.chernoffConstant
```

## RiffleLowerV2.Thinning.prefix_card_exact

```lean
RiffleLowerV2.Thinning.prefix_card_exact :
∀ (k K : ℕ), Fintype.card (RiffleLowerV2.Prefix k K) = ∑ n : Fin (K + 1), k ^ ↑n
```

## RiffleLowerV2.Thinning.prefix_card_le_of_cuts

```lean
RiffleLowerV2.Thinning.prefix_card_le_of_cuts :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K), 0 < N → Fintype.card (RiffleLowerV2.Prefix k K) ≤ (K + 1) * k ^ K
```

## RiffleLowerV2.Thinning.prefixFailure_le_envelope

```lean
RiffleLowerV2.Thinning.prefixFailure_le_envelope :
∀ {N k K : ℕ},
  2 ≤ N →
    2 ≤ k →
      ∀ {T : ℝ},
        0 < T →
          ↑K ≤ T * TimeProfile.logScale N →
            ∀ (ε : ℝ),
              RiffleLowerV2.prefixFailure N k K ε ≤ 2 * (T + 1) * ↑N ^ (1 + T * Real.log ↑k) * Real.exp (-↑N ^ ε / 8)
```

## RiffleLowerV2.Thinning.prefixFailureEnvelope_tendsto

```lean
RiffleLowerV2.Thinning.prefixFailureEnvelope_tendsto :
∀ (k : ℕ) (T ε : ℝ),
  0 < ε →
    Filter.Tendsto (fun (N : ℕ) => 2 * (T + 1) * ↑N ^ (1 + T * Real.log ↑k) * Real.exp (-↑N ^ ε / 8)) Filter.atTop
      (nhds 0)
```

