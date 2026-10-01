# LB06 exact checked exports v1

Required export: `RiffleLowerV2.Types.roundedType : RiffleLowerV2.Targets.RoundedTypeTarget` is a proved theorem. All types below are printed from the compiled Lean environment; no target definition is counted as a proof.

## RiffleLowerV2.Types.card_eq_rpow_log_div

Source: `RiffleLowerV2/Types/MassBins.lean:136`. Kind: theorem.

```lean
RiffleLowerV2.Types.card_eq_rpow_log_div : ∀ (N n : ℕ), 2 ≤ N → 0 < n → ↑n = ↑N ^ (Real.log ↑n / TimeProfile.logScale N)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.cellPositionCount_eq_fiberCard

Source: `RiffleLowerV2/Types/Counting.lean:222`. Kind: theorem.

```lean
RiffleLowerV2.Types.cellPositionCount_eq_fiberCard : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K))
  (i : Fin P.cellCount),
  RiffleLowerV2.cellPositionCount cuts hN P I i = Fintype.card { j : ↥I // P.classify (cuts.profile hN ↑j) = i }
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.cellPositionCount_le_card

Source: `RiffleLowerV2/Types/WordEstimates.lean:9`. Kind: theorem.

```lean
RiffleLowerV2.Types.cellPositionCount_le_card : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K))
  (i : Fin P.cellCount), RiffleLowerV2.cellPositionCount cuts hN P I i ≤ I.card
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.cell_sum_error

Source: `RiffleLowerV2/Types/WordEstimates.lean:134`. Kind: theorem.

```lean
RiffleLowerV2.Types.cell_sum_error : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K))
  (v : Fin P.cellCount → ℝ) (f : Fin K → ℝ) (e : ℝ),
  (∀ j ∈ I, |v (P.classify (cuts.profile hN j)) - f j| ≤ e) →
    |∑ i : Fin P.cellCount, ↑(RiffleLowerV2.cellPositionCount cuts hN P I i) * v i - ∑ j ∈ I, f j| ≤ ↑I.card * e
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.cell_sum_identity

Source: `RiffleLowerV2/Types/WordEstimates.lean:22`. Kind: theorem.

```lean
RiffleLowerV2.Types.cell_sum_identity : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K))
  (v : Fin P.cellCount → ℝ),
  ∑ j ∈ I, v (P.classify (cuts.profile hN j)) =
    ∑ i : Fin P.cellCount, ↑(RiffleLowerV2.cellPositionCount cuts hN P I i) * v i
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.constructedTypeData

Source: `RiffleLowerV2/Types/Construction.lean:46`. Kind: definition.

```lean
RiffleLowerV2.Types.constructedTypeData : {k N K : ℕ} →
  TimeProfile.Cuts k N K →
    0 < N →
      2 ≤ k →
        (P : TimeProfile.BorelPartition k) →
          Finset (Fin K) → {xi : ℝ} → 0 < xi → xi < 1 / (4 * ↑k) → ℝ → RiffleLowerV2.RoundedTypeData P
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.constructedTypeData_count

Source: `RiffleLowerV2/Types/Construction.lean:53`. Kind: theorem.

```lean
RiffleLowerV2.Types.constructedTypeData_count : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (hk : 2 ≤ k) (P : TimeProfile.BorelPartition k)
  (I : Finset (Fin K)) {xi : ℝ} (hxi : 0 < xi) (hxiK : xi < 1 / (4 * ↑k)) (alpha : ℝ) (i : Fin P.cellCount) (l : Fin k),
  (RiffleLowerV2.Types.constructedTypeData cuts hN hk P I hxi hxiK alpha).count i l =
    RiffleLowerV2.Types.roundedCount (RiffleLowerV2.cellPositionCount cuts hN P I i)
      (RiffleLowerV2.retainedTilt P xi alpha i) l
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.constructedTypeData_spec

Source: `RiffleLowerV2/Types/Construction.lean:67`. Kind: theorem.

```lean
RiffleLowerV2.Types.constructedTypeData_spec : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N),
  2 ≤ N →
    ∀ (hk : 2 ≤ k) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K)) {xi C : ℝ} (hxi : 0 < xi)
      (hxiK : xi < 1 / (4 * ↑k)),
      P.IsRegular xi C →
        ∀ (alpha : ℝ),
          RiffleLowerV2.TypeDataSpec cuts hN P I xi alpha
            (RiffleLowerV2.Types.constructedTypeData cuts hN hk P I hxi hxiK alpha)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.cutoff_log_ge_one

Source: `RiffleLowerV2/Types/Truncation.lean:32`. Kind: theorem.

```lean
RiffleLowerV2.Types.cutoff_log_ge_one : ∀ {xi : ℝ}, 0 < xi → xi < 1 / 8 → 1 ≤ Real.log (1 / xi)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.cutoff_small

Source: `RiffleLowerV2/Types/Truncation.lean:20`. Kind: theorem.

```lean
RiffleLowerV2.Types.cutoff_small : ∀ {k : ℕ}, 2 ≤ k → ∀ {xi : ℝ}, 0 < xi → xi < 1 / (4 * ↑k) → xi < 1 / 8 ∧ 2 * xi < 1 / ↑k ∧ 3 * xi < 1 / ↑k
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.digitCost_bounds_of_cutoff

Source: `RiffleLowerV2/Types/WordEstimates.lean:54`. Kind: theorem.

```lean
RiffleLowerV2.Types.digitCost_bounds_of_cutoff : ∀ {p xi : ℝ}, 0 < xi → xi ≤ p → p ≤ 1 → 0 ≤ TimeProfile.digitCost p ∧ TimeProfile.digitCost p ≤ Real.log (1 / xi)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.digitCost_nonneg

Source: `RiffleLowerV2/Types/Truncation.lean:210`. Kind: theorem.

```lean
RiffleLowerV2.Types.digitCost_nonneg : ∀ {k : ℕ} (p : TimeProfile.Simplex k) (l : Fin k), 0 ≤ TimeProfile.digitCost (TimeProfile.prob p l)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.emptyTypeData

Source: `RiffleLowerV2/Types/Empty.lean:9`. Kind: definition.

```lean
RiffleLowerV2.Types.emptyTypeData : {k : ℕ} → (P : TimeProfile.BorelPartition k) → RiffleLowerV2.RoundedTypeData P
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.empty_classes_card_one

Source: `RiffleLowerV2/Types/Empty.lean:28`. Kind: theorem.

```lean
RiffleLowerV2.Types.empty_classes_card_one : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k),
  (RiffleLowerV2.roundedClass cuts hN P ∅ (RiffleLowerV2.Types.emptyTypeData P)).card = 1 ∧
    (RiffleLowerV2.selectedClass cuts hN P ∅ (RiffleLowerV2.Types.emptyTypeData P)).card = 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.empty_exponents_zero

Source: `RiffleLowerV2/Types/Empty.lean:34`. Kind: theorem.

```lean
RiffleLowerV2.Types.empty_exponents_zero : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k),
  RiffleLowerV2.typeJ N (RiffleLowerV2.Types.emptyTypeData P) = 0 ∧
    RiffleLowerV2.typeH cuts hN P ∅ (RiffleLowerV2.Types.emptyTypeData P) = 0
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.entropy_eq_cost_log

Source: `RiffleLowerV2/Types/Truncation.lean:154`. Kind: theorem.

```lean
RiffleLowerV2.Types.entropy_eq_cost_log : ∀ {k : ℕ} (p : TimeProfile.Simplex k) (q : Fin k → ℝ) (alpha Z : ℝ),
  0 < Z →
    ∑ l : Fin k, q l = 1 →
      (∀ (l : Fin k), q l ≠ 0 → 0 < TimeProfile.prob p l ∧ q l = TimeProfile.prob p l ^ alpha / Z) →
        TimeProfile.shannonEntropy q =
          alpha * ∑ l : Fin k, q l * TimeProfile.digitCost (TimeProfile.prob p l) + Real.log Z
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.entropy_rounding_error

Source: `RiffleLowerV2/Types/EntropyBounds.lean:155`. Kind: theorem.

```lean
RiffleLowerV2.Types.entropy_rounding_error : ∀ {k : ℕ} (n : ℕ) (c : Fin k → ℕ) (q : Fin k → ℝ),
  ∑ l : Fin k, c l = n →
    (∀ (l : Fin k), 0 ≤ q l) →
      ∑ l : Fin k, q l = 1 →
        (∀ (l : Fin k), |↑(c l) - ↑n * q l| ≤ 1) →
          |RiffleLowerV2.Types.xlogx ↑n - ∑ l : Fin k, RiffleLowerV2.Types.xlogx ↑(c l) -
                ↑n * TimeProfile.shannonEntropy q| ≤
            ↑k * (Real.log (↑n + 1) + 2)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.entropy_scale_identity

Source: `RiffleLowerV2/Types/EntropyBounds.lean:129`. Kind: theorem.

```lean
RiffleLowerV2.Types.entropy_scale_identity : ∀ {k : ℕ} (n : ℕ) (q : Fin k → ℝ),
  (∀ (l : Fin k), 0 ≤ q l) →
    ∑ l : Fin k, q l = 1 →
      ↑n * TimeProfile.shannonEntropy q =
        RiffleLowerV2.Types.xlogx ↑n - ∑ l : Fin k, RiffleLowerV2.Types.xlogx (↑n * q l)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.exists_maximal_indexFiber

Source: `RiffleLowerV2/Types/MassBins.lean:20`. Kind: theorem.

```lean
RiffleLowerV2.Types.exists_maximal_indexFiber : ∀ {Ω : Type u_1} [DecidableEq Ω] (s : Finset Ω) (f : Ω → ℕ),
  s.Nonempty →
    ∃ (b : ℕ), ∀ (a : ℕ), (RiffleLowerV2.Types.indexFiber s f a).card ≤ (RiffleLowerV2.Types.indexFiber s f b).card
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.exists_prob_ge_inv_card

Source: `RiffleLowerV2/Types/Truncation.lean:10`. Kind: theorem.

```lean
RiffleLowerV2.Types.exists_prob_ge_inv_card : ∀ {k : ℕ}, 0 < k → ∀ (p : TimeProfile.Simplex k), ∃ (l : Fin k), 1 / ↑k ≤ TimeProfile.prob p l
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.exists_supported_rounding

Source: `RiffleLowerV2/Types/Rounding.lean:93`. Kind: theorem.

```lean
RiffleLowerV2.Types.exists_supported_rounding : ∀ {k : ℕ} (n : ℕ) (q : Fin k → ℝ),
  (∀ (l : Fin k), 0 ≤ q l) →
    ∑ l : Fin k, q l = 1 →
      ∃ (c : Fin k → ℕ),
        ∑ l : Fin k, c l = n ∧ (∀ (l : Fin k), q l = 0 → c l = 0) ∧ ∀ (l : Fin k), |↑(c l) - ↑n * q l| ≤ 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.exists_typeDataSpec

Source: `RiffleLowerV2/Types/Construction.lean:84`. Kind: theorem.

```lean
RiffleLowerV2.Types.exists_typeDataSpec : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N),
  2 ≤ N →
    2 ≤ k →
      ∀ (P : TimeProfile.BorelPartition k) (I : Finset (Fin K)) {xi C : ℝ},
        0 < xi →
          xi < 1 / (4 * ↑k) →
            P.IsRegular xi C →
              ∀ (alpha : ℝ), ∃ (D : RiffleLowerV2.RoundedTypeData P), RiffleLowerV2.TypeDataSpec cuts hN P I xi alpha D
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.exists_type_partition

Source: `RiffleLowerV2/Types/Partition.lean:9`. Kind: theorem.

```lean
RiffleLowerV2.Types.exists_type_partition : ∀ {k : ℕ}, 2 ≤ k → ∀ {xi : ℝ}, 0 < xi → xi < 1 / (4 * ↑k) → ∃ (P : TimeProfile.BorelPartition k), P.IsRegular xi 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.exp_cell_error

Source: `RiffleLowerV2/Types/Truncation.lean:312`. Kind: theorem.

```lean
RiffleLowerV2.Types.exp_cell_error : ∀ {xi C : ℝ}, 0 ≤ xi → xi ≤ 1 / 8 → 0 ≤ C → Real.exp (8 * C * xi) - 1 ≤ 8 * C * Real.exp C * xi
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.factorial_log_error

Source: `RiffleLowerV2/Types/EntropyBounds.lean:45`. Kind: theorem.

```lean
RiffleLowerV2.Types.factorial_log_error : ∀ (n : ℕ), |Real.log ↑n.factorial - (RiffleLowerV2.Types.xlogx ↑n - ↑n)| ≤ Real.log (↑n + 1) + 2
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.finite_remainder_bound

Source: `RiffleLowerV2/Types/Rates.lean:43`. Kind: theorem.

```lean
RiffleLowerV2.Types.finite_remainder_bound : ∀ (k m : ℕ) {n L T B : ℝ},
  0 ≤ n →
    1 ≤ L →
      0 < T →
        0 ≤ B →
          n ≤ T * L →
            (↑k * ↑m * B + 1 + ↑m * (2 * ↑k + 1) * (Real.log (n + 1) + 2) + Real.log (2 + n * B)) / L ≤
              RiffleLowerV2.Types.roundConstant k m T B * (Real.log L + 1) / L
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.finite_type_approximation

Source: `RiffleLowerV2/Types/Approximation.lean:20`. Kind: theorem.

```lean
RiffleLowerV2.Types.finite_type_approximation : ∀ {k N K : ℕ},
  2 ≤ k →
    ∀ (cuts : TimeProfile.Cuts k N K) (hN : 0 < N),
      2 ≤ N →
        ∀ (P : TimeProfile.BorelPartition k) (I : Finset (Fin K)) {xi C alpha : ℝ},
          0 < xi →
            xi < 1 / (4 * ↑k) →
              0 ≤ C →
                P.IsRegular xi C →
                  alpha ∈ Set.Icc 2 4 →
                    ∀ (D : RiffleLowerV2.RoundedTypeData P),
                      RiffleLowerV2.TypeDataSpec cuts hN P I xi alpha D →
                        RiffleLowerV2.TypeApproximation cuts hN P I alpha
                          ((RiffleLowerV2.Types.typeConstant k C * ↑I.card * xi * Real.log (1 / xi) +
                                    ↑k * ↑P.cellCount * Real.log (1 / xi) +
                                  1 +
                                ↑P.cellCount * (2 * ↑k + 1) * (Real.log (↑I.card + 1) + 2) +
                              Real.log (2 + ↑I.card * Real.log (1 / xi))) /
                            TimeProfile.logScale N)
                          D
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.floor_image_card_bound

Source: `RiffleLowerV2/Types/MassBins.lean:58`. Kind: theorem.

```lean
RiffleLowerV2.Types.floor_image_card_bound : ∀ {Ω : Type u_1} [DecidableEq Ω] (s : Finset Ω) (g : Ω → ℝ) (M : ℝ),
  0 ≤ M → (∀ x ∈ s, g x ≤ M) → ↑(Finset.image (fun (x : Ω) => ⌊g x⌋₊) s).card ≤ 2 + M
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.fullPowerSum_le_one

Source: `RiffleLowerV2/Types/Truncation.lean:774`. Kind: theorem.

```lean
RiffleLowerV2.Types.fullPowerSum_le_one : ∀ {k : ℕ} (p : TimeProfile.Simplex k) {alpha : ℝ}, alpha ∈ Set.Icc 2 4 → TimeProfile.powerSum p alpha ≤ 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.fullPowerSum_pos

Source: `RiffleLowerV2/Types/Truncation.lean:134`. Kind: theorem.

```lean
RiffleLowerV2.Types.fullPowerSum_pos : ∀ {k : ℕ}, 2 ≤ k → ∀ (p : TimeProfile.Simplex k) {alpha : ℝ}, alpha ∈ Set.Icc 2 4 → 0 < TimeProfile.powerSum p alpha
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.indexFiber

Source: `RiffleLowerV2/Types/MassBins.lean:13`. Kind: definition.

```lean
RiffleLowerV2.Types.indexFiber : {Ω : Type u_1} → Finset Ω → (Ω → ℕ) → ℕ → Finset Ω
```

Transitive axioms: `Quot.sound`, `propext`.

## RiffleLowerV2.Types.indexFiber_nonempty

Source: `RiffleLowerV2/Types/MassBins.lean:16`. Kind: theorem.

```lean
RiffleLowerV2.Types.indexFiber_nonempty : ∀ {Ω : Type u_1} [DecidableEq Ω] {s : Finset Ω} {f : Ω → ℕ} {b : ℕ},
  (RiffleLowerV2.Types.indexFiber s f b).Nonempty ↔ b ∈ Finset.image f s
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.initialTypeData

Source: `RiffleLowerV2/Types/Construction.lean:11`. Kind: definition.

```lean
RiffleLowerV2.Types.initialTypeData : {k N K : ℕ} →
  TimeProfile.Cuts k N K →
    0 < N → (P : TimeProfile.BorelPartition k) → Finset (Fin K) → ℝ → ℝ → RiffleLowerV2.RoundedTypeData P
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.initialTypeData_error

Source: `RiffleLowerV2/Types/Construction.lean:32`. Kind: theorem.

```lean
RiffleLowerV2.Types.initialTypeData_error : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K))
  (xi alpha : ℝ) (i : Fin P.cellCount) (l : Fin k),
  |↑((RiffleLowerV2.Types.initialTypeData cuts hN P I xi alpha).count i l) -
        ↑(RiffleLowerV2.cellPositionCount cuts hN P I i) * RiffleLowerV2.retainedTilt P xi alpha i l| ≤
    1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.initialTypeData_nonempty

Source: `RiffleLowerV2/Types/Construction.lean:39`. Kind: theorem.

```lean
RiffleLowerV2.Types.initialTypeData_nonempty : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N),
  2 ≤ k →
    ∀ (P : TimeProfile.BorelPartition k) (I : Finset (Fin K)) {xi alpha : ℝ},
      0 < xi →
        xi < 1 / (4 * ↑k) →
          (RiffleLowerV2.roundedClass cuts hN P I (RiffleLowerV2.Types.initialTypeData cuts hN P I xi alpha)).Nonempty
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.initialTypeData_support

Source: `RiffleLowerV2/Types/Construction.lean:26`. Kind: theorem.

```lean
RiffleLowerV2.Types.initialTypeData_support : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K))
  (xi alpha : ℝ) (i : Fin P.cellCount) (l : Fin k),
  TimeProfile.prob (P.rep i) l ≤ 2 * xi → (RiffleLowerV2.Types.initialTypeData cuts hN P I xi alpha).count i l = 0
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.initialTypeData_total

Source: `RiffleLowerV2/Types/Construction.lean:17`. Kind: theorem.

```lean
RiffleLowerV2.Types.initialTypeData_total : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N),
  2 ≤ k →
    ∀ (P : TimeProfile.BorelPartition k) (I : Finset (Fin K)) {xi alpha : ℝ},
      0 < xi →
        xi < 1 / (4 * ↑k) →
          ∀ (i : Fin P.cellCount),
            ∑ l : Fin k, (RiffleLowerV2.Types.initialTypeData cuts hN P I xi alpha).count i l =
              RiffleLowerV2.cellPositionCount cuts hN P I i
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.leastMaxBin

Source: `RiffleLowerV2/Types/MassBins.lean:32`. Kind: definition.

```lean
RiffleLowerV2.Types.leastMaxBin : {Ω : Type u_1} → [DecidableEq Ω] → (s : Finset Ω) → (Ω → ℕ) → s.Nonempty → ℕ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.leastMaxBin_card_bound

Source: `RiffleLowerV2/Types/MassBins.lean:54`. Kind: theorem.

```lean
RiffleLowerV2.Types.leastMaxBin_card_bound : ∀ {Ω : Type u_1} [inst : DecidableEq Ω] (s : Finset Ω) (f : Ω → ℕ) (hs : s.Nonempty),
  s.card ≤ (RiffleLowerV2.Types.indexFiber s f (RiffleLowerV2.Types.leastMaxBin s f hs)).card * (Finset.image f s).card
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.leastMaxBin_log_loss

Source: `RiffleLowerV2/Types/MassBins.lean:72`. Kind: theorem.

```lean
RiffleLowerV2.Types.leastMaxBin_log_loss : ∀ {Ω : Type u_1} [inst : DecidableEq Ω] (s : Finset Ω) (f : Ω → ℕ) (hs : s.Nonempty) {B : ℝ},
  0 < B →
    ↑(Finset.image f s).card ≤ B →
      0 ≤
          Real.log ↑s.card -
            Real.log ↑(RiffleLowerV2.Types.indexFiber s f (RiffleLowerV2.Types.leastMaxBin s f hs)).card ∧
        Real.log ↑s.card -
            Real.log ↑(RiffleLowerV2.Types.indexFiber s f (RiffleLowerV2.Types.leastMaxBin s f hs)).card ≤
          Real.log B
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.leastMaxBin_maximal

Source: `RiffleLowerV2/Types/MassBins.lean:35`. Kind: theorem.

```lean
RiffleLowerV2.Types.leastMaxBin_maximal : ∀ {Ω : Type u_1} [inst : DecidableEq Ω] (s : Finset Ω) (f : Ω → ℕ) (hs : s.Nonempty) (b : ℕ),
  (RiffleLowerV2.Types.indexFiber s f b).card ≤
    (RiffleLowerV2.Types.indexFiber s f (RiffleLowerV2.Types.leastMaxBin s f hs)).card
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.leastMaxBin_nonempty

Source: `RiffleLowerV2/Types/MassBins.lean:47`. Kind: theorem.

```lean
RiffleLowerV2.Types.leastMaxBin_nonempty : ∀ {Ω : Type u_1} [inst : DecidableEq Ω] (s : Finset Ω) (f : Ω → ℕ) (hs : s.Nonempty),
  (RiffleLowerV2.Types.indexFiber s f (RiffleLowerV2.Types.leastMaxBin s f hs)).Nonempty
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.leastMaxBin_tie

Source: `RiffleLowerV2/Types/MassBins.lean:39`. Kind: theorem.

```lean
RiffleLowerV2.Types.leastMaxBin_tie : ∀ {Ω : Type u_1} [inst : DecidableEq Ω] (s : Finset Ω) (f : Ω → ℕ) (hs : s.Nonempty) (b : ℕ),
  (RiffleLowerV2.Types.indexFiber s f b).card =
      (RiffleLowerV2.Types.indexFiber s f (RiffleLowerV2.Types.leastMaxBin s f hs)).card →
    RiffleLowerV2.Types.leastMaxBin s f hs ≤ b
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.logScale_ge_one

Source: `RiffleLowerV2/Types/Rates.lean:26`. Kind: theorem.

```lean
RiffleLowerV2.Types.logScale_ge_one : ∀ {N : ℕ}, RiffleLowerV2.Types.typeThreshold ≤ N → 1 ≤ TimeProfile.logScale N
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.log_multinomial_quotient

Source: `RiffleLowerV2/Types/ClassEntropy.lean:20`. Kind: theorem.

```lean
RiffleLowerV2.Types.log_multinomial_quotient : ∀ {k : ℕ} (n : ℕ) (c : Fin k → ℕ),
  ∑ l : Fin k, c l = n →
    Real.log ↑(n.factorial / ∏ l : Fin k, (c l).factorial) =
      Real.log ↑n.factorial - ∑ l : Fin k, Real.log ↑(c l).factorial
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.massBin_eq_indexFiber

Source: `RiffleLowerV2/Types/MassBins.lean:121`. Kind: theorem.

```lean
RiffleLowerV2.Types.massBin_eq_indexFiber : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K))
  (D : RiffleLowerV2.RoundedTypeData P),
  (∀ x ∈ RiffleLowerV2.roundedClass cuts hN P I D, 0 < RiffleLowerV2.massOn cuts x) →
    ∀ (b : ℕ),
      RiffleLowerV2.massBin cuts hN P I D b =
        RiffleLowerV2.Types.indexFiber (RiffleLowerV2.roundedClass cuts hN P I D)
          (fun (x : RiffleLowerV2.WordOn k I) => ⌊-Real.log (RiffleLowerV2.massOn cuts x)⌋₊) b
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.massOn_cost_bounds

Source: `RiffleLowerV2/Types/MassBins.lean:103`. Kind: theorem.

```lean
RiffleLowerV2.Types.massOn_cost_bounds : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  0 < N →
    ∀ {I : Finset (Fin K)} (x : RiffleLowerV2.WordOn k I) {xi : ℝ},
      0 < xi →
        (∀ (j : ↥I), xi ≤ ↑(cuts.count (↑j) (x j)) / ↑N) →
          0 ≤ -Real.log (RiffleLowerV2.massOn cuts x) ∧
            -Real.log (RiffleLowerV2.massOn cuts x) ≤ ↑I.card * Real.log (1 / xi)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.massOn_empty

Source: `RiffleLowerV2/Types/Empty.lean:12`. Kind: theorem.

```lean
RiffleLowerV2.Types.massOn_empty : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (x : RiffleLowerV2.WordOn k ∅), RiffleLowerV2.massOn cuts x = 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.massOn_le_one

Source: `RiffleLowerV2/Types/MassBins.lean:95`. Kind: theorem.

```lean
RiffleLowerV2.Types.massOn_le_one : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  0 < N → ∀ {I : Finset (Fin K)} (x : RiffleLowerV2.WordOn k I), RiffleLowerV2.massOn cuts x ≤ 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.massOn_pos

Source: `RiffleLowerV2/Types/MassBins.lean:91`. Kind: theorem.

```lean
RiffleLowerV2.Types.massOn_pos : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) {I : Finset (Fin K)} (x : RiffleLowerV2.WordOn k I),
  (∀ (j : ↥I), 0 < ↑(cuts.count (↑j) (x j)) / ↑N) → 0 < RiffleLowerV2.massOn cuts x
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.multinomial_log_entropy_error

Source: `RiffleLowerV2/Types/EntropyBounds.lean:228`. Kind: theorem.

```lean
RiffleLowerV2.Types.multinomial_log_entropy_error : ∀ {k : ℕ} (n : ℕ) (c : Fin k → ℕ) (q : Fin k → ℝ),
  ∑ l : Fin k, c l = n →
    (∀ (l : Fin k), 0 ≤ q l) →
      ∑ l : Fin k, q l = 1 →
        (∀ (l : Fin k), |↑(c l) - ↑n * q l| ≤ 1) →
          |Real.log ↑n.factorial - ∑ l : Fin k, Real.log ↑(c l).factorial - ↑n * TimeProfile.shannonEntropy q| ≤
            (2 * ↑k + 1) * (Real.log (↑n + 1) + 2)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.multinomial_log_factorial_error

Source: `RiffleLowerV2/Types/EntropyBounds.lean:187`. Kind: theorem.

```lean
RiffleLowerV2.Types.multinomial_log_factorial_error : ∀ {k : ℕ} (n : ℕ) (c : Fin k → ℕ),
  ∑ l : Fin k, c l = n →
    |Real.log ↑n.factorial - ∑ l : Fin k, Real.log ↑(c l).factorial -
          (RiffleLowerV2.Types.xlogx ↑n - ∑ l : Fin k, RiffleLowerV2.Types.xlogx ↑(c l))| ≤
      (↑k + 1) * (Real.log (↑n + 1) + 2)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.multinomial_quotient_pos

Source: `RiffleLowerV2/Types/ClassEntropy.lean:11`. Kind: theorem.

```lean
RiffleLowerV2.Types.multinomial_quotient_pos : ∀ {k : ℕ} (n : ℕ) (c : Fin k → ℕ), ∑ l : Fin k, c l = n → 0 < n.factorial / ∏ l : Fin k, (c l).factorial
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.omittedCostSum

Source: `RiffleLowerV2/Types/Truncation.lean:373`. Kind: definition.

```lean
RiffleLowerV2.Types.omittedCostSum : {k : ℕ} → TimeProfile.Simplex k → TimeProfile.Simplex k → ℝ → ℝ → ℝ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.omittedCostSum_le

Source: `RiffleLowerV2/Types/Truncation.lean:427`. Kind: theorem.

```lean
RiffleLowerV2.Types.omittedCostSum_le : ∀ {k : ℕ} (r p : TimeProfile.Simplex k) {xi alpha : ℝ},
  0 ≤ xi →
    alpha ∈ Set.Icc 2 4 →
      (∀ (l : Fin k), TimeProfile.prob r l ≤ 2 * xi → TimeProfile.prob p l ≤ 3 * xi) →
        RiffleLowerV2.Types.omittedCostSum r p xi alpha ≤ 3 * ↑k * xi
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.omittedCostSum_small

Source: `RiffleLowerV2/Types/Truncation.lean:739`. Kind: theorem.

```lean
RiffleLowerV2.Types.omittedCostSum_small : ∀ {k : ℕ} (r p : TimeProfile.Simplex k) {xi alpha : ℝ},
  0 < xi →
    xi < 1 / 8 →
      alpha ∈ Set.Icc 2 4 →
        (∀ (l : Fin k), TimeProfile.prob r l ≤ 2 * xi → TimeProfile.prob p l ≤ 3 * xi) →
          RiffleLowerV2.Types.omittedCostSum r p xi alpha ≤ 12 * ↑k * xi ^ 2 * Real.log (1 / xi)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.omittedEntropySum

Source: `RiffleLowerV2/Types/Truncation.lean:769`. Kind: definition.

```lean
RiffleLowerV2.Types.omittedEntropySum : {k : ℕ} → TimeProfile.Simplex k → TimeProfile.Simplex k → ℝ → ℝ → ℝ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.omittedEntropySum_bounds

Source: `RiffleLowerV2/Types/Truncation.lean:822`. Kind: theorem.

```lean
RiffleLowerV2.Types.omittedEntropySum_bounds : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (r p : TimeProfile.Simplex k) {xi alpha : ℝ},
      0 < xi →
        xi < 1 / 8 →
          alpha ∈ Set.Icc 2 4 →
            (∀ (l : Fin k), TimeProfile.prob r l ≤ 2 * xi → TimeProfile.prob p l ≤ 3 * xi) →
              0 ≤ RiffleLowerV2.Types.omittedEntropySum r p xi alpha ∧
                RiffleLowerV2.Types.omittedEntropySum r p xi alpha ≤ 48 * ↑k ^ 5 * xi ^ 2 * Real.log (1 / xi)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.omittedPower

Source: `RiffleLowerV2/Types/Truncation.lean:367`. Kind: definition.

```lean
RiffleLowerV2.Types.omittedPower : {k : ℕ} → TimeProfile.Simplex k → TimeProfile.Simplex k → ℝ → ℝ → Fin k → ℝ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.omittedPower_nonneg

Source: `RiffleLowerV2/Types/Truncation.lean:376`. Kind: theorem.

```lean
RiffleLowerV2.Types.omittedPower_nonneg : ∀ {k : ℕ} (r p : TimeProfile.Simplex k) (xi alpha : ℝ) (l : Fin k), 0 ≤ RiffleLowerV2.Types.omittedPower r p xi alpha l
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.omittedSum

Source: `RiffleLowerV2/Types/Truncation.lean:370`. Kind: definition.

```lean
RiffleLowerV2.Types.omittedSum : {k : ℕ} → TimeProfile.Simplex k → TimeProfile.Simplex k → ℝ → ℝ → ℝ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.omittedSum_le

Source: `RiffleLowerV2/Types/Truncation.lean:392`. Kind: theorem.

```lean
RiffleLowerV2.Types.omittedSum_le : ∀ {k : ℕ} (r p : TimeProfile.Simplex k) {xi alpha : ℝ},
  0 ≤ xi →
    alpha ∈ Set.Icc 2 4 →
      (∀ (l : Fin k), TimeProfile.prob r l ≤ 2 * xi → TimeProfile.prob p l ≤ 3 * xi) →
        RiffleLowerV2.Types.omittedSum r p xi alpha ≤ 9 * ↑k * xi ^ 2
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.omittedTiltedCost_le

Source: `RiffleLowerV2/Types/Truncation.lean:496`. Kind: theorem.

```lean
RiffleLowerV2.Types.omittedTiltedCost_le : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (r p : TimeProfile.Simplex k) {xi alpha : ℝ},
      0 ≤ xi →
        alpha ∈ Set.Icc 2 4 →
          (∀ (l : Fin k), TimeProfile.prob r l ≤ 2 * xi → TimeProfile.prob p l ≤ 3 * xi) →
            RiffleLowerV2.Types.omittedCostSum r p xi alpha / TimeProfile.powerSum p alpha ≤ 3 * ↑k ^ 5 * xi
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.omittedTiltedCost_small

Source: `RiffleLowerV2/Types/Truncation.lean:754`. Kind: theorem.

```lean
RiffleLowerV2.Types.omittedTiltedCost_small : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (r p : TimeProfile.Simplex k) {xi alpha : ℝ},
      0 < xi →
        xi < 1 / 8 →
          alpha ∈ Set.Icc 2 4 →
            (∀ (l : Fin k), TimeProfile.prob r l ≤ 2 * xi → TimeProfile.prob p l ≤ 3 * xi) →
              RiffleLowerV2.Types.omittedCostSum r p xi alpha / TimeProfile.powerSum p alpha ≤
                12 * ↑k ^ 5 * xi ^ 2 * Real.log (1 / xi)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.omittedTiltedSum_le

Source: `RiffleLowerV2/Types/Truncation.lean:483`. Kind: theorem.

```lean
RiffleLowerV2.Types.omittedTiltedSum_le : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (r p : TimeProfile.Simplex k) {xi alpha : ℝ},
      0 ≤ xi →
        alpha ∈ Set.Icc 2 4 →
          (∀ (l : Fin k), TimeProfile.prob r l ≤ 2 * xi → TimeProfile.prob p l ≤ 3 * xi) →
            RiffleLowerV2.Types.omittedSum r p xi alpha / TimeProfile.powerSum p alpha ≤ 9 * ↑k ^ 5 * xi ^ 2
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.powerSum_card_lower

Source: `RiffleLowerV2/Types/Truncation.lean:116`. Kind: theorem.

```lean
RiffleLowerV2.Types.powerSum_card_lower : ∀ {k : ℕ},
  2 ≤ k → ∀ (p : TimeProfile.Simplex k) {alpha : ℝ}, alpha ∈ Set.Icc 2 4 → 1 ≤ ↑k ^ 4 * TimeProfile.powerSum p alpha
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.powerSum_split

Source: `RiffleLowerV2/Types/Truncation.lean:383`. Kind: theorem.

```lean
RiffleLowerV2.Types.powerSum_split : ∀ {k : ℕ} (r p : TimeProfile.Simplex k) (xi alpha : ℝ),
  TimeProfile.powerSum p alpha =
    RiffleLowerV2.Types.restrictedSum r p xi alpha + RiffleLowerV2.Types.omittedSum r p xi alpha
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.power_digitCost_le_prob

Source: `RiffleLowerV2/Types/Truncation.lean:408`. Kind: theorem.

```lean
RiffleLowerV2.Types.power_digitCost_le_prob : ∀ {k : ℕ} (p : TimeProfile.Simplex k) {alpha : ℝ},
  alpha ∈ Set.Icc 2 4 →
    ∀ (l : Fin k), TimeProfile.prob p l ^ alpha * TimeProfile.digitCost (TimeProfile.prob p l) ≤ TimeProfile.prob p l
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.power_digitCost_small

Source: `RiffleLowerV2/Types/Truncation.lean:708`. Kind: theorem.

```lean
RiffleLowerV2.Types.power_digitCost_small : ∀ {k : ℕ} (p : TimeProfile.Simplex k) {xi alpha : ℝ},
  0 < xi →
    xi < 1 / 8 →
      alpha ∈ Set.Icc 2 4 →
        ∀ (l : Fin k),
          TimeProfile.prob p l ≤ 3 * xi →
            TimeProfile.prob p l ^ alpha * TimeProfile.digitCost (TimeProfile.prob p l) ≤
              12 * xi ^ 2 * Real.log (1 / xi)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.prescribedCellWords

Source: `RiffleLowerV2/Types/Counting.lean:133`. Kind: definition.

```lean
RiffleLowerV2.Types.prescribedCellWords : {J : Type u_1} →
  {A : Type u_2} → {B : Type u_3} → [Fintype J] → [Fintype A] → [Fintype B] → (J → A) → (A → B → ℕ) → Finset (J → B)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.prescribedCellWords_card

Source: `RiffleLowerV2/Types/Counting.lean:199`. Kind: theorem.

```lean
RiffleLowerV2.Types.prescribedCellWords_card : ∀ {J : Type u_1} {A : Type u_2} {B : Type u_3} [inst : Fintype J] [inst_1 : Fintype A] [inst_2 : Fintype B]
  (cell : J → A) (c : A → B → ℕ),
  (∀ (a : A), ∑ b : B, c a b = Fintype.card { j : J // cell j = a }) →
    (RiffleLowerV2.Types.prescribedCellWords cell c).card =
      ∏ a : A, (Fintype.card { j : J // cell j = a }).factorial / ∏ b : B, (c a b).factorial
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.prescribedCellWords_nonempty

Source: `RiffleLowerV2/Types/Counting.lean:188`. Kind: theorem.

```lean
RiffleLowerV2.Types.prescribedCellWords_nonempty : ∀ {J : Type u_1} {A : Type u_2} {B : Type u_3} [inst : Fintype J] [inst_1 : Fintype A] [inst_2 : Fintype B]
  (cell : J → A) (c : A → B → ℕ),
  (∀ (a : A), ∑ b : B, c a b = Fintype.card { j : J // cell j = a }) →
    (RiffleLowerV2.Types.prescribedCellWords cell c).Nonempty
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.prescribedWords

Source: `RiffleLowerV2/Types/Counting.lean:39`. Kind: definition.

```lean
RiffleLowerV2.Types.prescribedWords : (J : Type u_1) → (A : Type u_2) → [Fintype J] → [Fintype A] → (A → ℕ) → Finset (J → A)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.prescribedWords_card

Source: `RiffleLowerV2/Types/Counting.lean:123`. Kind: theorem.

```lean
RiffleLowerV2.Types.prescribedWords_card : ∀ {J : Type u_1} {A : Type u_2} [inst : Fintype J] [inst_1 : Fintype A] (c : A → ℕ),
  ∑ a : A, c a = Fintype.card J →
    (RiffleLowerV2.Types.prescribedWords J A c).card = (Fintype.card J).factorial / ∏ a : A, (c a).factorial
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.prescribedWords_card_mul

Source: `RiffleLowerV2/Types/Counting.lean:81`. Kind: theorem.

```lean
RiffleLowerV2.Types.prescribedWords_card_mul : ∀ {J : Type u_1} {A : Type u_2} [inst : Fintype J] [inst_1 : Fintype A] (c : A → ℕ),
  ∑ a : A, c a = Fintype.card J →
    (RiffleLowerV2.Types.prescribedWords J A c).card * ∏ a : A, (c a).factorial = (Fintype.card J).factorial
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.prescribedWords_nonempty

Source: `RiffleLowerV2/Types/Counting.lean:58`. Kind: theorem.

```lean
RiffleLowerV2.Types.prescribedWords_nonempty : ∀ {J : Type u_1} {A : Type u_2} [inst : Fintype J] [inst_1 : Fintype A] (c : A → ℕ),
  ∑ a : A, c a = Fintype.card J → (RiffleLowerV2.Types.prescribedWords J A c).Nonempty
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.raw_word_cost_error

Source: `RiffleLowerV2/Types/WordEstimates.lean:60`. Kind: theorem.

```lean
RiffleLowerV2.Types.raw_word_cost_error : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K))
  (D : RiffleLowerV2.RoundedTypeData P) {xi C : ℝ},
  0 < xi →
    xi ≤ 1 →
      P.IsRegular xi C →
        ∀ (q : Fin P.cellCount → Fin k → ℝ),
          (∀ (i : Fin P.cellCount) (l : Fin k), TimeProfile.prob (P.rep i) l ≤ 2 * xi → D.count i l = 0) →
            (∀ (i : Fin P.cellCount) (l : Fin k), TimeProfile.prob (P.rep i) l ≤ 2 * xi → q i l = 0) →
              (∀ (i : Fin P.cellCount) (l : Fin k),
                  |↑(D.count i l) - ↑(RiffleLowerV2.cellPositionCount cuts hN P I i) * q i l| ≤ 1) →
                ∀ x ∈ RiffleLowerV2.roundedClass cuts hN P I D,
                  |-Real.log (RiffleLowerV2.massOn cuts x) -
                        ∑ i : Fin P.cellCount,
                          ↑(RiffleLowerV2.cellPositionCount cuts hN P I i) *
                            ∑ l : Fin k, q i l * TimeProfile.digitCost (TimeProfile.prob (P.rep i) l)| ≤
                    C * xi * ↑I.card + ↑k * ↑P.cellCount * Real.log (1 / xi)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.representativeCost_error

Source: `RiffleLowerV2/Types/Truncation.lean:557`. Kind: theorem.

```lean
RiffleLowerV2.Types.representativeCost_error : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (P : TimeProfile.BorelPartition k) {xi C alpha : ℝ},
      0 < xi →
        xi < 1 / (4 * ↑k) →
          P.IsRegular xi C →
            ∀ (i : Fin P.cellCount) (p : TimeProfile.Simplex k),
              P.classify p = i →
                |∑ l : Fin k,
                        RiffleLowerV2.retainedTilt P xi alpha i l *
                          TimeProfile.digitCost (TimeProfile.prob (P.rep i) l) -
                      ∑ l : Fin k,
                        RiffleLowerV2.retainedTilt P xi alpha i l * TimeProfile.digitCost (TimeProfile.prob p l)| ≤
                  C * xi
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.restrictedCost_bounds

Source: `RiffleLowerV2/Types/Truncation.lean:217`. Kind: theorem.

```lean
RiffleLowerV2.Types.restrictedCost_bounds : ∀ {k : ℕ} (r p : TimeProfile.Simplex k) {xi alpha : ℝ},
  0 < xi →
    0 < RiffleLowerV2.Types.restrictedSum r p xi alpha →
      (∀ (l : Fin k), 2 * xi < TimeProfile.prob r l → xi ≤ TimeProfile.prob p l) →
        0 ≤
            ∑ l : Fin k,
              RiffleLowerV2.Types.restrictedWeight r p xi alpha l * TimeProfile.digitCost (TimeProfile.prob p l) ∧
          ∑ l : Fin k,
              RiffleLowerV2.Types.restrictedWeight r p xi alpha l * TimeProfile.digitCost (TimeProfile.prob p l) ≤
            Real.log (1 / xi)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.restrictedCost_cell_error

Source: `RiffleLowerV2/Types/Truncation.lean:326`. Kind: theorem.

```lean
RiffleLowerV2.Types.restrictedCost_cell_error : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (P : TimeProfile.BorelPartition k) {xi C alpha : ℝ},
      0 < xi →
        xi < 1 / (4 * ↑k) →
          0 ≤ C →
            P.IsRegular xi C →
              alpha ∈ Set.Icc 2 4 →
                ∀ (i : Fin P.cellCount) (p : TimeProfile.Simplex k),
                  P.classify p = i →
                    |∑ l : Fin k,
                            RiffleLowerV2.Types.restrictedWeight (P.rep i) (P.rep i) xi alpha l *
                              TimeProfile.digitCost (TimeProfile.prob p l) -
                          ∑ l : Fin k,
                            RiffleLowerV2.Types.restrictedWeight (P.rep i) p xi alpha l *
                              TimeProfile.digitCost (TimeProfile.prob p l)| ≤
                      8 * C * Real.exp C * xi * Real.log (1 / xi)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.restrictedCost_eq_raw

Source: `RiffleLowerV2/Types/Truncation.lean:450`. Kind: theorem.

```lean
RiffleLowerV2.Types.restrictedCost_eq_raw : ∀ {k : ℕ} (r p : TimeProfile.Simplex k) (xi alpha : ℝ),
  ∑ l : Fin k, RiffleLowerV2.Types.restrictedWeight r p xi alpha l * TimeProfile.digitCost (TimeProfile.prob p l) =
    (∑ l : Fin k, RiffleLowerV2.Types.restrictedPower r p xi alpha l * TimeProfile.digitCost (TimeProfile.prob p l)) /
      RiffleLowerV2.Types.restrictedSum r p xi alpha
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.restrictedCost_truncation_error

Source: `RiffleLowerV2/Types/Truncation.lean:510`. Kind: theorem.

```lean
RiffleLowerV2.Types.restrictedCost_truncation_error : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (r p : TimeProfile.Simplex k) {xi alpha : ℝ},
      0 < xi →
        xi < 1 / 8 →
          alpha ∈ Set.Icc 2 4 →
            0 < RiffleLowerV2.Types.restrictedSum r p xi alpha →
              (∀ (l : Fin k), 2 * xi < TimeProfile.prob r l → xi ≤ TimeProfile.prob p l) →
                (∀ (l : Fin k), TimeProfile.prob r l ≤ 2 * xi → TimeProfile.prob p l ≤ 3 * xi) →
                  |∑ l : Fin k,
                          RiffleLowerV2.Types.restrictedWeight r p xi alpha l *
                            TimeProfile.digitCost (TimeProfile.prob p l) -
                        TimeProfile.tiltedCost p alpha| ≤
                    18 * ↑k ^ 5 * xi * Real.log (1 / xi)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.restrictedEntropy_identity

Source: `RiffleLowerV2/Types/Truncation.lean:174`. Kind: theorem.

```lean
RiffleLowerV2.Types.restrictedEntropy_identity : ∀ {k : ℕ} (r p : TimeProfile.Simplex k) (xi alpha : ℝ),
  0 < RiffleLowerV2.Types.restrictedSum r p xi alpha →
    (∀ (l : Fin k), 2 * xi < TimeProfile.prob r l → 0 < TimeProfile.prob p l) →
      TimeProfile.shannonEntropy (RiffleLowerV2.Types.restrictedWeight r p xi alpha) =
        alpha *
            ∑ l : Fin k,
              RiffleLowerV2.Types.restrictedWeight r p xi alpha l * TimeProfile.digitCost (TimeProfile.prob p l) +
          Real.log (RiffleLowerV2.Types.restrictedSum r p xi alpha)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.restrictedLog_rep_error

Source: `RiffleLowerV2/Types/Truncation.lean:631`. Kind: theorem.

```lean
RiffleLowerV2.Types.restrictedLog_rep_error : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (P : TimeProfile.BorelPartition k) {xi alpha : ℝ},
      0 < xi →
        xi < 1 / (4 * ↑k) →
          alpha ∈ Set.Icc 2 4 →
            ∀ (i : Fin P.cellCount),
              |Real.log (RiffleLowerV2.Types.restrictedSum (P.rep i) (P.rep i) xi alpha) -
                    Real.log (TimeProfile.powerSum (P.rep i) alpha)| ≤
                9 * ↑k ^ 5 * xi ^ 2
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.restrictedPower

Source: `RiffleLowerV2/Types/Truncation.lean:44`. Kind: definition.

```lean
RiffleLowerV2.Types.restrictedPower : {k : ℕ} → TimeProfile.Simplex k → TimeProfile.Simplex k → ℝ → ℝ → Fin k → ℝ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.restrictedPower_nonneg

Source: `RiffleLowerV2/Types/Truncation.lean:53`. Kind: theorem.

```lean
RiffleLowerV2.Types.restrictedPower_nonneg : ∀ {k : ℕ} (r p : TimeProfile.Simplex k) (xi alpha : ℝ) (l : Fin k),
  0 ≤ RiffleLowerV2.Types.restrictedPower r p xi alpha l
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.restrictedSum

Source: `RiffleLowerV2/Types/Truncation.lean:47`. Kind: definition.

```lean
RiffleLowerV2.Types.restrictedSum : {k : ℕ} → TimeProfile.Simplex k → TimeProfile.Simplex k → ℝ → ℝ → ℝ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.restrictedSum_pos

Source: `RiffleLowerV2/Types/Truncation.lean:60`. Kind: theorem.

```lean
RiffleLowerV2.Types.restrictedSum_pos : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (P : TimeProfile.BorelPartition k) {xi C alpha : ℝ},
      0 < xi →
        xi < 1 / (4 * ↑k) →
          P.IsRegular xi C →
            ∀ (i : Fin P.cellCount) (p : TimeProfile.Simplex k),
              P.classify p = i → 0 < RiffleLowerV2.Types.restrictedSum (P.rep i) p xi alpha
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.restrictedSum_rep_card_lower

Source: `RiffleLowerV2/Types/Truncation.lean:608`. Kind: theorem.

```lean
RiffleLowerV2.Types.restrictedSum_rep_card_lower : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (r : TimeProfile.Simplex k) {xi alpha : ℝ},
      0 < xi → xi < 1 / (4 * ↑k) → alpha ∈ Set.Icc 2 4 → 1 ≤ ↑k ^ 4 * RiffleLowerV2.Types.restrictedSum r r xi alpha
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.restrictedWeight

Source: `RiffleLowerV2/Types/Truncation.lean:50`. Kind: definition.

```lean
RiffleLowerV2.Types.restrictedWeight : {k : ℕ} → TimeProfile.Simplex k → TimeProfile.Simplex k → ℝ → ℝ → Fin k → ℝ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.restrictedWeight_cell_error

Source: `RiffleLowerV2/Types/Truncation.lean:278`. Kind: theorem.

```lean
RiffleLowerV2.Types.restrictedWeight_cell_error : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (P : TimeProfile.BorelPartition k) {xi C alpha : ℝ},
      0 < xi →
        xi < 1 / (4 * ↑k) →
          0 ≤ C →
            P.IsRegular xi C →
              alpha ∈ Set.Icc 2 4 →
                ∀ (i : Fin P.cellCount) (p : TimeProfile.Simplex k),
                  P.classify p = i →
                    ∀ (l : Fin k),
                      |RiffleLowerV2.Types.restrictedWeight (P.rep i) (P.rep i) xi alpha l -
                            RiffleLowerV2.Types.restrictedWeight (P.rep i) p xi alpha l| ≤
                        (Real.exp (8 * C * xi) - 1) * RiffleLowerV2.Types.restrictedWeight (P.rep i) p xi alpha l
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.restrictedWeight_nonneg

Source: `RiffleLowerV2/Types/Truncation.lean:142`. Kind: theorem.

```lean
RiffleLowerV2.Types.restrictedWeight_nonneg : ∀ {k : ℕ} (r p : TimeProfile.Simplex k) (xi alpha : ℝ) (l : Fin k),
  0 ≤ RiffleLowerV2.Types.restrictedWeight r p xi alpha l
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.restrictedWeight_sum

Source: `RiffleLowerV2/Types/Truncation.lean:147`. Kind: theorem.

```lean
RiffleLowerV2.Types.restrictedWeight_sum : ∀ {k : ℕ} (r p : TimeProfile.Simplex k) (xi alpha : ℝ),
  0 < RiffleLowerV2.Types.restrictedSum r p xi alpha →
    ∑ l : Fin k, RiffleLowerV2.Types.restrictedWeight r p xi alpha l = 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.retainedTilt_cost_transfer

Source: `RiffleLowerV2/Types/Truncation.lean:581`. Kind: theorem.

```lean
RiffleLowerV2.Types.retainedTilt_cost_transfer : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (P : TimeProfile.BorelPartition k) {xi C alpha : ℝ},
      0 < xi →
        xi < 1 / (4 * ↑k) →
          0 ≤ C →
            P.IsRegular xi C →
              alpha ∈ Set.Icc 2 4 →
                ∀ (i : Fin P.cellCount) (p : TimeProfile.Simplex k),
                  P.classify p = i →
                    |∑ l : Fin k,
                            RiffleLowerV2.retainedTilt P xi alpha i l *
                              TimeProfile.digitCost (TimeProfile.prob (P.rep i) l) -
                          TimeProfile.tiltedCost p alpha| ≤
                      RiffleLowerV2.Types.truncationCostConstant k C * xi * Real.log (1 / xi)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.retainedTilt_denominator_pos

Source: `RiffleLowerV2/Types/Truncation.lean:72`. Kind: theorem.

```lean
RiffleLowerV2.Types.retainedTilt_denominator_pos : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (P : TimeProfile.BorelPartition k) {xi alpha : ℝ},
      0 < xi →
        xi < 1 / (4 * ↑k) →
          ∀ (i : Fin P.cellCount),
            0 < ∑ l : Fin k, if 2 * xi < TimeProfile.prob (P.rep i) l then TimeProfile.prob (P.rep i) l ^ alpha else 0
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.retainedTilt_entropy_transfer

Source: `RiffleLowerV2/Types/Truncation.lean:659`. Kind: theorem.

```lean
RiffleLowerV2.Types.retainedTilt_entropy_transfer : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (P : TimeProfile.BorelPartition k) {xi C alpha : ℝ},
      0 < xi →
        xi < 1 / (4 * ↑k) →
          0 ≤ C →
            P.IsRegular xi C →
              alpha ∈ Set.Icc 2 4 →
                ∀ (i : Fin P.cellCount) (p : TimeProfile.Simplex k),
                  P.classify p = i →
                    |TimeProfile.shannonEntropy (RiffleLowerV2.retainedTilt P xi alpha i) -
                          TimeProfile.tiltedEntropy p alpha| ≤
                      RiffleLowerV2.Types.truncationEntropyConstant k C * xi * Real.log (1 / xi)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.retainedTilt_eq_zero_of_omitted

Source: `RiffleLowerV2/Types/Truncation.lean:96`. Kind: theorem.

```lean
RiffleLowerV2.Types.retainedTilt_eq_zero_of_omitted : ∀ {k : ℕ} (P : TimeProfile.BorelPartition k) (xi alpha : ℝ) (i : Fin P.cellCount) (l : Fin k),
  TimeProfile.prob (P.rep i) l ≤ 2 * xi → RiffleLowerV2.retainedTilt P xi alpha i l = 0
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.retainedTilt_le_one

Source: `RiffleLowerV2/Types/Truncation.lean:109`. Kind: theorem.

```lean
RiffleLowerV2.Types.retainedTilt_le_one : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (P : TimeProfile.BorelPartition k) {xi alpha : ℝ},
      0 < xi → xi < 1 / (4 * ↑k) → ∀ (i : Fin P.cellCount) (l : Fin k), RiffleLowerV2.retainedTilt P xi alpha i l ≤ 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.retainedTilt_nonneg

Source: `RiffleLowerV2/Types/Truncation.lean:84`. Kind: theorem.

```lean
RiffleLowerV2.Types.retainedTilt_nonneg : ∀ {k : ℕ} (P : TimeProfile.BorelPartition k) (xi alpha : ℝ) (i : Fin P.cellCount) (l : Fin k),
  0 ≤ RiffleLowerV2.retainedTilt P xi alpha i l
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.retainedTilt_pos_of_retained

Source: `RiffleLowerV2/Types/Truncation.lean:101`. Kind: theorem.

```lean
RiffleLowerV2.Types.retainedTilt_pos_of_retained : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (P : TimeProfile.BorelPartition k) {xi alpha : ℝ},
      0 < xi →
        xi < 1 / (4 * ↑k) →
          ∀ (i : Fin P.cellCount) (l : Fin k),
            2 * xi < TimeProfile.prob (P.rep i) l → 0 < RiffleLowerV2.retainedTilt P xi alpha i l
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.retainedTilt_sum

Source: `RiffleLowerV2/Types/Truncation.lean:89`. Kind: theorem.

```lean
RiffleLowerV2.Types.retainedTilt_sum : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (P : TimeProfile.BorelPartition k) {xi alpha : ℝ},
      0 < xi → xi < 1 / (4 * ↑k) → ∀ (i : Fin P.cellCount), ∑ l : Fin k, RiffleLowerV2.retainedTilt P xi alpha i l = 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundConstant

Source: `RiffleLowerV2/Types/Rates.lean:33`. Kind: definition.

```lean
RiffleLowerV2.Types.roundConstant : ℕ → ℕ → ℝ → ℝ → ℝ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundConstant_pos

Source: `RiffleLowerV2/Types/Rates.lean:36`. Kind: theorem.

```lean
RiffleLowerV2.Types.roundConstant_pos : ∀ (k m : ℕ) {T B : ℝ}, 0 < T → 0 ≤ B → 0 < RiffleLowerV2.Types.roundConstant k m T B
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundedClass_actual_lower

Source: `RiffleLowerV2/Types/MassBins.lean:173`. Kind: theorem.

```lean
RiffleLowerV2.Types.roundedClass_actual_lower : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K))
  (D : RiffleLowerV2.RoundedTypeData P) {xi C : ℝ},
  P.IsRegular xi C →
    (∀ (i : Fin P.cellCount) (l : Fin k), TimeProfile.prob (P.rep i) l ≤ 2 * xi → D.count i l = 0) →
      ∀ x ∈ RiffleLowerV2.roundedClass cuts hN P I D, ∀ (j : ↥I), xi ≤ ↑(cuts.count (↑j) (x j)) / ↑N
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundedClass_card

Source: `RiffleLowerV2/Types/Counting.lean:286`. Kind: theorem.

```lean
RiffleLowerV2.Types.roundedClass_card : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K))
  (D : RiffleLowerV2.RoundedTypeData P),
  (∀ (i : Fin P.cellCount), ∑ l : Fin k, D.count i l = RiffleLowerV2.cellPositionCount cuts hN P I i) →
    (RiffleLowerV2.roundedClass cuts hN P I D).card =
      ∏ i : Fin P.cellCount,
        (RiffleLowerV2.cellPositionCount cuts hN P I i).factorial / ∏ l : Fin k, (D.count i l).factorial
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundedClass_constructedTypeData

Source: `RiffleLowerV2/Types/Construction.lean:60`. Kind: theorem.

```lean
RiffleLowerV2.Types.roundedClass_constructedTypeData : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (hk : 2 ≤ k) (P : TimeProfile.BorelPartition k)
  (I : Finset (Fin K)) {xi : ℝ} (hxi : 0 < xi) (hxiK : xi < 1 / (4 * ↑k)) (alpha : ℝ),
  RiffleLowerV2.roundedClass cuts hN P I (RiffleLowerV2.Types.constructedTypeData cuts hN hk P I hxi hxiK alpha) =
    RiffleLowerV2.roundedClass cuts hN P I (RiffleLowerV2.Types.initialTypeData cuts hN P I xi alpha)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundedClass_empty

Source: `RiffleLowerV2/Types/Empty.lean:16`. Kind: theorem.

```lean
RiffleLowerV2.Types.roundedClass_empty : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k),
  RiffleLowerV2.roundedClass cuts hN P ∅ (RiffleLowerV2.Types.emptyTypeData P) = Finset.univ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundedClass_entropy_error

Source: `RiffleLowerV2/Types/ClassEntropy.lean:57`. Kind: theorem.

```lean
RiffleLowerV2.Types.roundedClass_entropy_error : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K))
  (D : RiffleLowerV2.RoundedTypeData P) (q : Fin P.cellCount → Fin k → ℝ),
  (∀ (i : Fin P.cellCount), ∑ l : Fin k, D.count i l = RiffleLowerV2.cellPositionCount cuts hN P I i) →
    (∀ (i : Fin P.cellCount) (l : Fin k), 0 ≤ q i l) →
      (∀ (i : Fin P.cellCount), ∑ l : Fin k, q i l = 1) →
        (∀ (i : Fin P.cellCount) (l : Fin k),
            |↑(D.count i l) - ↑(RiffleLowerV2.cellPositionCount cuts hN P I i) * q i l| ≤ 1) →
          |Real.log ↑(RiffleLowerV2.roundedClass cuts hN P I D).card -
                ∑ i : Fin P.cellCount,
                  ↑(RiffleLowerV2.cellPositionCount cuts hN P I i) * TimeProfile.shannonEntropy (q i)| ≤
            ↑P.cellCount * (2 * ↑k + 1) * (Real.log (↑I.card + 1) + 2)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundedClass_eq_prescribedCellWords

Source: `RiffleLowerV2/Types/Counting.lean:245`. Kind: theorem.

```lean
RiffleLowerV2.Types.roundedClass_eq_prescribedCellWords : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K))
  (D : RiffleLowerV2.RoundedTypeData P),
  RiffleLowerV2.roundedClass cuts hN P I D =
    RiffleLowerV2.Types.prescribedCellWords (fun (j : ↥I) => P.classify (cuts.profile hN ↑j)) D.count
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundedClass_log_card

Source: `RiffleLowerV2/Types/ClassEntropy.lean:43`. Kind: theorem.

```lean
RiffleLowerV2.Types.roundedClass_log_card : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K))
  (D : RiffleLowerV2.RoundedTypeData P),
  (∀ (i : Fin P.cellCount), ∑ l : Fin k, D.count i l = RiffleLowerV2.cellPositionCount cuts hN P I i) →
    Real.log ↑(RiffleLowerV2.roundedClass cuts hN P I D).card =
      ∑ i : Fin P.cellCount,
        (Real.log ↑(RiffleLowerV2.cellPositionCount cuts hN P I i).factorial -
          ∑ l : Fin k, Real.log ↑(D.count i l).factorial)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundedClass_nonempty

Source: `RiffleLowerV2/Types/Counting.lean:274`. Kind: theorem.

```lean
RiffleLowerV2.Types.roundedClass_nonempty : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K))
  (D : RiffleLowerV2.RoundedTypeData P),
  (∀ (i : Fin P.cellCount), ∑ l : Fin k, D.count i l = RiffleLowerV2.cellPositionCount cuts hN P I i) →
    (RiffleLowerV2.roundedClass cuts hN P I D).Nonempty
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundedClass_selectBinData

Source: `RiffleLowerV2/Types/MassBins.lean:204`. Kind: theorem.

```lean
RiffleLowerV2.Types.roundedClass_selectBinData : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K))
  (D : RiffleLowerV2.RoundedTypeData P) (hC : (RiffleLowerV2.roundedClass cuts hN P I D).Nonempty),
  RiffleLowerV2.roundedClass cuts hN P I (RiffleLowerV2.Types.selectBinData cuts hN P I D hC) =
    RiffleLowerV2.roundedClass cuts hN P I D
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundedCount

Source: `RiffleLowerV2/Types/Rounding.lean:17`. Kind: definition.

```lean
RiffleLowerV2.Types.roundedCount : {k : ℕ} → ℕ → (Fin k → ℝ) → Fin k → ℕ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundedCount_error

Source: `RiffleLowerV2/Types/Rounding.lean:88`. Kind: theorem.

```lean
RiffleLowerV2.Types.roundedCount_error : ∀ {k : ℕ} (n : ℕ) (q : Fin k → ℝ),
  (∀ (l : Fin k), 0 ≤ q l) → ∀ (l : Fin k), |↑(RiffleLowerV2.Types.roundedCount n q l) - ↑n * q l| ≤ 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundedCount_error_lt

Source: `RiffleLowerV2/Types/Rounding.lean:75`. Kind: theorem.

```lean
RiffleLowerV2.Types.roundedCount_error_lt : ∀ {k : ℕ} (n : ℕ) (q : Fin k → ℝ),
  (∀ (l : Fin k), 0 ≤ q l) → ∀ (l : Fin k), |↑(RiffleLowerV2.Types.roundedCount n q l) - ↑n * q l| < 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundedCount_sum

Source: `RiffleLowerV2/Types/Rounding.lean:49`. Kind: theorem.

```lean
RiffleLowerV2.Types.roundedCount_sum : ∀ {k : ℕ} (n : ℕ) (q : Fin k → ℝ),
  (∀ (l : Fin k), 0 ≤ q l) → ∑ l : Fin k, q l = 1 → ∑ l : Fin k, RiffleLowerV2.Types.roundedCount n q l = n
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundedCount_zero

Source: `RiffleLowerV2/Types/Rounding.lean:71`. Kind: theorem.

```lean
RiffleLowerV2.Types.roundedCount_zero : ∀ {k : ℕ} (n : ℕ) (q : Fin k → ℝ) (l : Fin k), q l = 0 → RiffleLowerV2.Types.roundedCount n q l = 0
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundedType

Source: `RiffleLowerV2/Types/Main.lean:12`. Kind: theorem.

```lean
RiffleLowerV2.Types.roundedType : RiffleLowerV2.Targets.RoundedTypeTarget
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundingPrefix

Source: `RiffleLowerV2/Types/Rounding.lean:13`. Kind: definition.

```lean
RiffleLowerV2.Types.roundingPrefix : {k : ℕ} → ℕ → (Fin k → ℝ) → ℕ → ℝ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundingPrefix_nonneg

Source: `RiffleLowerV2/Types/Rounding.lean:27`. Kind: theorem.

```lean
RiffleLowerV2.Types.roundingPrefix_nonneg : ∀ {k : ℕ} (n : ℕ) (q : Fin k → ℝ), (∀ (l : Fin k), 0 ≤ q l) → ∀ (a : ℕ), 0 ≤ RiffleLowerV2.Types.roundingPrefix n q a
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundingPrefix_succ

Source: `RiffleLowerV2/Types/Rounding.lean:31`. Kind: theorem.

```lean
RiffleLowerV2.Types.roundingPrefix_succ : ∀ {k : ℕ} (n : ℕ) (q : Fin k → ℝ) (l : Fin k),
  RiffleLowerV2.Types.roundingPrefix n q (↑l + 1) = RiffleLowerV2.Types.roundingPrefix n q ↑l + ↑n * q l
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundingPrefix_total

Source: `RiffleLowerV2/Types/Rounding.lean:42`. Kind: theorem.

```lean
RiffleLowerV2.Types.roundingPrefix_total : ∀ {k : ℕ} (n : ℕ) (q : Fin k → ℝ), ∑ l : Fin k, q l = 1 → RiffleLowerV2.Types.roundingPrefix n q k = ↑n
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundingRate

Source: `RiffleLowerV2/Types/Rates.lean:9`. Kind: definition.

```lean
RiffleLowerV2.Types.roundingRate : ℕ → ℝ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.roundingRate_tendsto

Source: `RiffleLowerV2/Types/Rates.lean:11`. Kind: theorem.

```lean
RiffleLowerV2.Types.roundingRate_tendsto : Filter.Tendsto RiffleLowerV2.Types.roundingRate Filter.atTop (nhds 0)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.rpow_neg_typeJ

Source: `RiffleLowerV2/Types/MassBins.lean:146`. Kind: theorem.

```lean
RiffleLowerV2.Types.rpow_neg_typeJ : ∀ {k : ℕ} {P : TimeProfile.BorelPartition k} (N : ℕ),
  2 ≤ N → ∀ (D : RiffleLowerV2.RoundedTypeData P), ↑N ^ (-RiffleLowerV2.typeJ N D) = Real.exp (-↑D.binIndex)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.selectBinData

Source: `RiffleLowerV2/Types/MassBins.lean:192`. Kind: definition.

```lean
RiffleLowerV2.Types.selectBinData : {k N K : ℕ} →
  (cuts : TimeProfile.Cuts k N K) →
    (hN : 0 < N) →
      (P : TimeProfile.BorelPartition k) →
        (I : Finset (Fin K)) →
          (D : RiffleLowerV2.RoundedTypeData P) →
            (RiffleLowerV2.roundedClass cuts hN P I D).Nonempty → RiffleLowerV2.RoundedTypeData P
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.selectBinData_count

Source: `RiffleLowerV2/Types/MassBins.lean:199`. Kind: theorem.

```lean
RiffleLowerV2.Types.selectBinData_count : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K))
  (D : RiffleLowerV2.RoundedTypeData P) (hC : (RiffleLowerV2.roundedClass cuts hN P I D).Nonempty),
  (RiffleLowerV2.Types.selectBinData cuts hN P I D hC).count = D.count
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.selectedClass_empty

Source: `RiffleLowerV2/Types/Empty.lean:22`. Kind: theorem.

```lean
RiffleLowerV2.Types.selectedClass_empty : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k),
  RiffleLowerV2.selectedClass cuts hN P ∅ (RiffleLowerV2.Types.emptyTypeData P) = Finset.univ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.selectedClass_exact_mass

Source: `RiffleLowerV2/Types/MassBins.lean:157`. Kind: theorem.

```lean
RiffleLowerV2.Types.selectedClass_exact_mass : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N),
  2 ≤ N →
    ∀ (P : TimeProfile.BorelPartition k) (I : Finset (Fin K)) (D : RiffleLowerV2.RoundedTypeData P),
      (∀ x ∈ RiffleLowerV2.roundedClass cuts hN P I D, 0 < RiffleLowerV2.massOn cuts x) →
        ∀ x ∈ RiffleLowerV2.selectedClass cuts hN P I D,
          Real.exp (-1) * ↑N ^ (-RiffleLowerV2.typeJ N D) < RiffleLowerV2.massOn cuts x ∧
            RiffleLowerV2.massOn cuts x ≤ ↑N ^ (-RiffleLowerV2.typeJ N D)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.selectedClass_log_loss

Source: `RiffleLowerV2/Types/WordEstimates.lean:159`. Kind: theorem.

```lean
RiffleLowerV2.Types.selectedClass_log_loss : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K))
  (D : RiffleLowerV2.RoundedTypeData P),
  (RiffleLowerV2.selectedClass cuts hN P I D).Nonempty →
    (∀ x ∈ RiffleLowerV2.roundedClass cuts hN P I D, 0 < RiffleLowerV2.massOn cuts x) →
      (∀ (b : ℕ), (RiffleLowerV2.massBin cuts hN P I D b).card ≤ (RiffleLowerV2.selectedClass cuts hN P I D).card) →
        ∀ {B : ℝ},
          0 < B →
            ↑(Finset.image (fun (x : RiffleLowerV2.WordOn k I) => ⌊-Real.log (RiffleLowerV2.massOn cuts x)⌋₊)
                      (RiffleLowerV2.roundedClass cuts hN P I D)).card ≤
                B →
              |Real.log ↑(RiffleLowerV2.selectedClass cuts hN P I D).card -
                    Real.log ↑(RiffleLowerV2.roundedClass cuts hN P I D).card| ≤
                Real.log B
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.selectedClass_selectBinData

Source: `RiffleLowerV2/Types/MassBins.lean:210`. Kind: theorem.

```lean
RiffleLowerV2.Types.selectedClass_selectBinData : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K))
  (D : RiffleLowerV2.RoundedTypeData P) (hC : (RiffleLowerV2.roundedClass cuts hN P I D).Nonempty),
  (∀ x ∈ RiffleLowerV2.roundedClass cuts hN P I D, 0 < RiffleLowerV2.massOn cuts x) →
    RiffleLowerV2.selectedClass cuts hN P I (RiffleLowerV2.Types.selectBinData cuts hN P I D hC) =
      RiffleLowerV2.Types.indexFiber (RiffleLowerV2.roundedClass cuts hN P I D)
        (fun (x : RiffleLowerV2.WordOn k I) => ⌊-Real.log (RiffleLowerV2.massOn cuts x)⌋₊)
        (RiffleLowerV2.Types.leastMaxBin (RiffleLowerV2.roundedClass cuts hN P I D)
          (fun (x : RiffleLowerV2.WordOn k I) => ⌊-Real.log (RiffleLowerV2.massOn cuts x)⌋₊) hC)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.selectedH_error_of_raw_entropy

Source: `RiffleLowerV2/Types/WordEstimates.lean:192`. Kind: theorem.

```lean
RiffleLowerV2.Types.selectedH_error_of_raw_entropy : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N),
  2 ≤ N →
    ∀ (P : TimeProfile.BorelPartition k) (I : Finset (Fin K)) (D : RiffleLowerV2.RoundedTypeData P) (a e loss : ℝ),
      |Real.log ↑(RiffleLowerV2.roundedClass cuts hN P I D).card - a| ≤ e →
        |Real.log ↑(RiffleLowerV2.selectedClass cuts hN P I D).card -
                Real.log ↑(RiffleLowerV2.roundedClass cuts hN P I D).card| ≤
            loss →
          |RiffleLowerV2.typeH cuts hN P I D - a / TimeProfile.logScale N| ≤ (e + loss) / TimeProfile.logScale N
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.selectedJ_error_of_raw_cost

Source: `RiffleLowerV2/Types/WordEstimates.lean:144`. Kind: theorem.

```lean
RiffleLowerV2.Types.selectedJ_error_of_raw_cost : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N),
  2 ≤ N →
    ∀ (P : TimeProfile.BorelPartition k) (I : Finset (Fin K)) (D : RiffleLowerV2.RoundedTypeData P),
      (RiffleLowerV2.selectedClass cuts hN P I D).Nonempty →
        ∀ (a e : ℝ),
          (∀ x ∈ RiffleLowerV2.roundedClass cuts hN P I D, |-Real.log (RiffleLowerV2.massOn cuts x) - a| ≤ e) →
            |RiffleLowerV2.typeJ N D - a / TimeProfile.logScale N| ≤ (e + 1) / TimeProfile.logScale N
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.sum_cellPositionCount

Source: `RiffleLowerV2/Types/WordEstimates.lean:14`. Kind: theorem.

```lean
RiffleLowerV2.Types.sum_cellPositionCount : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K)),
  ∑ i : Fin P.cellCount, RiffleLowerV2.cellPositionCount cuts hN P I i = I.card
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.tiltedCost_eq_raw

Source: `RiffleLowerV2/Types/Truncation.lean:439`. Kind: theorem.

```lean
RiffleLowerV2.Types.tiltedCost_eq_raw : ∀ {k : ℕ} (p : TimeProfile.Simplex k) (alpha : ℝ),
  TimeProfile.tiltedCost p alpha =
    (∑ l : Fin k, TimeProfile.prob p l ^ alpha * TimeProfile.digitCost (TimeProfile.prob p l)) /
      TimeProfile.powerSum p alpha
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.tiltedCost_split

Source: `RiffleLowerV2/Types/Truncation.lean:460`. Kind: theorem.

```lean
RiffleLowerV2.Types.tiltedCost_split : ∀ {k : ℕ} (r p : TimeProfile.Simplex k) (xi alpha : ℝ),
  0 < TimeProfile.powerSum p alpha →
    0 < RiffleLowerV2.Types.restrictedSum r p xi alpha →
      TimeProfile.tiltedCost p alpha =
        RiffleLowerV2.Types.restrictedSum r p xi alpha / TimeProfile.powerSum p alpha *
            ∑ l : Fin k,
              RiffleLowerV2.Types.restrictedWeight r p xi alpha l * TimeProfile.digitCost (TimeProfile.prob p l) +
          RiffleLowerV2.Types.omittedCostSum r p xi alpha / TimeProfile.powerSum p alpha
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.tiltedEntropy_identity

Source: `RiffleLowerV2/Types/Truncation.lean:187`. Kind: theorem.

```lean
RiffleLowerV2.Types.tiltedEntropy_identity : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (p : TimeProfile.Simplex k) {alpha : ℝ},
      alpha ∈ Set.Icc 2 4 →
        TimeProfile.tiltedEntropy p alpha =
          alpha * TimeProfile.tiltedCost p alpha + Real.log (TimeProfile.powerSum p alpha)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.tiltedEntropy_term_bounds

Source: `RiffleLowerV2/Types/Truncation.lean:781`. Kind: theorem.

```lean
RiffleLowerV2.Types.tiltedEntropy_term_bounds : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (p : TimeProfile.Simplex k) {alpha : ℝ},
      alpha ∈ Set.Icc 2 4 →
        ∀ (l : Fin k),
          (0 ≤
              -if TimeProfile.tiltedWeight p alpha l = 0 then 0
                else TimeProfile.tiltedWeight p alpha l * Real.log (TimeProfile.tiltedWeight p alpha l)) ∧
            (-if TimeProfile.tiltedWeight p alpha l = 0 then 0
                else TimeProfile.tiltedWeight p alpha l * Real.log (TimeProfile.tiltedWeight p alpha l)) ≤
              4 * (TimeProfile.tiltedWeight p alpha l * TimeProfile.digitCost (TimeProfile.prob p l))
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.truncationCostConstant

Source: `RiffleLowerV2/Types/Truncation.lean:551`. Kind: definition.

```lean
RiffleLowerV2.Types.truncationCostConstant : ℕ → ℝ → ℝ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.truncationEntropyConstant

Source: `RiffleLowerV2/Types/Truncation.lean:554`. Kind: definition.

```lean
RiffleLowerV2.Types.truncationEntropyConstant : ℕ → ℝ → ℝ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.typeConstant

Source: `RiffleLowerV2/Types/Approximation.lean:12`. Kind: definition.

```lean
RiffleLowerV2.Types.typeConstant : ℕ → ℝ → ℝ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.typeConstant_pos

Source: `RiffleLowerV2/Types/Approximation.lean:15`. Kind: theorem.

```lean
RiffleLowerV2.Types.typeConstant_pos : ∀ (k : ℕ) {C : ℝ}, 0 ≤ C → 0 < RiffleLowerV2.Types.typeConstant k C
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.typeDataSpec_of_counts

Source: `RiffleLowerV2/Types/MassBins.lean:221`. Kind: theorem.

```lean
RiffleLowerV2.Types.typeDataSpec_of_counts : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N),
  2 ≤ N →
    ∀ (P : TimeProfile.BorelPartition k) (I : Finset (Fin K)) (D : RiffleLowerV2.RoundedTypeData P) {xi alpha C : ℝ},
      0 < xi →
        xi ≤ 1 →
          P.IsRegular xi C →
            (∀ (i : Fin P.cellCount), ∑ l : Fin k, D.count i l = RiffleLowerV2.cellPositionCount cuts hN P I i) →
              (∀ (i : Fin P.cellCount) (l : Fin k), TimeProfile.prob (P.rep i) l ≤ 2 * xi → D.count i l = 0) →
                (∀ (i : Fin P.cellCount) (l : Fin k),
                    |↑(D.count i l) -
                          ↑(RiffleLowerV2.cellPositionCount cuts hN P I i) *
                            RiffleLowerV2.retainedTilt P xi alpha i l| ≤
                      1) →
                  (∀ (i : Fin P.cellCount),
                      0 <
                        ∑ l : Fin k,
                          if 2 * xi < TimeProfile.prob (P.rep i) l then TimeProfile.prob (P.rep i) l ^ alpha else 0) →
                    ∀ (hC : (RiffleLowerV2.roundedClass cuts hN P I D).Nonempty),
                      (RiffleLowerV2.roundedClass cuts hN P I D).card =
                          ∏ i : Fin P.cellCount,
                            (RiffleLowerV2.cellPositionCount cuts hN P I i).factorial /
                              ∏ l : Fin k, (D.count i l).factorial →
                        RiffleLowerV2.TypeDataSpec cuts hN P I xi alpha
                          (RiffleLowerV2.Types.selectBinData cuts hN P I D hC)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.typeThreshold

Source: `RiffleLowerV2/Types/Rates.lean:22`. Kind: definition.

```lean
RiffleLowerV2.Types.typeThreshold : ℕ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.typeThreshold_ge_two

Source: `RiffleLowerV2/Types/Rates.lean:24`. Kind: theorem.

```lean
RiffleLowerV2.Types.typeThreshold_ge_two : 2 ≤ RiffleLowerV2.Types.typeThreshold
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.type_approximation_uniform

Source: `RiffleLowerV2/Types/Approximation.lean:85`. Kind: theorem.

```lean
RiffleLowerV2.Types.type_approximation_uniform : ∀ {k N K : ℕ},
  2 ≤ k →
    ∀ (cuts : TimeProfile.Cuts k N K) (hN : 0 < N),
      RiffleLowerV2.Types.typeThreshold ≤ N →
        ∀ (P : TimeProfile.BorelPartition k) (I : Finset (Fin K)) {xi C T alpha : ℝ},
          0 < xi →
            xi < 1 / (4 * ↑k) →
              0 ≤ C →
                0 < T →
                  P.IsRegular xi C →
                    alpha ∈ Set.Icc 2 4 →
                      ↑I.card ≤ T * TimeProfile.logScale N →
                        ∀ (D : RiffleLowerV2.RoundedTypeData P),
                          RiffleLowerV2.TypeDataSpec cuts hN P I xi alpha D →
                            RiffleLowerV2.TypeApproximation cuts hN P I alpha
                              (RiffleLowerV2.Types.typeConstant k C * T * xi * Real.log (1 / xi) +
                                RiffleLowerV2.Types.roundConstant k P.cellCount T (Real.log (1 / xi)) *
                                    (Real.log (TimeProfile.logScale N) + 1) /
                                  TimeProfile.logScale N)
                              D
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.wordCellCount_eq_fiberCard

Source: `RiffleLowerV2/Types/Counting.lean:236`. Kind: theorem.

```lean
RiffleLowerV2.Types.wordCellCount_eq_fiberCard : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) {I : Finset (Fin K)}
  (x : RiffleLowerV2.WordOn k I) (i : Fin P.cellCount) (l : Fin k),
  RiffleLowerV2.wordCellCount cuts hN P x i l = Fintype.card { j : ↥I // P.classify (cuts.profile hN ↑j) = i ∧ x j = l }
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.word_sum_identity

Source: `RiffleLowerV2/Types/WordEstimates.lean:29`. Kind: theorem.

```lean
RiffleLowerV2.Types.word_sum_identity : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K))
  (D : RiffleLowerV2.RoundedTypeData P),
  ∀ x ∈ RiffleLowerV2.roundedClass cuts hN P I D,
    ∀ (v : Fin P.cellCount → Fin k → ℝ),
      ∑ j : ↥I, v (P.classify (cuts.profile hN ↑j)) (x j) = ∑ i : Fin P.cellCount, ∑ l : Fin k, ↑(D.count i l) * v i l
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.xlogx

Source: `RiffleLowerV2/Types/EntropyBounds.lean:10`. Kind: definition.

```lean
RiffleLowerV2.Types.xlogx : ℝ → ℝ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.xlogx_rounding_bound

Source: `RiffleLowerV2/Types/EntropyBounds.lean:111`. Kind: theorem.

```lean
RiffleLowerV2.Types.xlogx_rounding_bound : ∀ {n x y : ℝ},
  0 ≤ n →
    0 ≤ x →
      x ≤ n →
        0 ≤ y → y ≤ n → |x - y| ≤ 1 → |RiffleLowerV2.Types.xlogx x - RiffleLowerV2.Types.xlogx y| ≤ Real.log (n + 1) + 2
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Types.xlogx_zero

Source: `RiffleLowerV2/Types/EntropyBounds.lean:12`. Kind: theorem.

```lean
RiffleLowerV2.Types.xlogx_zero : RiffleLowerV2.Types.xlogx 0 = 0
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.
