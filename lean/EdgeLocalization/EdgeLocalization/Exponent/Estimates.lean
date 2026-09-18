import EdgeLocalization.Exponent.Mean
import EdgeLocalization.Exponent.Tail
import EdgeLocalization.Collision.Estimates

/-! Frozen density exponent consequences X.09–12 and X.14. -/

namespace EdgeLocalization

theorem matrix_internal_density_le_ambient_tail_exponent {N K k A M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (hM : M ≤ K) (hAM : A ≤ M) (w : Fin A → Fin k) (x : Fin M → Fin k)
    (b : ℝ) (hprefix : ∀ t, x (Fin.castLE hAM t) = w t)
    (hN : 2 ≤ N) (hx : legalPrefix n hM x) :
    edgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord x) ≤
      Real.rpow (N : ℝ) (4 * (ambientSizeExponent N n hM A b x +
        ambientMeanError N n (hAM.trans hM) w b) +
        2 * tailEdgeExponent N n M) / 4 := by
  let L := ambientSizeExponent N n hM A b x
  let ε := ambientMeanError N n (hAM.trans hM) w b
  let E := tailEdgeExponent N n M
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hmean : prefixMean N n hM x = Real.rpow (N : ℝ) (L + ε) :=
    prefixMean_eq_rpow_ambientSizeExponent N n hM hAM w x b hprefix hN hx
  have htail : tailCollisionFactor N n M ≤ Real.rpow (N : ℝ) E :=
    tailCollisionFactor_le_rpow_tailEdgeExponent N n hn M hN
  have htail0 : 0 ≤ tailCollisionFactor N n M := (tail_factors_nonneg N n M).1
  have hsquare : (tailCollisionFactor N n M) ^ 2 ≤ (Real.rpow (N : ℝ) E) ^ 2 := by
    simpa only [pow_two] using mul_le_mul htail htail htail0 (le_trans htail0 htail)
  have hfour : (Real.rpow (N : ℝ) (L + ε)) ^ 4 =
      Real.rpow (N : ℝ) (4 * (L + ε)) := by
    change ((N : ℝ) ^ (L + ε)) ^ 4 = (N : ℝ) ^ (4 * (L + ε))
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hNpos)]
    congr 1
    ring
  have htwo : (Real.rpow (N : ℝ) E) ^ 2 = Real.rpow (N : ℝ) (2 * E) := by
    change ((N : ℝ) ^ E) ^ 2 = (N : ℝ) ^ (2 * E)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hNpos)]
    congr 1
    ring
  change edgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord x) ≤
    Real.rpow (N : ℝ) (4 * (L + ε) + 2 * E) / 4
  calc
    _ ≤ (prefixMean N n hM x) ^ 4 * (tailCollisionFactor N n M) ^ 2 / 4 :=
      matrix_internal_density_le_mean_tail_fourth n hn hM x
    _ ≤ (prefixMean N n hM x) ^ 4 * (Real.rpow (N : ℝ) E) ^ 2 / 4 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsquare
          (pow_nonneg (le_of_lt (prefixMean_pos_of_legal N n hM x hN hx)) 4))
        (by norm_num)
    _ = _ := by
      rw [hmean, hfour, htwo]
      change (N : ℝ) ^ (4 * (L + ε)) * (N : ℝ) ^ (2 * E) / 4 =
        (N : ℝ) ^ (4 * (L + ε) + 2 * E) / 4
      rw [← Real.rpow_add hNpos]

theorem matrix_internal_density_le_small_coarse_exponent {N K k A M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (hM : M ≤ K) (hAM : A ≤ M) (w : Fin A → Fin k) (x : Fin M → Fin k)
    (b : ℝ) (hprefix : ∀ t, x (Fin.castLE hAM t) = w t)
    (hN : 2 ≤ N) (hx : legalPrefix n hM x)
    (δ : ℝ) (hsmall : ambientSizeExponent N n hM A b x < 2 * δ) :
    edgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord x) ≤
      Real.rpow (N : ℝ) (2 * tailEdgeExponent N n M + 8 * δ +
        4 * ambientMeanError N n (hAM.trans hM) w b) / 4 := by
  have hNone : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  calc
    _ ≤ Real.rpow (N : ℝ) (4 * (ambientSizeExponent N n hM A b x +
        ambientMeanError N n (hAM.trans hM) w b) +
        2 * tailEdgeExponent N n M) / 4 :=
      matrix_internal_density_le_ambient_tail_exponent n hn hM hAM w x b hprefix hN hx
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply Real.rpow_le_rpow_of_exponent_le hNone
      linarith only [hsmall]

theorem matrix_internal_density_le_small_singleton_exponent {N K k A M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (hM : M ≤ K) (hAM : A ≤ M) (w : Fin A → Fin k) (x : Fin M → Fin k)
    (b : ℝ) (hprefix : ∀ t, x (Fin.castLE hAM t) = w t)
    (hN : 2 ≤ N) (hx : legalPrefix n hM x)
    (δ : ℝ) (hsmall : ambientSizeExponent N n hM A b x < 2 * δ) :
    edgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord x) ≤
      Real.rpow (N : ℝ) (2 * ambientSizeExponent N n hM A b x +
        2 * tailEdgeExponent N n M + 4 * δ +
        4 * ambientMeanError N n (hAM.trans hM) w b) / 4 := by
  have hNone : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  calc
    _ ≤ Real.rpow (N : ℝ) (4 * (ambientSizeExponent N n hM A b x +
        ambientMeanError N n (hAM.trans hM) w b) +
        2 * tailEdgeExponent N n M) / 4 :=
      matrix_internal_density_le_ambient_tail_exponent n hn hM hAM w x b hprefix hN hx
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply Real.rpow_le_rpow_of_exponent_le hNone
      linarith only [hsmall]

theorem matrix_internal_density_le_ambient_size_exponent {N K k A M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (hM : M ≤ K) (hAM : A ≤ M) (w : Fin A → Fin k) (x : Fin M → Fin k)
    (b : ℝ) (hprefix : ∀ t, x (Fin.castLE hAM t) = w t)
    (hN : 2 ≤ N) (hx : legalPrefix n hM x) :
    edgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord x) ≤
      Real.rpow (N : ℝ) (ambientSizeExponent N n hM A b x +
        ambientMeanError N n (hAM.trans hM) w b) := by
  calc
    _ ≤ prefixMean N n hM x := matrix_internal_density_le_prefixMean n hn hM x
    _ = _ := prefixMean_eq_rpow_ambientSizeExponent N n hM hAM w x b hprefix hN hx

theorem matrix_internal_density_terminal_exponent {N K k A : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N) (hA : A ≤ K)
    (w : Fin A → Fin k) (x : Fin K → Fin k) (b : ℝ)
    (hprefix : ∀ t, x (Fin.castLE hA t) = w t)
    (hN : 2 ≤ N) (hx : legalPrefix n (Nat.le_refl K) x) :
    edgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord x) ≤
      Real.rpow (N : ℝ) (ambientSizeExponent N n (Nat.le_refl K) A b x +
        ambientMeanError N n hA w b) := by
  exact matrix_internal_density_le_ambient_size_exponent
    n hn (Nat.le_refl K) hA w x b hprefix hN hx

end EdgeLocalization
