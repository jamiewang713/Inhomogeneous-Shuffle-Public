import EdgeLocalization.Exponent.Model

/-! Frozen exponent theorems X.01–X.05 and X.15. -/

noncomputable section

namespace EdgeLocalization

theorem legalPrefix_of_prefix {K k A M : ℕ} (n : Fin K → Fin k → ℕ)
    (hM : M ≤ K) (hAM : A ≤ M) (w : Fin A → Fin k) (x : Fin M → Fin k)
    (hprefix : ∀ t, x (Fin.castLE hAM t) = w t) (hx : legalPrefix n hM x) :
    legalPrefix n (hAM.trans hM) w := by
  intro t
  change 0 < n (Fin.castLE hM (Fin.castLE hAM t)) (w t)
  rw [← hprefix t]
  exact hx (Fin.castLE hAM t)

theorem prefixMean_pos_of_legal (N : ℕ) {K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hM : M ≤ K) (x : Fin M → Fin k)
    (hN : 2 ≤ N) (hx : legalPrefix n hM x) :
    0 < prefixMean N n hM x := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  unfold prefixMean prefixMass singleFactor
  apply mul_pos hNr
  apply Finset.prod_pos
  intro t _
  exact div_pos (by exact_mod_cast hx t) hNr

theorem log_prefixMean_of_legal (N : ℕ) {K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hM : M ≤ K) (x : Fin M → Fin k)
    (hN : 2 ≤ N) (hx : legalPrefix n hM x) :
    Real.log (prefixMean N n hM x) = Real.log (N : ℝ) -
      ∑ t : Fin M, Real.log ((N : ℝ) / (n (Fin.castLE hM t) (x t) : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hc : ∀ t : Fin M, (0 : ℝ) < n (Fin.castLE hM t) (x t) := by
    intro t
    exact_mod_cast hx t
  have hf : ∀ t : Fin M, 0 < singleFactor N (n (Fin.castLE hM t)) (x t) := by
    intro t
    exact div_pos (hc t) hNr
  have hp : 0 < prefixMass N n hM x :=
    Finset.prod_pos (fun t _ => hf t)
  calc
    Real.log (prefixMean N n hM x) = Real.log (N : ℝ) +
        ∑ t : Fin M, Real.log (singleFactor N (n (Fin.castLE hM t)) (x t)) := by
      rw [prefixMean, Real.log_mul hNr.ne' hp.ne', prefixMass,
        Real.log_prod _ _ (fun t _ => (hf t).ne')]
    _ = Real.log (N : ℝ) +
        ∑ t : Fin M, -Real.log ((N : ℝ) / (n (Fin.castLE hM t) (x t) : ℝ)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      rw [singleFactor, Real.log_div (hc t).ne' hNr.ne',
        Real.log_div hNr.ne' (hc t).ne']
      ring
    _ = _ := by rw [Finset.sum_neg_distrib, sub_eq_add_neg]

theorem log_prefixMean_extension (N : ℕ) {K k A M : ℕ}
    (n : Fin K → Fin k → ℕ) (hM : M ≤ K) (hAM : A ≤ M)
    (w : Fin A → Fin k) (x : Fin M → Fin k)
    (hprefix : ∀ t, x (Fin.castLE hAM t) = w t)
    (hN : 2 ≤ N) (hx : legalPrefix n hM x) :
    Real.log (prefixMean N n hM x) = Real.log (prefixMean N n (hAM.trans hM) w) -
      ∑ t ∈ Finset.univ.filter (fun t : Fin M => A ≤ t.val),
        Real.log ((N : ℝ) / (n (Fin.castLE hM t) (x t) : ℝ)) := by
  let f : Fin M → ℝ := fun t =>
    Real.log ((N : ℝ) / (n (Fin.castLE hM t) (x t) : ℝ))
  have hfirst :
      (∑ t : Fin A,
        Real.log ((N : ℝ) / (n (Fin.castLE (hAM.trans hM) t) (w t) : ℝ))) =
      ∑ t ∈ Finset.univ.filter (fun t : Fin M => t.val < A), f t := by
    refine Finset.sum_bij (fun t _ => Fin.castLE hAM t) ?_ ?_ ?_ ?_
    · intro t _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.isLt⟩
    · intro t ht u hu htu
      exact Fin.ext (congrArg (fun z : Fin M => z.val) htu)
    · intro t ht
      refine ⟨⟨t.val, (Finset.mem_filter.mp ht).2⟩, Finset.mem_univ _, ?_⟩
      rfl
    · intro t _
      dsimp [f]
      rw [hprefix t]
      rfl
  have hsplit := Finset.sum_filter_add_sum_filter_not
    Finset.univ (fun t : Fin M => t.val < A) f
  simp only [not_lt] at hsplit
  rw [← hfirst] at hsplit
  have hw := legalPrefix_of_prefix n hM hAM w x hprefix hx
  rw [log_prefixMean_of_legal N n hM x hN hx,
    log_prefixMean_of_legal N n (hAM.trans hM) w hN hw]
  dsimp [f] at hsplit
  linarith

theorem prefixMean_eq_rpow_ambientSizeExponent (N : ℕ) {K k A M : ℕ}
    (n : Fin K → Fin k → ℕ) (hM : M ≤ K) (hAM : A ≤ M)
    (w : Fin A → Fin k) (x : Fin M → Fin k) (b : ℝ)
    (hprefix : ∀ t, x (Fin.castLE hAM t) = w t)
    (hN : 2 ≤ N) (hx : legalPrefix n hM x) :
    prefixMean N n hM x = Real.rpow (N : ℝ)
      (ambientSizeExponent N n hM A b x +
        ambientMeanError N n (hAM.trans hM) w b) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  have hexponent : ambientSizeExponent N n hM A b x +
        ambientMeanError N n (hAM.trans hM) w b =
      Real.log (prefixMean N n hM x) / Real.log (N : ℝ) := by
    rw [ambientSizeExponent, ambientMeanError,
      log_prefixMean_extension N n hM hAM w x hprefix hN hx]
    ring
  rw [hexponent]
  change prefixMean N n hM x =
    (N : ℝ) ^ (Real.log (prefixMean N n hM x) / Real.log (N : ℝ))
  rw [Real.rpow_def_of_pos hNr]
  have hcancel : Real.log (N : ℝ) *
      (Real.log (prefixMean N n hM x) / Real.log (N : ℝ)) =
      Real.log (prefixMean N n hM x) := by
    field_simp [hlog]
  rw [hcancel, Real.exp_log (prefixMean_pos_of_legal N n hM x hN hx)]

theorem ambientMeanError_root (N : ℕ) {K k : ℕ}
    (n : Fin K → Fin k → ℕ) (w : Fin 0 → Fin k) (hN : 2 ≤ N) :
    ambientMeanError N n (Nat.zero_le K) w 1 = 0 := by
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  simp [ambientMeanError, prefixMean, prefixMass, hlog]

end EdgeLocalization
