import EdgeLocalization.Asymptotic.Model
import EdgeLocalization.Exponent.Model
import EdgeLocalization.Collision.Matrix

/-! Frozen asymptotic ambient-error theorems A.01–A.02. -/

namespace EdgeLocalization

theorem hasSizeExponent_eventually_log_error_le (f : ℕ → ℝ) (b : ℝ)
    (hsize : HasSizeExponent f b) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      |Real.log (f N) / Real.log (N : ℝ) - b| ≤ ε := by
  obtain ⟨N1, hN1⟩ := hsize ε hε
  refine ⟨max N1 2, le_max_right _ _, ?_⟩
  intro N hN
  have h2 : 2 ≤ N := le_trans (le_max_right N1 2) hN
  have h1 : N1 ≤ N := le_trans (le_max_left N1 2) hN
  obtain ⟨hlower, hupper⟩ := hN1 N h1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNgt : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos hNgt
  have hlowerpos : 0 < Real.rpow (N : ℝ) (b - ε) :=
    Real.rpow_pos_of_pos hNpos _
  have hfpos : 0 < f N := lt_of_lt_of_le hlowerpos hlower
  have hloglower := Real.log_le_log hlowerpos hlower
  have hlogupper := Real.log_le_log hfpos hupper
  change Real.log ((N : ℝ) ^ (b - ε)) ≤ Real.log (f N) at hloglower
  change Real.log (f N) ≤ Real.log ((N : ℝ) ^ (b + ε)) at hlogupper
  rw [Real.log_rpow hNpos] at hloglower hlogupper
  have hlower' : b - ε ≤ Real.log (f N) / Real.log (N : ℝ) :=
    (le_div_iff₀ hlogpos).mpr hloglower
  have hupper' : Real.log (f N) / Real.log (N : ℝ) ≤ b + ε :=
    (div_le_iff₀ hlogpos).mpr hlogupper
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem ambientMeanError_eventually_abs_le
    (k : ℕ) (K A : ℕ → ℕ)
    (n : ∀ N : ℕ, Fin (K N) → Fin k → ℕ)
    (hn : ∀ (N : ℕ) (j : Fin (K N)), ∑ a, n N j a = N)
    (hA : ∀ N : ℕ, A N ≤ K N)
    (w : ∀ N : ℕ, Fin (A N) → Fin k) (b : ℝ)
    (hsize : HasSizeExponent
      (fun N => (matrixLaw (n N) (hn N)).expectation
        (fun ω => (occupancyCount N (sortedRows (n N) ω) (prefixWord (w N)) : ℝ))) b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      |ambientMeanError N (n N) (hA N) (w N) b| ≤ ε := by
  obtain ⟨N0, hN0, herr⟩ := hasSizeExponent_eventually_log_error_le
    (fun N => (matrixLaw (n N) (hn N)).expectation
      (fun ω => (occupancyCount N (sortedRows (n N) ω) (prefixWord (w N)) : ℝ)))
    b hsize ε hε
  refine ⟨N0, hN0, ?_⟩
  intro N hN
  have h := herr N hN
  rw [matrix_expected_sorted_occupancy (n N) (hn N) (hA N) (w N)] at h
  exact h

end EdgeLocalization
