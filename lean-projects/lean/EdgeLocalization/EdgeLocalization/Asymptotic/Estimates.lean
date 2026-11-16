import EdgeLocalization.Asymptotic.Error
import EdgeLocalization.Relative.Estimates

/-! Frozen uniform asymptotic density consequences A.03–A.07. -/

namespace EdgeLocalization

theorem matrix_relative_density_eventually_le_ambient_tail_exponent (k : ℕ) (K A : ℕ → ℕ)
    (n : ∀ N : ℕ, Fin (K N) → Fin k → ℕ)
    (hn : ∀ (N : ℕ) (j : Fin (K N)), ∑ a, n N j a = N)
    (hA : ∀ N : ℕ, A N ≤ K N) (w : ∀ N : ℕ, Fin (A N) → Fin k)
    (b : ℝ)
    (hsize : HasSizeExponent
      (fun N => (matrixLaw (n N) (hn N)).expectation
        (fun ω => (occupancyCount N (sortedRows (n N) ω) (prefixWord (w N)) : ℝ))) b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      ∀ (M : ℕ) (hM : M ≤ K N) (hAM : A N ≤ M)
        (x : Fin M → Fin k)
        (hprefix : ∀ t : Fin (A N), x (Fin.castLE hAM t) = w N t)
        (hx : legalPrefix (n N) hM x),
      relativeEdgeDensity (matrixLaw (n N) (hn N)) N (sortedRows (n N))
          (prefixWord x)
          (fun ω => ambientLeft N (sortedRows (n N) ω) (prefixWord (w N))) ≤
        Real.rpow (N : ℝ) (4 * ambientSizeExponent N (n N) hM (A N) b x +
          2 * tailEdgeExponent N (n N) M + ε) / 4 := by
  obtain ⟨N0, hN0, herror⟩ := ambientMeanError_eventually_abs_le
    k K A n hn hA w b hsize (ε / 4) (by positivity)
  refine ⟨N0, hN0, ?_⟩
  intro N hNN M hM hAM x hprefix hx
  have hN : 2 ≤ N := hN0.trans hNN
  have hbase : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have he : ambientMeanError N (n N) (hAM.trans hM) (w N) b ≤ ε / 4 :=
    (abs_le.mp (herror N hNN)).2
  calc
    _ ≤ Real.rpow (N : ℝ) (4 * (ambientSizeExponent N (n N) hM (A N) b x +
        ambientMeanError N (n N) (hAM.trans hM) (w N) b) +
        2 * tailEdgeExponent N (n N) M) / 4 :=
      matrix_relative_density_le_ambient_tail_exponent
        (n N) (hn N) hM hAM (w N) x b hprefix hN hx
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply Real.rpow_le_rpow_of_exponent_le hbase
      linarith only [he]

theorem matrix_relative_density_eventually_le_small_coarse_exponent (k : ℕ) (K A : ℕ → ℕ)
    (n : ∀ N : ℕ, Fin (K N) → Fin k → ℕ)
    (hn : ∀ (N : ℕ) (j : Fin (K N)), ∑ a, n N j a = N)
    (hA : ∀ N : ℕ, A N ≤ K N) (w : ∀ N : ℕ, Fin (A N) → Fin k)
    (b : ℝ)
    (hsize : HasSizeExponent
      (fun N => (matrixLaw (n N) (hn N)).expectation
        (fun ω => (occupancyCount N (sortedRows (n N) ω) (prefixWord (w N)) : ℝ))) b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ δ : ℝ,
      ∀ (M : ℕ) (hM : M ≤ K N) (hAM : A N ≤ M)
        (x : Fin M → Fin k)
        (hprefix : ∀ t : Fin (A N), x (Fin.castLE hAM t) = w N t)
        (hx : legalPrefix (n N) hM x)
        (hsmall : ambientSizeExponent N (n N) hM (A N) b x < 2 * δ),
      relativeEdgeDensity (matrixLaw (n N) (hn N)) N (sortedRows (n N))
          (prefixWord x)
          (fun ω => ambientLeft N (sortedRows (n N) ω) (prefixWord (w N))) ≤
        Real.rpow (N : ℝ) (2 * tailEdgeExponent N (n N) M + 8 * δ + ε) / 4 := by
  obtain ⟨N0, hN0, hbound⟩ :=
    matrix_relative_density_eventually_le_ambient_tail_exponent
      k K A n hn hA w b hsize ε hε
  refine ⟨N0, hN0, ?_⟩
  intro N hNN δ M hM hAM x hprefix hx hsmall
  have hN : 2 ≤ N := hN0.trans hNN
  have hbase : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  calc
    _ ≤ Real.rpow (N : ℝ) (4 * ambientSizeExponent N (n N) hM (A N) b x +
        2 * tailEdgeExponent N (n N) M + ε) / 4 :=
      hbound N hNN M hM hAM x hprefix hx
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply Real.rpow_le_rpow_of_exponent_le hbase
      linarith only [hsmall]

theorem matrix_relative_density_eventually_le_small_singleton_exponent (k : ℕ) (K A : ℕ → ℕ)
    (n : ∀ N : ℕ, Fin (K N) → Fin k → ℕ)
    (hn : ∀ (N : ℕ) (j : Fin (K N)), ∑ a, n N j a = N)
    (hA : ∀ N : ℕ, A N ≤ K N) (w : ∀ N : ℕ, Fin (A N) → Fin k)
    (b : ℝ)
    (hsize : HasSizeExponent
      (fun N => (matrixLaw (n N) (hn N)).expectation
        (fun ω => (occupancyCount N (sortedRows (n N) ω) (prefixWord (w N)) : ℝ))) b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ δ : ℝ,
      ∀ (M : ℕ) (hM : M ≤ K N) (hAM : A N ≤ M)
        (x : Fin M → Fin k)
        (hprefix : ∀ t : Fin (A N), x (Fin.castLE hAM t) = w N t)
        (hx : legalPrefix (n N) hM x)
        (hsmall : ambientSizeExponent N (n N) hM (A N) b x < 2 * δ),
      relativeEdgeDensity (matrixLaw (n N) (hn N)) N (sortedRows (n N))
          (prefixWord x)
          (fun ω => ambientLeft N (sortedRows (n N) ω) (prefixWord (w N))) ≤
        Real.rpow (N : ℝ) (2 * ambientSizeExponent N (n N) hM (A N) b x +
          2 * tailEdgeExponent N (n N) M + 4 * δ + ε) / 4 := by
  obtain ⟨N0, hN0, hbound⟩ :=
    matrix_relative_density_eventually_le_ambient_tail_exponent
      k K A n hn hA w b hsize ε hε
  refine ⟨N0, hN0, ?_⟩
  intro N hNN δ M hM hAM x hprefix hx hsmall
  have hN : 2 ≤ N := hN0.trans hNN
  have hbase : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  calc
    _ ≤ Real.rpow (N : ℝ) (4 * ambientSizeExponent N (n N) hM (A N) b x +
        2 * tailEdgeExponent N (n N) M + ε) / 4 :=
      hbound N hNN M hM hAM x hprefix hx
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply Real.rpow_le_rpow_of_exponent_le hbase
      linarith only [hsmall]

theorem matrix_relative_density_eventually_le_ambient_size_exponent (k : ℕ) (K A : ℕ → ℕ)
    (n : ∀ N : ℕ, Fin (K N) → Fin k → ℕ)
    (hn : ∀ (N : ℕ) (j : Fin (K N)), ∑ a, n N j a = N)
    (hA : ∀ N : ℕ, A N ≤ K N) (w : ∀ N : ℕ, Fin (A N) → Fin k)
    (b : ℝ)
    (hsize : HasSizeExponent
      (fun N => (matrixLaw (n N) (hn N)).expectation
        (fun ω => (occupancyCount N (sortedRows (n N) ω) (prefixWord (w N)) : ℝ))) b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      ∀ (M : ℕ) (hM : M ≤ K N) (hAM : A N ≤ M)
        (x : Fin M → Fin k)
        (hprefix : ∀ t : Fin (A N), x (Fin.castLE hAM t) = w N t)
        (hx : legalPrefix (n N) hM x),
      relativeEdgeDensity (matrixLaw (n N) (hn N)) N (sortedRows (n N))
          (prefixWord x)
          (fun ω => ambientLeft N (sortedRows (n N) ω) (prefixWord (w N))) ≤
        Real.rpow (N : ℝ) (ambientSizeExponent N (n N) hM (A N) b x + ε) := by
  obtain ⟨N0, hN0, herror⟩ := ambientMeanError_eventually_abs_le
    k K A n hn hA w b hsize ε hε
  refine ⟨N0, hN0, ?_⟩
  intro N hNN M hM hAM x hprefix hx
  have hN : 2 ≤ N := hN0.trans hNN
  have hbase : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have he : ambientMeanError N (n N) (hAM.trans hM) (w N) b ≤ ε :=
    (abs_le.mp (herror N hNN)).2
  calc
    _ ≤ Real.rpow (N : ℝ) (ambientSizeExponent N (n N) hM (A N) b x +
        ambientMeanError N (n N) (hAM.trans hM) (w N) b) :=
      matrix_relative_density_le_ambient_size_exponent
        (n N) (hn N) hM hAM (w N) x b hprefix hN hx
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le hbase
      linarith only [he]

theorem matrix_relative_density_eventually_terminal_exponent (k : ℕ) (K A : ℕ → ℕ)
    (n : ∀ N : ℕ, Fin (K N) → Fin k → ℕ)
    (hn : ∀ (N : ℕ) (j : Fin (K N)), ∑ a, n N j a = N)
    (hA : ∀ N : ℕ, A N ≤ K N) (w : ∀ N : ℕ, Fin (A N) → Fin k)
    (b : ℝ)
    (hsize : HasSizeExponent
      (fun N => (matrixLaw (n N) (hn N)).expectation
        (fun ω => (occupancyCount N (sortedRows (n N) ω) (prefixWord (w N)) : ℝ))) b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      ∀ (x : Fin (K N) → Fin k)
        (hprefix : ∀ t : Fin (A N), x (Fin.castLE (hA N) t) = w N t)
        (hx : legalPrefix (n N) (Nat.le_refl (K N)) x),
      relativeEdgeDensity (matrixLaw (n N) (hn N)) N (sortedRows (n N))
          (prefixWord x)
          (fun ω => ambientLeft N (sortedRows (n N) ω) (prefixWord (w N))) ≤
        Real.rpow (N : ℝ)
          (ambientSizeExponent N (n N) (Nat.le_refl (K N)) (A N) b x + ε) := by
  obtain ⟨N0, hN0, hbound⟩ :=
    matrix_relative_density_eventually_le_ambient_size_exponent
      k K A n hn hA w b hsize ε hε
  refine ⟨N0, hN0, ?_⟩
  intro N hNN x hprefix hx
  exact hbound N hNN (K N) (Nat.le_refl (K N)) (hA N) x hprefix hx

end EdgeLocalization
