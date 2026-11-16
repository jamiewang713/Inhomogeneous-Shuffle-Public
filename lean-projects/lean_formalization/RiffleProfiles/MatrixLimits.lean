import RiffleProfiles.TailLimits
import RiffleProfiles.MatrixTruncation

/-! Frozen A06: ordered small-chi bounds for the actual expected row counts. -/

set_option autoImplicit false
noncomputable section

namespace RiffleProfiles

attribute [local instance] Classical.propDecidable

private theorem twice_rpow_le_succ (N : ℕ) (hN : 2 ≤ N) (r : ℝ) :
    2 * (N : ℝ) ^ r ≤ (N : ℝ) ^ (r + 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
  calc
    2 * (N : ℝ) ^ r ≤ (N : ℝ) * (N : ℝ) ^ r :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hN) (Real.rpow_pos_of_pos hN0 r).le
    _ = (N : ℝ) ^ (r + 1) := by rw [Real.rpow_add hN0, Real.rpow_one]; ring

theorem exists_boundary_truncation_parameters (k : ℕ) (T C0 : ℝ)
    (_hk : 2 ≤ k) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∃ χ0 : ℝ, 0 < χ0 ∧
      ∀ D : Riffle.Model, D.k = k → 2 ≤ D.N →
        (D.K : ℝ) ≤ T * TimeProfile.logScale D.N →
        ∀ A : Riffle.Setup D, A.C = C → 0 < A.chi → A.chi < χ0 →
          (Shuffle.fixedMatrixLaw (modelHistogram D)).expect
            (fun matrix => ((Finset.univ.filter (fun r : Fin D.N =>
              Riffle.fullList (modelRowWord D matrix r) ∈
                discardedBoundary A .left ∪ discardedBoundary A .right)).card : ℝ)) ≤
            (D.N : ℝ) ^ (-C0) := by
  let C : ℝ := |C0| + 4
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨χ0, hχ0, _hχ01, htail⟩ :=
    boundary_tailWeight_small_chi k T C 1 hT hC zero_lt_one
  refine ⟨C, hC, χ0, hχ0, ?_⟩
  intro D hdk hN hK A hAC hχ hχlt
  have hb : (D.N : ℝ) * tailWeight D.K (Nat.floor (boundaryThreshold A) + 1)
        ((D.k : ℝ) * A.chi) ≤ (D.N : ℝ) ^ (1 - C + 1) := by
    simpa only [hdk, boundaryThreshold, hAC, chiLog, TimeProfile.logScale] using
      htail A.chi hχ hχlt D.N D.K hN hK
  calc
    _ ≤ 2 * ((D.N : ℝ) * tailWeight D.K (Nat.floor (boundaryThreshold A) + 1)
        ((D.k : ℝ) * A.chi)) := model_discardedBoundary_union_expected_rows_le A
    _ ≤ 2 * (D.N : ℝ) ^ (1 - C + 1) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ ≤ (D.N : ℝ) ^ ((1 - C + 1) + 1) := twice_rpow_le_succ D.N hN _
    _ ≤ (D.N : ℝ) ^ (-C0) := by
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hN))
      dsimp [C]
      linarith [le_abs_self C0]

theorem exists_exceptional_truncation_parameters (k : ℕ) (T C0 : ℝ)
    (_hk : 2 ≤ k) (hT : 0 ≤ T) :
    ∃ χ0 : ℝ, 0 < χ0 ∧ χ0 < 1 ∧
      ∀ χ : ℝ, 0 < χ → χ < χ0 →
        ∀ D : Riffle.Model, D.k = k →
          (D.K : ℝ) ≤ T * TimeProfile.logScale D.N →
          ∀ (Creg : ℝ) (P : TimeProfile.BorelPartition D.k), P.IsRegular χ Creg →
            ∀ v M : Riffle.FullIndex D → ℕ,
              (Shuffle.fixedMatrixLaw (modelHistogram D)).expect
                (fun matrix => ((Finset.univ.filter (fun r : Fin D.N =>
                  exceptionalAllowance χ <
                    ((sourceExceptionalPositions (modelColumnProfile D) P χ v M
                      (modelRowWord D matrix r)).card : ℝ) /
                        TimeProfile.logScale D.N)).card : ℝ)) ≤
                (D.N : ℝ) ^ (-C0) := by
  obtain ⟨χ0, hχ0, hχ01, htail⟩ := exceptional_tailWeight_small_chi k T C0 hT
  refine ⟨χ0, hχ0, hχ01, ?_⟩
  intro χ hχ hχlt D hdk hK Creg P hreg v M
  have hN : 2 ≤ D.N := by have := D.one_lt_N; omega
  have hα := (exceptionalAllowance_pos hχ (hχlt.trans hχ01)).le
  have ht := htail χ hχ hχlt D.N D.K hN hK
  have hb := model_exceptionalPrefix_expected_rows_le D P χ Creg
    (exceptionalAllowance χ) v M hreg hχ hα
  exact hb.trans (by simpa only [hdk] using ht)

end RiffleProfiles
