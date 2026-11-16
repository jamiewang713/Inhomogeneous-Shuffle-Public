import RiffleLowerV2.Witness.Main
import RiffleLowerV2.Shared.Adapters

noncomputable section
open scoped BigOperators
open Set TimeProfile
namespace RiffleLowerV2.Localization

theorem gridTime_nonneg {N : ℕ} (hN : 2 ≤ N) (m : ℕ) : 0 ≤ gridTime N m := by
  exact div_nonneg (Nat.cast_nonneg _) (logScale_pos hN).le

theorem gridTime_mono {N : ℕ} (hN : 2 ≤ N) {a b : ℕ} (hab : a ≤ b) :
    gridTime N a ≤ gridTime N b := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast hab) (logScale_pos hN).le

theorem gridTime_le_horizon {N K m : ℕ} (hN : 2 ≤ N) (hm : m ≤ K) :
    gridTime N m ≤ horizon N K := gridTime_mono hN hm

theorem columnSet_size {N : ℕ} (hN : 2 ≤ N) {T : ℝ} (hT : 0 ≤ T) (a b : ℕ) :
    ((columnSet (horizonDepth N T) a b).card : ℝ) ≤ T*logScale N := by
  have hc : (columnSet (horizonDepth N T) a b).card ≤ horizonDepth N T := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
  have hcr : ((columnSet (horizonDepth N T) a b).card : ℝ) ≤ horizonDepth N T := by
    exact_mod_cast hc
  exact hcr.trans (Nat.floor_le (mul_nonneg hT (logScale_pos hN).le))

/-- Translate the shared finite-sum type estimate to exact empirical grid costs. -/
theorem typeApproximation_grid {k N K : ℕ} (hN2 : 2 ≤ N)
    (cuts : Cuts k N K) (hN : 0 < N) (P : BorelPartition k)
    {a b : ℕ} (hab : a ≤ b) (alpha err : ℝ) (D : RoundedTypeData P)
    (h : TypeApproximation cuts hN P (columnSet K a b) alpha err D) :
    |typeJ N D - J cuts hN alpha (gridTime N a) (gridTime N b)| +
      |typeH cuts hN P (columnSet K a b) D - H cuts hN alpha (gridTime N a) (gridTime N b)| ≤ err := by
  simpa only [J, H, empiricalIntegral_grid hN2 _ a b hab, gridSum, columnSet,
    TypeApproximation] using h

theorem bridge_grid_cost_bounds {k N K : ℕ} (hk : 2 ≤ k) (hN2 : 2 ≤ N)
    (cuts : Cuts k N K) (hN : 0 < N) {mu bl : ℕ} {rho : ℝ}
    (hrho : 0 < rho) (hbl : bl = ⌈2*rho*logScale N⌉₊) (hbound : mu+bl ≤ K) :
    let u := gridTime N mu
    let v := gridTime N (mu+bl)
    let d := (2*rho+1/logScale N)*Real.log k
    0 ≤ J cuts hN 2 u v ∧ J cuts hN 2 u v ≤ d ∧
      0 ≤ H cuts hN 2 u v ∧ H cuts hN 2 u v ≤ d := by
  dsimp only
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
  have hL := logScale_pos hN2
  have huv := gridTime_mono hN2 (Nat.le_add_right mu bl)
  have ⟨hj0, hjle⟩ := Witness.J_bounds Witness.oneColumnTilt hk hN2 cuts hN
    (show (2 : ℝ) ∈ Icc (2 : ℝ) 4 by norm_num) (gridTime_nonneg hN2 mu)
    huv (gridTime_le_horizon hN2 hbound)
  have ⟨hh0, hhj⟩ := Witness.H_bounds Witness.oneColumnTilt hk hN2 cuts hN
    (show (2 : ℝ) ∈ Icc (2 : ℝ) 4 by norm_num) huv
  have hlen : gridTime N (mu+bl)-gridTime N mu ≤ 2*rho+1/logScale N := by
    have hb : (bl : ℝ) ≤ 2*rho*logScale N+1 := by
      rw [hbl]
      exact (Nat.ceil_lt_add_one (by positivity)).le
    dsimp [gridTime]
    rw [Nat.cast_add, ← sub_div, add_sub_cancel_left]
    apply (div_le_iff₀ hL).mpr
    calc
      (bl : ℝ) ≤ 2*rho*logScale N+1 := hb
      _ = (2*rho+1/logScale N)*logScale N := by field_simp
  have hjd := hjle.trans (mul_le_mul_of_nonneg_right hlen hlog)
  exact ⟨hj0, hjd, hh0, hhj.trans hjd⟩

theorem tail_grid_cost_sub {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (mu bl : ℕ) :
    J cuts hN 2 (gridTime N (mu+bl)) (horizon N K) =
      J cuts hN 2 (gridTime N mu) (horizon N K) -
      J cuts hN 2 (gridTime N mu) (gridTime N (mu+bl)) ∧
    H cuts hN 2 (gridTime N (mu+bl)) (horizon N K) =
      H cuts hN 2 (gridTime N mu) (horizon N K) -
      H cuts hN 2 (gridTime N mu) (gridTime N (mu+bl)) := by
  constructor
  · have h := empiricalIntegral_add N (fun j => tiltedCost (cuts.profile hN j) 2)
      (gridTime N mu) (gridTime N (mu+bl)) (horizon N K)
    unfold J
    linarith
  · have h := empiricalIntegral_add N (fun j => tiltedEntropy (cuts.profile hN j) 2)
      (gridTime N mu) (gridTime N (mu+bl)) (horizon N K)
    unfold H
    linarith

end RiffleLowerV2.Localization
