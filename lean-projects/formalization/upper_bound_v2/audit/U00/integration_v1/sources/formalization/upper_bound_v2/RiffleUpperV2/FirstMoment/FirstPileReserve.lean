import RiffleUpperV2.FirstMoment.FirstColumn
import RiffleUpperV2.Shared.Empirical

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.FirstMoment
open TimeProfile Hypergeometric Anchor

/-- A good exposed column leaves at least g*n rows outside every pile. -/
theorem goodColumn_pile_bound {k n d : ℕ} (cuts : Cuts k n (d+1)) (hn : 0 < n)
    {g : ℝ} (hgood : GoodColumn (cuts.profile hn 0) g) (p : Fin k) :
    (cuts.count 0 p : ℝ) ≤ (1-g)*n := by
  classical
  obtain ⟨a,b,hab,ha,hb⟩ := hgood
  have he : ∃ q : Fin k, q ≠ p ∧ g ≤ (cuts.count 0 q : ℝ)/n := by
    by_cases h : a=p
    · exact ⟨b,by intro hh; exact hab (h.trans hh.symm),hb⟩
    · exact ⟨a,h,ha⟩
  obtain ⟨q,hq,hqg⟩ := he
  have hsum : cuts.count 0 p+cuts.count 0 q ≤ n := by
    have h := Finset.sum_le_univ_sum_of_nonneg (s := {p,q})
      (f := cuts.count 0) (fun _ => Nat.zero_le _)
    simpa [Finset.sum_pair (Ne.symm hq),cuts.sum_count] using h
  have hsumR : (cuts.count 0 p : ℝ)+(cuts.count 0 q : ℝ) ≤ n := by exact_mod_cast hsum
  have hcount := (le_div_iff₀ (by exact_mod_cast hn : (0 : ℝ)<n)).mp hqg
  nlinarith

/-- The smoothing reserve is a consequence of the actual first-column good event. -/
theorem firstPileReserve {k n d : ℕ} (cuts : Cuts k n (d+1)) (hn : 0 < n)
    {g : ℝ} (hg : 0 < g) (hg1 : g < 1)
    (hgood : FirstColumnGood cuts hn g) (c : ColumnAssignments cuts 0) (p : Fin k) :
    Reserve (anchorRows c p) g := by
  obtain ⟨_,hgood⟩ := hgood
  refine ⟨hg,hg1,?_⟩
  rw [anchorRows_card]
  exact goodColumn_pile_bound cuts hn hgood p

/-- Two positive-probability piles force at least two actual rows. -/
theorem firstColumnGood_population {k n d : ℕ} (cuts : Cuts k n (d+1)) (hn : 0 < n)
    {g : ℝ} (hg : 0 < g) (hgood : FirstColumnGood cuts hn g) : 2 ≤ n := by
  classical
  obtain ⟨_,a,b,hab,ha,hb⟩ := hgood
  have ha' : 0 < cuts.count 0 a := by
    have hh : 0 < (cuts.count 0 a : ℝ)/n := hg.trans_le ha
    exact_mod_cast (div_pos_iff.mp hh).resolve_right (by intro h; exact (not_lt_of_ge (Nat.cast_nonneg n)) h.2) |>.1
  have hb' : 0 < cuts.count 0 b := by
    have hh : 0 < (cuts.count 0 b : ℝ)/n := hg.trans_le hb
    exact_mod_cast (div_pos_iff.mp hh).resolve_right (by intro h; exact (not_lt_of_ge (Nat.cast_nonneg n)) h.2) |>.1
  have hsum : cuts.count 0 a+cuts.count 0 b ≤ n := by
    have h := Finset.sum_le_univ_sum_of_nonneg (s := {a,b})
      (f := cuts.count 0) (fun _ => Nat.zero_le _)
    simpa [Finset.sum_pair hab,cuts.sum_count] using h
  omega

end RiffleUpperV2.FirstMoment
