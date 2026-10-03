import RiffleUpperV2.Exploration.Clusters

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Exploration
open TimeProfile

/-- Closed macroscopic intervals contained in an integer window give the claimed
integer condition (in fact the proof needs no two-column loss). -/
theorem localGood_integerWindow {k N L : ℕ} (cuts : Cuts k N (L+1)) (hN : 2 ≤ N)
    (ρ γ g : ℝ)
    (hgood : LocalGood cuts (by omega) g γ ρ 0 (((L+1 : ℕ) : ℝ) / Real.log (N : ℝ))) :
    integerWindowGood N cuts (by omega) ρ γ g := by
  intro b hb
  let z := Real.log (N : ℝ)
  have hz : 0 < z := Real.log_pos (by exact_mod_cast hN)
  let a : ℝ := ((b : ℝ)+1)/z
  have ha : 0 ≤ a := by positivity
  have hx : ρ*z ≤ (⌈ρ*z⌉₊ : ℝ) := Nat.le_ceil _
  have hbr : (b : ℝ) + (windowLength N ρ : ℝ) ≤ ((L+1 : ℕ) : ℝ) := by exact_mod_cast hb
  have hm : (windowLength N ρ : ℝ) = (⌈ρ*z⌉₊ : ℝ)+1 := by
    simp [windowLength, z]
  have haρ : a+ρ ≤ ((L+1 : ℕ) : ℝ)/z := by
    apply (le_div_iff₀ hz).2
    have haeq : a*z = (b : ℝ)+1 := by dsimp [a]; exact div_mul_cancel₀ _ hz.ne'
    rw [add_mul, haeq]
    rw [hm] at hbr
    linarith
  have hsource := hgood a ha haρ
  have hsub : (Finset.univ.filter fun j : Fin (L+1) =>
      a ≤ columnTime N j ∧ columnTime N j ≤ a+ρ ∧ GoodColumn (cuts.profile (by omega) j) g) ⊆
      (Finset.univ.filter fun j : Fin (L+1) => b ≤ j.val ∧
        j.val < b+windowLength N ρ ∧ GoodColumn (cuts.profile (by omega) j) g) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    have hjlow : (b : ℝ)+1 ≤ (j.val : ℝ)+1 := by
      apply (div_le_div_iff_of_pos_right hz).mp
      exact hj.1
    have hjhigh : (j.val : ℝ)+1 ≤ (b : ℝ)+1+ρ*z := by
      have hh := (div_le_iff₀ hz).mp hj.2.1
      have haeq : a*z = (b : ℝ)+1 := by dsimp [a]; exact div_mul_cancel₀ _ hz.ne'
      simpa only [add_mul, haeq] using hh
    have hjnatlow : b ≤ j.val := by exact_mod_cast (by linarith : (b : ℝ) ≤ j.val)
    have hjrealhigh : (j.val : ℝ)+1 ≤ b+windowLength N ρ := by rw [hm]; linarith
    have hjnathigh : j.val+1 ≤ b+windowLength N ρ := by exact_mod_cast hjrealhigh
    exact ⟨hjnatlow, by omega, hj.2.2⟩
  have hc : ((Finset.univ.filter fun j : Fin (L+1) =>
      a ≤ columnTime N j ∧ columnTime N j ≤ a+ρ ∧ GoodColumn (cuts.profile (by omega) j) g).card : ℝ) ≤
      ((Finset.univ.filter fun j : Fin (L+1) => b ≤ j.val ∧
        j.val < b+windowLength N ρ ∧ GoodColumn (cuts.profile (by omega) j) g).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  dsimp [logScale] at hsource
  exact (by linarith : γ*ρ*Real.log (N : ℝ)-2 ≤ γ*ρ*Real.log (N : ℝ)).trans (hsource.trans hc)

end RiffleUpperV2.Exploration
