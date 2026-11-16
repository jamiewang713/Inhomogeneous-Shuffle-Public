import RiffleMain.Profile.Integrability

set_option autoImplicit false

noncomputable section
open Set
open scoped BigOperators
namespace RiffleMain.Profile
open TimeProfile RiffleLowerV2.ProfileTransfer

/-- If at most one coordinate is at least `g`, nearly all mass lies in one pile. -/
theorem pileMax_of_not_good {k : ℕ} (hk : 2 ≤ k) (p : Simplex k)
    {g : ℝ} (hg : 0 ≤ g) (hgk : g < 1/(k : ℝ))
    (hbad : ¬ GoodColumn p g) : 1-(k : ℝ)*g ≤ pileMax p := by
  classical
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, by omega⟩, by simp⟩
  have hsum : (∑ _ : Fin k, 1/(k : ℝ)) ≤ ∑ l, prob p l := by
    simp [sum_prob, hkpos.ne']
  obtain ⟨l, _, hl⟩ := Finset.exists_le_of_sum_le hne hsum
  have hlarge : g ≤ prob p l := hgk.le.trans hl
  have hsmall (m : Fin k) (hm : m ≠ l) : prob p m < g := by
    by_contra h
    exact hbad ⟨l, m, hm.symm, hlarge, le_of_not_gt h⟩
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun m _ =>
    show prob p m ≤ (if m = l then prob p l else 0) + g from by
      by_cases hm : m = l
      · subst m
        simpa using le_add_of_nonneg_right hg (a := prob p l)
      · simpa only [if_neg hm, zero_add] using (hsmall m hm).le)
  simp only [sum_prob, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hb
  have hp := prob_le_pileMax p l
  linarith

theorem maxCost_of_not_good {k : ℕ} (hk : 2 ≤ k) (p : Simplex k)
    {g : ℝ} (hg : 0 ≤ g) (hgk : g < 1/(k : ℝ))
    (hsmall : (k : ℝ)*g ≤ 1/4) (hbad : ¬ GoodColumn p g) :
    maxCost p ≤ 2*(k : ℝ)*g := by
  have hp := pileMax_of_not_good hk p hg hgk hbad
  have hp0 := pileMax_pos p
  have hhalf : 1/2 ≤ pileMax p := by linarith
  have hlog := Real.log_le_sub_one_of_pos (one_div_pos.mpr hp0)
  have hinv : 1/pileMax p-1 ≤ 2*(k : ℝ)*g := by
    apply (sub_le_iff_le_add).2
    apply (div_le_iff₀ hp0).2
    have hkg : 0 ≤ (k : ℝ)*g := mul_nonneg (Nat.cast_nonneg _) hg
    have hmul := mul_le_mul_of_nonneg_left hhalf
      (show 0 ≤ 2*(k : ℝ)*g by nlinarith)
    nlinarith
  exact hlog.trans hinv

def goodThreshold (k : ℕ) (a : ℝ) : ℝ := min (1/(4*(k : ℝ))) (a/(16*(k : ℝ)))

theorem goodThreshold_spec {k : ℕ} (hk : 2 ≤ k) {a : ℝ} (ha : 0 < a) :
    0 < goodThreshold k a ∧ goodThreshold k a < 1/(k : ℝ) ∧
    ∀ p : Simplex k, ¬ GoodColumn p (goodThreshold k a) → maxCost p ≤ a/4 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hg : 0 < goodThreshold k a := by unfold goodThreshold; positivity
  have hg1 : goodThreshold k a ≤ 1/(4*(k : ℝ)) := min_le_left _ _
  have hg2 : goodThreshold k a ≤ a/(16*(k : ℝ)) := min_le_right _ _
  have hkg1 : (k : ℝ)*goodThreshold k a ≤ 1/4 := by
    have hh := (le_div_iff₀ (show 0 < 4*(k : ℝ) by positivity)).mp hg1
    nlinarith
  have hkg2 : 2*(k : ℝ)*goodThreshold k a ≤ a/4 := by
    have hh := (le_div_iff₀ (show 0 < 16*(k : ℝ) by positivity)).mp hg2
    nlinarith
  have hgk : goodThreshold k a < 1/(k : ℝ) := by
    apply (lt_div_iff₀ hkpos).2
    nlinarith
  refine ⟨hg, hgk, ?_⟩
  intro p hp
  exact (maxCost_of_not_good hk p hg.le hgk hkg1 hp).trans hkg2

end RiffleMain.Profile
