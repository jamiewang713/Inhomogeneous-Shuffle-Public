import RiffleUpperV2.Exploration.UniformConcentration
import RiffleUpperV2.Exploration.SmallPiles
import RiffleUpperV2.Margins.Empirical

noncomputable section
namespace RiffleUpperV2.Exploration

/-- The actual regularity event, with both probabilistic inputs discharged from
full-column concentration and the empirical terminal margin. Constants precede arrays. -/
theorem regularityFailure (k : ℕ) (hk : 1 ≤ k) (D : ℕ) (T g ξ η : ℝ)
    (hT : 0 < T) (hg : 0 < g) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∃ N0 : ℕ, ∃ hN0 : 2 ≤ N0,
      ∀ (n : ℕ) (hn : N0 ≤ n), ∀ L : ℕ, ((L+1 : ℕ) : ℝ) ≤ T*Real.log (n : ℝ) →
      ∀ cuts : Cuts k n (L+1), ∀ a : ℕ,
      empiricalBeta n a cuts (by omega) (a+(L+1)) ≤ -η →
      probability (fixedCountPMF cuts)
        (fun ω => ¬ regularityEvent cuts D g ξ (Real.sqrt (badBound n ξ A c)) ω) ≤
          badBound n ξ A c + 2*n*Real.sqrt (badBound n ξ A c) + (k : ℝ)/2*(n : ℝ)^(ξ-η) := by
  obtain ⟨A,c,hA,hc,N0,hN0,hH⟩ := uniformConcentration k hk D T g ξ hT hg hξ hξ1
  refine ⟨A,c,hA,hc,max N0 2,le_max_right _ _,?_⟩
  intro n hn L hL cuts a hmargin
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hr : 0 < badBound n ξ A c := by
    unfold badBound
    exact mul_pos (mul_pos hA (Real.rpow_pos_of_pos (by exact_mod_cast (show 0<n by omega)) _)) (Real.exp_pos _)
  exact regularityFailure_of_bounds cuts D g ξ (badBound n ξ A c) ((k : ℝ)/2*(n : ℝ)^(ξ-η)) hr
    (hH n ((le_max_left _ _).trans hn) L hL cuts)
    (smallPileFailure cuts hn2 ξ η (Margins.maximalMean_le_of_terminalMargin hn2 a cuts (by omega) hmargin))

end RiffleUpperV2.Exploration
