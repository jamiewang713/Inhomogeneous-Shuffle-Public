import RiffleUpperV2.Localization.Eventual

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace RiffleUpperV2.Localization
open Anchor

/-- The smoothing failure in every large stopped block is uniformly negligible.
The threshold depends only on the fixed reserve and stopping parameters. -/
theorem largeDensityFailure_eventually (g δ : ℝ) (hg : 0<g) (hδ : 0<δ) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ (N k n d : ℕ), N0 ≤ N →
      ∀ (cuts : Cuts k n d) (hn : 0<n) (R : Finset (Fin n))
        (χ : ℝ) (y z v x : Prefix k d), GenuineBoundaryPair cuts R χ y z v →
        Stops N cuts R v δ x → 2*δ ≤ meanExponent N cuts R x →
        ∀ (slots : Finset ℤ), slots.card ≤ N →
      6*(slots.card : ℝ)*Real.exp (-RiffleLowerV2.chernoffConstant*g*sideScale cuts R v) ≤
        Real.exp (-(N : ℝ)^δ) := by
  have hc : 0 < RiffleLowerV2.chernoffConstant*g :=
    mul_pos RiffleLowerV2.Thinning.chernoffConstant_pos hg
  obtain ⟨M,hM,h⟩ := powerExp_eventually_le (by positivity : 0<2*δ)
    (by linarith : δ<2*δ) hc 2
  refine ⟨max M 6,by omega,?_⟩
  intro N k n d hN cuts hn R χ y z v x hpair hx hlarge slots hs
  have hNm : M≤N := (le_max_left _ _).trans hN
  have hN6 : (6:ℝ)≤N := by exact_mod_cast (show 6≤N by omega)
  have hNgt : 1<N := by omega
  have hF := large_stopped_fluctuation hx hlarge
  have hω : (N : ℝ)^(2*δ) ≤ sideScale cuts R v := by
    rw [sideScale_eq_rpow N hNgt cuts hn R hpair]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega)) (by linarith)
  have hpre : 6*(slots.card : ℝ) ≤ (N : ℝ)^2 := by
    have hs' : (slots.card : ℝ) ≤ N := by exact_mod_cast hs
    nlinarith
  have he : Real.exp (-RiffleLowerV2.chernoffConstant*g*sideScale cuts R v) ≤
      Real.exp (-(RiffleLowerV2.chernoffConstant*g)*(N : ℝ)^(2*δ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hω hc.le]
  calc
    _ ≤ (N : ℝ)^2*Real.exp (-(RiffleLowerV2.chernoffConstant*g)*(N : ℝ)^(2*δ)) :=
      mul_le_mul hpre he (Real.exp_pos _).le (sq_nonneg _)
    _ ≤ _ := by simpa only [Real.rpow_two] using h N hNm

end RiffleUpperV2.Localization
