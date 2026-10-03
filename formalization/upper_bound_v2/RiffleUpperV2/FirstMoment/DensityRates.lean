import RiffleUpperV2.FirstMoment.DensityPowers
import RiffleUpperV2.Localization.FailureRate

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization

/-- Uniform square-root prefactors cost an arbitrarily small fixed power. -/
theorem smoothingPrefactor_eventually (T chi g epsilon : ℝ)
    (hT : 0 ≤ T) (hchi : 0 < chi) (hg : 0 < g) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N d : ℕ, N0 ≤ N → (d : ℝ) ≤ T*logScale N →
      ∀ k : ℕ, ∀ v : Prefix k d,
      4*Real.sqrt (varianceDenominator chi v/g) ≤ (N : ℝ)^epsilon := by
  let c := 4*((2+chi⁻¹)/g+1)
  obtain ⟨N0,hN0,h⟩ := Compat.fixed_polynomial_le_rpow c T 1 epsilon
    (by dsimp [c]; positivity) hT hepsilon
  refine ⟨N0,hN0,?_⟩
  intro N d hN hd k v
  have hv : (v.1.val : ℝ) ≤ d := by exact_mod_cast Nat.le_of_lt_succ v.1.isLt
  have hD : varianceDenominator chi v/g ≤ ((2+chi⁻¹)/g)*((d : ℝ)+1) := by
    apply (div_le_iff₀ hg).mpr
    dsimp [varianceDenominator]
    have hc : 0 ≤ chi⁻¹ := inv_nonneg.mpr hchi.le
    have hn : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
    have hh : ((2+chi⁻¹)/g)*((d : ℝ)+1)*g = (2+chi⁻¹)*((d : ℝ)+1) := by field_simp
    rw [hh]
    nlinarith
  have hpos : 0 ≤ varianceDenominator chi v/g := by unfold varianceDenominator; positivity
  have hs := Real.sq_sqrt hpos
  have hroot : Real.sqrt (varianceDenominator chi v/g) ≤ varianceDenominator chi v/g+1 := by
    nlinarith [sq_nonneg (Real.sqrt (varianceDenominator chi v/g)-1)]
  have hpre : 4*Real.sqrt (varianceDenominator chi v/g) ≤ c*((d : ℝ)+1) := by
    dsimp [c]
    nlinarith [(Nat.cast_nonneg d : (0 : ℝ)≤d)]
  exact hpre.trans (by simpa using h N d hN hd)

/-- A fixed stretched exponential is below every inverse power uniformly in N. -/
theorem stretchedExp_le_power_eventually (a M : ℝ) (ha : 0 < a) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      Real.exp (-(N : ℝ)^a) ≤ (N : ℝ)^(-M) := by
  obtain ⟨N0,hN0,h⟩ := powerExp_eventually_le ha (by linarith : (0 : ℝ)<a)
    (by norm_num : (0 : ℝ)<1) M
  refine ⟨N0,hN0,?_⟩
  intro N hN
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hh := h N hN
  norm_num only [Real.rpow_zero,neg_one_mul] at hh
  have hh' : (N : ℝ)^M*Real.exp (-(N : ℝ)^a) ≤ 1 :=
    hh.trans (Real.exp_le_one_iff.mpr (by norm_num))
  rw [Real.rpow_neg hNp.le,← one_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hNp M)).mpr
  simpa [mul_comm] using hh'

/-- The whole possible prefix count can multiply the large-block failure term. -/
theorem classFailure_eventually (k : ℕ) (hk : 1 ≤ k) (T g delta M : ℝ)
    (hT : 0 ≤ T) (hg : 0 < g) (hdelta : 0 < delta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N n d : ℕ, N0 ≤ N → (d : ℝ) ≤ T*logScale N →
      ∀ (cuts : Cuts k n d) (hn : 0<n) (R : Finset (Fin n)) (chi : ℝ)
        (y z v x : Prefix k d), GenuineBoundaryPair cuts R chi y z v →
        Stops N cuts R v delta x → 2*delta ≤ meanExponent N cuts R x →
      ∀ (slots : Finset ℤ), slots.card ≤ N → ∀ W : Finset (Prefix k d),
      (W.card : ℝ)*(6*(slots.card : ℝ)*Real.exp (-RiffleLowerV2.chernoffConstant*g*sideScale cuts R v)) ≤
        (N : ℝ)^(-M) := by
  obtain ⟨N1,hN1,hfailure⟩ := largeDensityFailure_eventually g delta hg hdelta
  obtain ⟨N2,hN2,hcount⟩ := countedWindowError_rate k hk T (16*delta) hT (by positivity)
  obtain ⟨N3,hN3,hpower⟩ := stretchedExp_le_power_eventually (delta/2) M (by positivity)
  refine ⟨max N1 (max N2 N3),hN1.trans (le_max_left _ _),?_⟩
  intro N n d hN hd cuts hn R chi y z v x hp hstop hlarge slots hslots W
  have h1 : N1≤N := (le_max_left _ _).trans hN
  have h2 : N2≤N := (le_max_left N2 N3).trans ((le_max_right _ _).trans hN)
  have h3 : N3≤N := (le_max_right N2 N3).trans ((le_max_right _ _).trans hN)
  have hcard : (W.card : ℝ) ≤ ((d : ℝ)+1)*(k : ℝ)^d := by
    exact_mod_cast (Finset.card_le_univ W).trans (prefix_card_bound k d (by omega))
  have hh := hcount N d h2 hd
  norm_num only [show 16*delta/16=delta by ring,show 16*delta/32=delta/2 by ring] at hh
  calc
    _ ≤ (((d : ℝ)+1)*(k : ℝ)^d)*Real.exp (-(N : ℝ)^delta) :=
      mul_le_mul hcard (hfailure N k n d h1 cuts hn R chi y z v x hp hstop hlarge slots hslots)
        (by positivity) (by positivity)
    _ ≤ _ := hh.trans (hpower N h3)

end RiffleUpperV2.FirstMoment
