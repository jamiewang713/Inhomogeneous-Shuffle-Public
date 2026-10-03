import RiffleUpperV2.Conditional.TailPower

noncomputable section
namespace RiffleUpperV2.Conditional

/-- The prescribed exponent retained before selecting rho. -/
def decayBudget (η δF : ℝ) : ℝ := min (3*(η/10)/4) (min (3*η/5) δF)

theorem decayBudget_pos {η δF : ℝ} (hη : 0 < η) (hδ : 0 < δF) :
    0 < decayBudget η δF := by unfold decayBudget; positivity

theorem decayBudget_bounds (η δF : ℝ) :
    decayBudget η δF ≤ 3*(η/10)/4 ∧ decayBudget η δF ≤ 3*η/5 ∧ decayBudget η δF ≤ δF :=
  ⟨min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩

/-- Source tiny-mean alpha budget. -/
theorem tinyExponent_budget {ξ α : ℝ} (hξ : 0 < ξ)
    (hα : α ≤ ξ/(4*(1+ξ))) : -ξ+α*(1+ξ) ≤ -3*ξ/4 := by
  have h := (le_div_iff₀ (by positivity : 0 < 4*(1+ξ))).mp hα
  nlinarith

/-- The intermediate collision exponent has the asserted 3 eta / 5 decay. -/
theorem intermediateExponent_budget {η α : ℝ} (hη : 0 < η) (hα0 : 0 ≤ α)
    (hα : α ≤ η/(40*(1+η))) :
    -η+3*(η/10)+2*α*(1+η-2*(η/10)) ≤ -3*η/5 := by
  have h := (le_div_iff₀ (by positivity : 0 < 40*(1+η))).mp hα
  have ht := mul_nonneg hα0 hη.le
  nlinarith

theorem currentExponent_budget {η α : ℝ} (hη : 0 < η)
    (hα : α ≤ η/(40*(1+η))) : -η+α*(1+η) ≤ -3*η/5 := by
  have h := (le_div_iff₀ (by positivity : 0 < 40*(1+η))).mp hα
  nlinarith

/-- Any positive alpha target below one is realized by an actual rare-digit
threshold tau<g; the logarithmic alpha is exactly the chosen value. -/
theorem rareThreshold_exists {g b : ℝ} (hg : 0 < g) (hg1 : g < 1)
    (hb : 0 < b) (hb1 : b < 1) :
    ∃ τ : ℝ, 0 < τ ∧ τ < g ∧ Real.log (1/g)/Real.log (1/τ) = b := by
  let τ := g^(1/b)
  have hτ : 0 < τ := Real.rpow_pos_of_pos hg _
  have hτg : τ < g := Real.rpow_lt_self_of_lt_one hg hg1 ((lt_div_iff₀ hb).mpr (by simpa))
  refine ⟨τ,hτ,hτg,?_⟩
  have hlog : Real.log g ≠ 0 := (Real.log_neg hg hg1).ne
  dsimp [τ]
  rw [one_div,one_div,Real.log_inv,Real.log_inv,Real.log_rpow hg]
  field_simp

/-- Parameter choices follow eta and delta_F. The eventual model threshold
is selected only after these fixed rho and tau parameters. -/
theorem conditionalParameter_choices {k : ℕ} (hk : 2 ≤ k) {η δF g : ℝ}
    (hη : 0 < η) (hδ : 0 < δF) (hg : 0 < g) (hg1 : g < 1) :
    ∃ τ ρ0 : ℝ, 0 < τ ∧ τ < g ∧ 0 < ρ0 ∧
      Real.log (1/g)/Real.log (1/τ) ≤ (η/10)/(4*(1+η/10)) ∧
      Real.log (1/g)/Real.log (1/τ) ≤ η/(40*(1+η)) ∧
      Real.log (1/g)/Real.log (1/τ) < 1/2 ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 → ρ*Real.log (k : ℝ) ≤ decayBudget η δF/4 := by
  let b := min ((η/10)/(4*(1+η/10))) (min (η/(40*(1+η))) (1/4))
  have hb : 0 < b := by dsimp [b]; positivity
  have hb4 : b ≤ 1/4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨τ,hτ,hτg,he⟩ := rareThreshold_exists hg hg1 hb (by linarith)
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast hk)
  refine ⟨τ,decayBudget η δF/(4*Real.log (k : ℝ)),hτ,hτg,
    div_pos (decayBudget_pos hη hδ) (by positivity),?_,?_,?_,?_⟩
  · rw [he]; exact min_le_left _ _
  · rw [he]; exact (min_le_right _ _).trans (min_le_left _ _)
  · rw [he]; linarith
  · intro ρ hρ hbound
    have h := (le_div_iff₀ (by positivity : 0 < 4*Real.log (k : ℝ))).mp hbound
    nlinarith

end RiffleUpperV2.Conditional
