import RiffleUpperV2.EmpiricalUpper.Restart

noncomputable section
namespace RiffleUpperV2.EmpiricalUpper

/-- Source choices, made before rho, N, the horizon, and the cut array. -/
def upperEta (η0 : ℝ) : ℝ := min (η0/4) 1
def upperGood (k : ℕ) (g0 : ℝ) : ℝ := min g0 (1/(2*(k : ℝ)))
def upperDensity (γ0 : ℝ) : ℝ := min γ0 1
def upperAlpha (η δF : ℝ) : ℝ := min (3*(η/10)/4) (min (3*η/5) δF)

theorem upperEta_spec {η0 : ℝ} (hη0 : 0 < η0) :
    0 < upperEta η0 ∧ upperEta η0 ≤ 1 ∧ 4*upperEta η0 ≤ η0 := by
  unfold upperEta
  exact ⟨lt_min (by positivity) (by norm_num),min_le_right _ _,by linarith [min_le_left (η0/4) 1]⟩

theorem upperGood_spec {k : ℕ} (hk : 2 ≤ k) {g0 : ℝ} (hg0 : 0 < g0) :
    0 < upperGood k g0 ∧ upperGood k g0 ≤ g0 ∧ upperGood k g0 < 1/(k : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold upperGood
  refine ⟨lt_min hg0 (by positivity),min_le_left _ _,(min_le_right _ _).trans_lt ?_⟩
  exact one_div_lt_one_div_of_lt hkpos (by linarith)

theorem upperDensity_spec {γ0 : ℝ} (hγ0 : 0 < γ0) :
    0 < upperDensity γ0 ∧ upperDensity γ0 ≤ γ0 ∧ upperDensity γ0 ≤ 1 := by
  exact ⟨lt_min hγ0 (by norm_num),min_le_left _ _,min_le_right _ _⟩

theorem upperAlpha_pos {η δF : ℝ} (hη : 0 < η) (hδF : 0 < δF) :
    0 < upperAlpha η δF := by unfold upperAlpha; positivity

/-- The C mesh allowance and all three source budgets are imposed before rho. -/
theorem completionRho {k : ℕ} (hk : 2 ≤ k) {η a ρC : ℝ}
    (hη : 0 < η) (ha : 0 < a) (hρC : 0 < ρC) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧ ρ0 ≤ ρC ∧
      ρ0*Real.log (k : ℝ) ≤ min (η/7) (min (a/4) (1/4)) := by
  have hklog : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast hk)
  let budget : ℝ := min (η/7) (min (a/4) (1/4))
  have hb : 0 < budget := by dsimp [budget]; positivity
  refine ⟨min ρC (budget/Real.log (k : ℝ)),lt_min hρC (div_pos hb hklog),
    min_le_left _ _,?_⟩
  exact (le_div_iff₀ hklog).mp (min_le_right _ _)

/-- A fixed component cutoff with the manuscript's stronger eta*B>=2 budget. -/
theorem componentBoundExists {η : ℝ} (hη : 0 < η) :
    ∃ B : ℕ, 2 ≤ B ∧ 2 ≤ η*(B : ℝ) := by
  refine ⟨max 2 ⌈2/η⌉₊,le_max_left _ _,?_⟩
  have hceil : 2/η ≤ (⌈2/η⌉₊ : ℝ) := Nat.le_ceil _
  have hmax : (⌈2/η⌉₊ : ℝ) ≤ (max 2 ⌈2/η⌉₊ : ℕ) := by exact_mod_cast le_max_right 2 ⌈2/η⌉₊
  have hh := (div_le_iff₀ hη).mp (hceil.trans hmax)
  linarith

theorem positiveHorizon {k N K : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    (cuts : Cuts k N K) {η0 : ℝ} (hη0 : 0 < η0)
    (hmargin : EmpiricalNegativeMargin N 0 cuts (by omega) η0) : 0 < K := by
  have hh := terminal_horizon hk hN cuts hmargin
  have hz := TimeProfile.logScale_pos hN
  by_contra h
  have he : K = 0 := by omega
  rw [he, Nat.cast_zero, zero_mul] at hh
  nlinarith

end RiffleUpperV2.EmpiricalUpper
