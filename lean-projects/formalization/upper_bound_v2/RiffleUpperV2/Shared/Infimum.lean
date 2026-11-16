import RiffleUpperV2.Shared.Empirical

noncomputable section
open Set
open scoped BigOperators
namespace RiffleUpperV2
open TimeProfile

theorem thetaDomain_nonempty : (Icc (3 : ℝ) 4).Nonempty := ⟨3, by norm_num⟩

/-- Zero probabilities cause no discontinuity on this strictly positive theta interval. -/
theorem psi_continuousOn_theta {k : ℕ} (p : Simplex k) :
    ContinuousOn (psi p) (Icc (3 : ℝ) 4) := by
  have hz : ContinuousOn (powerSum p) (Icc (3 : ℝ) 4) := by
    apply continuousOn_finsetSum
    intro l _
    exact continuousOn_const.rpow continuousOn_id
      (fun θ hθ => Or.inr (by have := hθ.1; linarith))
  exact (hz.log (fun θ hθ => (powerSum_pos p (by have := hθ.1; linarith)).ne')).neg

theorem empiricalB_continuousOn_theta {k n L : ℕ} (N a : ℕ)
    (cuts : Cuts k n L) (hn : 0 < n) (s u : ℕ) :
    ContinuousOn (fun θ => empiricalB N a cuts hn θ s u) (Icc (3 : ℝ) 4) := by
  unfold empiricalB RiffleLowerV2.gridSum
  apply ContinuousOn.div_const
  apply continuousOn_finsetSum
  intro j _
  exact psi_continuousOn_theta (cuts.profile hn j)

theorem empiricalExpression_continuousOn {k n L : ℕ} (N a : ℕ)
    (cuts : Cuts k n L) (hn : 0 < n) (s u : ℕ) :
    ContinuousOn (fun θ => empiricalExpression N a cuts hn θ s u) (Icc (3 : ℝ) 4) := by
  exact ((((continuousOn_id.add continuousOn_const).div_const 2).mul continuousOn_const).sub
    (empiricalB_continuousOn_theta N a cuts hn s u)).sub continuousOn_const

theorem empiricalExpression_bddBelow {k n L : ℕ} (N a : ℕ)
    (cuts : Cuts k n L) (hn : 0 < n) (s u : ℕ) :
    BddBelow ((fun θ => empiricalExpression N a cuts hn θ s u) '' Icc 3 4) :=
  (isCompact_Icc.image_of_continuousOn
    (empiricalExpression_continuousOn N a cuts hn s u)).bddBelow

theorem empiricalExpression_bddAbove {k n L : ℕ} (N a : ℕ)
    (cuts : Cuts k n L) (hn : 0 < n) (s u : ℕ) :
    BddAbove ((fun θ => empiricalExpression N a cuts hn θ s u) '' Icc 3 4) :=
  (isCompact_Icc.image_of_continuousOn
    (empiricalExpression_continuousOn N a cuts hn s u)).bddAbove

theorem empiricalInf_le {k n L : ℕ} (N a : ℕ) (cuts : Cuts k n L)
    (hn : 0 < n) (s u : ℕ) {θ : ℝ} (hθ : θ ∈ Icc (3 : ℝ) 4) :
    empiricalInf N a cuts hn s u ≤ empiricalExpression N a cuts hn θ s u :=
  csInf_le (empiricalExpression_bddBelow N a cuts hn s u) ⟨θ, hθ, rfl⟩

theorem empiricalInf_attained {k n L : ℕ} (N a : ℕ) (cuts : Cuts k n L)
    (hn : 0 < n) (s u : ℕ) :
    ∃ θ ∈ Icc (3 : ℝ) 4,
      empiricalExpression N a cuts hn θ s u = empiricalInf N a cuts hn s u := by
  obtain ⟨θ, hθ, hmin⟩ := isCompact_Icc.exists_isMinOn thetaDomain_nonempty
    (empiricalExpression_continuousOn N a cuts hn s u)
  refine ⟨θ, hθ, le_antisymm ?_ (empiricalInf_le N a cuts hn s u hθ)⟩
  apply le_csInf (thetaDomain_nonempty.image _)
  rintro _ ⟨x, hx, rfl⟩
  exact hmin hx

end RiffleUpperV2
