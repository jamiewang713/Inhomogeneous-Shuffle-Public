import RiffleUpperV2.Shared.Infimum
import RiffleUpperV2.Contracts.V1.Empirical

noncomputable section
open RiffleUpperV2

-- Compare the exact filter used by gridSum with manuscript columns s<h<=u.
example {L : ℕ} (a s u : ℕ) (r : Fin L) (has : a ≤ s) (hsu : s ≤ u) :
    (s-a ≤ r.val ∧ r.val < u-a) ↔
      (s < absoluteColumn a r ∧ absoluteColumn a r ≤ u) := by
  unfold absoluteColumn
  omega

-- F's retained length K-a has terminal absolute index K.
example (a K : ℕ) (haK : a < K) : a + (K-a) = K := by omega

-- Empty intervals have exactly zero empirical cost; beta starts at log_N n.
example {k n L : ℕ} (N a : ℕ) (cuts : Cuts k n L) (hn : 0 < n) :
    empiricalBeta N a cuts hn a = Real.log (n : ℝ) / Real.log (N : ℝ) := by
  simp [empiricalBeta, empiricalA, RiffleLowerV2.gridSum]

-- The whole-deck empty horizon cannot satisfy a strictly negative margin.
example {k N : ℕ} (hN : 2 ≤ N) (cuts : Cuts k N 0) (hpos : 0 < N)
    {η : ℝ} (hη : 0 < η) : ¬ EmpiricalNegativeMargin N 0 cuts hpos η := by
  intro hm
  have hlog : Real.log (N : ℝ) ≠ 0 := (TimeProfile.logScale_pos hN).ne'
  have hb : empiricalBeta N 0 cuts hpos 0 = 1 := by
    simp [empiricalBeta, empiricalA, RiffleLowerV2.gridSum, hlog]
  have ht := hm.1
  simp only [Nat.add_zero] at ht
  rw [hb] at ht
  linarith

#print RiffleUpperV2.Contracts.V1.F
#print RiffleUpperV2.Contracts.V1.E
#print axioms RiffleUpperV2.physical_graph_representation
#print axioms RiffleUpperV2.empiricalInf_attained
