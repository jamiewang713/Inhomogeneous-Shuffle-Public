import RiffleUpperV2.GraphOverlap.Collision
import RiffleUpperV2.GraphOverlap.Disjoint

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.GraphOverlap
open RiffleLowerV2

theorem boundedComponentTail_factorial {k N K B : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) (hB : 1 ≤ B) :
    probability (fixedCountPMF cuts) (fun ω => ¬ BoundedComponents (shuffleEdges ω) B) ≤
      N * (maximalMean cuts hN)^B / (B+1).factorial := by
  have h := largestComponentTail_factorial cuts hN (show 2 ≤ B+1 by omega)
  simp only [Nat.add_sub_cancel] at h
  convert h using 1
  congr 1
  funext ω
  exact propext (not_boundedComponents_shuffle ω)

/-- The component cutoff is selected before populations and cut arrays. -/
theorem exists_boundedComponentTail (η A : ℝ) (hη : 0 < η) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ (k N K : ℕ) (cuts : Cuts k N K) (hN : 2 ≤ N),
      maximalMean cuts (by omega) ≤ (N : ℝ)^(-η) →
      probability (fixedCountPMF cuts) (fun ω => ¬ BoundedComponents (shuffleEdges ω) B) ≤
        (N : ℝ)^(-A) / (B+1).factorial := by
  obtain ⟨B, hB⟩ := exists_nat_gt (max 2 ((A+1)/η))
  have hB2 : 2 ≤ B := by
    have hb : (2 : ℝ) < B := (le_max_left _ _).trans_lt hB
    exact_mod_cast hb.le
  have he : A+1 ≤ η*B := by
    have hb : (A+1)/η ≤ B := ((le_max_right _ _).trans_lt hB).le
    have hh := (div_le_iff₀ hη).mp hb
    simpa [mul_comm] using hh
  refine ⟨B, hB2, ?_⟩
  intro k N K cuts hN hμ
  exact boundedComponentTail cuts hN hB2 hμ he

end RiffleUpperV2.GraphOverlap
