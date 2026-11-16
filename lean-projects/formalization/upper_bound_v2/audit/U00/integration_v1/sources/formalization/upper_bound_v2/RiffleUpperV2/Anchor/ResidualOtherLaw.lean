import RiffleUpperV2.Anchor.UnequalLaw
import RiffleUpperV2.Shared.FiniteAveraging

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile Hypergeometric

/-- A random set selected entirely by all columns other than j. -/
def OtherDetermined {k n d : ℕ} {cuts : Cuts k n d} (j : Fin d)
    (A : Sample cuts → Finset (Fin n)) : Prop :=
  ∀ ω₀ ω, (∀ t : Fin d, t ≠ j → ω t = ω₀ t) → A ω = A ω₀

theorem otherFiber_eq_partialEmpty {k n d : ℕ} {cuts : Cuts k n d}
    (j : Fin d) (ω₀ : Sample cuts) :
    (fun ω => otherColumnHistory j ω = otherColumnHistory j ω₀) =
      partialRevealFiber j ∅ ω₀ := by
  funext ω
  apply propext
  rw [otherColumnHistory_eq_iff]
  simp only [partialRevealFiber, columnFiber, Finset.notMem_empty, false_implies, implies_true,
    and_true]

theorem residualAllowed_eq_inter {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (A : Finset (Fin n)) (D : Finset (Fin k)) (c : ColumnAssignments cuts j) :
    residualAllowed A D c = (Finset.univ \ A) ∩ residualAllowed ∅ D c := by
  apply Finset.ext
  intro r
  simp only [residualAllowed, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_inter,
    Finset.mem_univ, Finset.notMem_empty, not_false_eq_true, and_true, true_and]
  exact and_comm

def otherResidualParams {k n d : ℕ} {cuts : Cuts k n d} (j : Fin d)
    (A : Finset (Fin n)) (D : Finset (Fin k)) (ω₀ : Sample cuts) :=
  sourceSamplingParams ∅ (Finset.univ \ A) D (ω₀ j) (by simp)

theorem otherResidualParams_fields {k n d : ℕ} {cuts : Cuts k n d} (j : Fin d)
    (A : Finset (Fin n)) (D : Finset (Fin k)) (ω₀ : Sample cuts) :
    (otherResidualParams j A D ω₀).population = n ∧
    (otherResidualParams j A D ω₀).marked = allowedCount cuts j D ∧
    (otherResidualParams j A D ω₀).draws = n-A.card := by
  simp only [otherResidualParams, sourceSamplingParams_population, Finset.card_empty,
    Nat.sub_zero, sourceSamplingParams_marked, Finset.filter_empty,
    sourceSamplingParams_draws, Finset.card_sdiff_of_subset (Finset.subset_univ A),
    Finset.card_univ, Fintype.card_fin, and_self]

theorem otherResidualParams_mean {k n d : ℕ} {cuts : Cuts k n d} (j : Fin d)
    (A : Finset (Fin n)) (D : Finset (Fin k)) (ω₀ : Sample cuts) :
    (otherResidualParams j A D ω₀).mean =
      ((n : ℝ)-A.card)*((allowedCount cuts j D : ℝ)/n) := by
  have hp := otherResidualParams_fields j A D ω₀
  unfold RiffleLowerV2.Thinning.Compat.HypergeomParams.mean
  rw [hp.1, hp.2.1, hp.2.2,
    Nat.cast_sub (by simpa using Finset.card_le_univ A : A.card ≤ n)]
  ring

/-- The random exposed set is fixed on each conditioning atom. This law
therefore applies to adaptive A chosen from the other columns. -/
theorem otherResidualConditionalExpect {k n d : ℕ} (cuts : Cuts k n d)
    (j : Fin d) (A : Sample cuts → Finset (Fin n)) (hA : OtherDetermined j A)
    (D : Finset (Fin k)) (ω₀ : Sample cuts) (f : ℕ → ℝ) :
    conditionalExpect (fixedCountPMF cuts)
      (fun ω => f (residualAllowed (A ω) D (ω j)).card)
      (fun ω => otherColumnHistory j ω = otherColumnHistory j ω₀) =
    expect (otherResidualParams j (A ω₀) D ω₀).law.toPMF (fun q => f q.val) := by
  rw [otherFiber_eq_partialEmpty]
  trans conditionalExpect (fixedCountPMF cuts)
    (fun ω => f ((Finset.univ \ A ω₀) ∩ residualAllowed ∅ D (ω j)).card)
    (partialRevealFiber j ∅ ω₀)
  · apply conditionalExpect_congr_on
    intro ω hf
    rw [hA ω₀ ω hf.1, residualAllowed_eq_inter]
  · exact partialRevealSourceExpect cuts j ∅ (Finset.univ \ A ω₀) D ω₀ (by simp) f

theorem otherResidualConditionalProbability {k n d : ℕ} (cuts : Cuts k n d)
    (j : Fin d) (A : Sample cuts → Finset (Fin n)) (hA : OtherDetermined j A)
    (D : Finset (Fin k)) (ω₀ : Sample cuts) (E : ℕ → Prop) :
    conditionalProbability (fixedCountPMF cuts)
      (fun ω => E (residualAllowed (A ω) D (ω j)).card)
      (fun ω => otherColumnHistory j ω = otherColumnHistory j ω₀) =
    probability (otherResidualParams j (A ω₀) D ω₀).law.toPMF (fun q => E q.val) := by
  have he := otherResidualConditionalExpect cuts j A hA D ω₀ (fun q => if E q then 1 else 0)
  have hcp : conditionalProbability (fixedCountPMF cuts)
      (fun ω => E (residualAllowed (A ω) D (ω j)).card)
      (fun ω => otherColumnHistory j ω = otherColumnHistory j ω₀) =
      conditionalExpect (fixedCountPMF cuts)
        (fun ω => if E (residualAllowed (A ω) D (ω j)).card then 1 else 0)
        (fun ω => otherColumnHistory j ω = otherColumnHistory j ω₀) := by
    unfold conditionalProbability conditionalExpect RiffleLowerV2.conditionalProbability
      RiffleLowerV2.conditionalExpect RiffleLowerV2.probability RiffleLowerV2.expect
    congr 1
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hF : otherColumnHistory j ω = otherColumnHistory j ω₀ <;>
      by_cases hE : E (residualAllowed (A ω) D (ω j)).card <;> simp [hF, hE]
  exact hcp.trans he

end RiffleUpperV2.Anchor
