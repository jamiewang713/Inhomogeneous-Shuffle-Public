import RiffleLowerV2.Model.GraphSorting

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleLowerV2.Model
open TimeProfile

/-- Inversion and translation send a uniform row relabelling to uniform labels. -/
def relabelToLabels {N : ℕ} (s : Permutation N) : Permutation N ≃ Permutation N where
  toFun ρ := s.trans ρ.symm
  invFun π := π.symm.trans s
  left_inv ρ := by ext i; simp
  right_inv π := by ext i; simp

theorem expect_uniform_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    expect (PMF.uniformOfFintype α) (fun _ => c) = c := by
  rw [expect_uniform]
  simp [Fintype.card_ne_zero]

theorem expect_swap {α β : Type*} [Fintype α] [Fintype β]
    (P : PMF α) (Q : PMF β) (F : α → β → ℝ) :
    expect P (fun a => expect Q (F a)) =
      expect Q (fun b => expect P (fun a => F a b)) := by
  unfold expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Unconditional joint identity with an arbitrary test of the full-word multiset.
Taking a multiset indicator gives the conditional identity on every positive atom. -/
theorem matrix_multiset_expect {k N K : ℕ} (cuts : Cuts k N K)
    (F : (Fin N → Word k K) → Permutation N → ℝ) :
    expect (fixedCountPMF cuts) (fun ω => F (sortedWord ω) (stableSort ω)) =
      expect (fixedCountPMF cuts) (fun ω =>
        expect (uniformPermutation N) (fun π =>
          F (sortedWord ω) (componentSort (shuffleEdges ω) π))) := by
  have hrelabel (ρ : Permutation N) :
      expect (fixedCountPMF cuts)
          (fun ω => F (sortedWord ω) (stableSort (sampleRelabel cuts ρ ω))) =
        expect (fixedCountPMF cuts) (fun ω => F (sortedWord ω) (stableSort ω)) := by
    have h := congrArg (fun P : PMF (Sample cuts) =>
      expect P (fun ω => F (sortedWord ω) (stableSort ω))) (sampleRelabel_uniform cuts ρ)
    rw [expect_map] at h
    simpa only [sortedWord_relabel] using h
  calc
    _ = expect (uniformPermutation N) (fun _ : Permutation N =>
        expect (fixedCountPMF cuts) (fun ω => F (sortedWord ω) (stableSort ω))) :=
      (expect_uniform_const _).symm
    _ = expect (uniformPermutation N) (fun ρ => expect (fixedCountPMF cuts)
        (fun ω => F (sortedWord ω) (stableSort (sampleRelabel cuts ρ ω)))) := by
      simp_rw [hrelabel]
    _ = expect (fixedCountPMF cuts) (fun ω => expect (uniformPermutation N)
        (fun ρ => F (sortedWord ω) (stableSort (sampleRelabel cuts ρ ω)))) :=
      expect_swap _ _ _
    _ = _ := by
      congr 1
      funext ω
      simp_rw [stableSort_relabel]
      exact uniform_expect_equiv (relabelToLabels (stableSort ω))
        (fun π => F (sortedWord ω) (componentSort (shuffleEdges ω) π))

theorem matrix_expect_eq_graph_expect {k N K : ℕ} (cuts : Cuts k N K)
    (F : Permutation N → ℝ) :
    expect (matrixLaw cuts) F = expect (graphMixtureLaw cuts) F := by
  rw [matrixLaw, expect_map, graphMixtureLaw, expect_bind]
  simp_rw [expect_map]
  exact matrix_multiset_expect cuts (fun _ π => F π)

/-- Conditional graph law expressed without division, including impossible multiset atoms. -/
theorem matrix_multiset_event {k N K : ℕ} (cuts : Cuts k N K)
    (w : Fin N → Word k K) (A : Permutation N → Prop) :
    probability (fixedCountPMF cuts) (fun ω => sortedWord ω = w ∧ A (stableSort ω)) =
      expect (fixedCountPMF cuts) (fun ω => if sortedWord ω = w then
        probability (uniformPermutation N) (fun π => A (componentSort (shuffleEdges ω) π)) else 0) := by
  have h := matrix_multiset_expect cuts
    (fun words π => if words = w ∧ A π then 1 else 0)
  rw [show probability (fixedCountPMF cuts) (fun ω => sortedWord ω = w ∧ A (stableSort ω)) =
    expect (fixedCountPMF cuts) (fun ω => if sortedWord ω = w ∧ A (stableSort ω) then 1 else 0) from by
      unfold probability
      congr 1
      funext ω
      by_cases hA : sortedWord ω = w ∧ A (stableSort ω) <;> simp [hA]]
  rw [h]
  congr 1
  funext ω
  by_cases hw : sortedWord ω = w
  · simp only [hw, true_and, if_true, probability]
  · simp [hw, expect]

/-- Exact concrete matrix-law identity, with an independently sampled uniform permutation. -/
theorem graphRepresentation : Targets.GraphRepresentation := by
  intro k N K cuts
  ext π
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  have h := matrix_expect_eq_graph_expect cuts (fun σ => if σ = π then 1 else 0)
  simpa [expect] using h

/-- Event interface for downstream permutation tests. -/
theorem graphEventIdentity : Targets.GraphEventIdentity := by
  intro k N K cuts A
  rw [graphRepresentation cuts]
  unfold probability graphMixtureLaw
  rw [expect_bind]
  simp_rw [expect_map]

end RiffleLowerV2.Model
