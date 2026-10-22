import Contracts.v1.AdditionalFinite

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Ascent

/-- Successful shifts depend on the graph and deterministic geometry alone. -/
def successfulTranslates {N : ℕ} (H0 : Finset ℤ) (G : PathEdges N) (r : ℝ) :
    Finset (Fin (N+1)) :=
  Finset.univ.filter fun q => r ≤ ((G ∩ internalEdges (clipTranslate N H0 q.val)).card : ℝ)

/-- Total least-shift choice; zero is the fixed default when no shift is successful. -/
def chosenTranslate {N : ℕ} (H0 : Finset ℤ) (G : PathEdges N) (r : ℝ) : Fin (N+1) :=
  if h : (successfulTranslates H0 G r).Nonempty then
    (successfulTranslates H0 G r).min' h else 0

@[simp] theorem mem_successfulTranslates {N : ℕ} (H0 : Finset ℤ) (G : PathEdges N)
    (r : ℝ) (q : Fin (N+1)) :
    q ∈ successfulTranslates H0 G r ↔
      r ≤ ((G ∩ internalEdges (clipTranslate N H0 q.val)).card : ℝ) := by
  simp [successfulTranslates]

theorem chosenTranslate_spec {N : ℕ} (H0 : Finset ℤ) (G : PathEdges N) (r : ℝ)
    (h : ∃ q : Fin (N+1), r ≤ ((G ∩ internalEdges (clipTranslate N H0 q.val)).card : ℝ)) :
    r ≤ ((G ∩ internalEdges (clipTranslate N H0 (chosenTranslate H0 G r).val)).card : ℝ) ∧
      ∀ q' : Fin (N+1), q' < chosenTranslate H0 G r →
        ((G ∩ internalEdges (clipTranslate N H0 q'.val)).card : ℝ) < r := by
  have hs : (successfulTranslates H0 G r).Nonempty := by
    obtain ⟨q,hq⟩ := h
    exact ⟨q, (mem_successfulTranslates H0 G r q).mpr hq⟩
  unfold chosenTranslate
  rw [dif_pos hs]
  constructor
  · exact (mem_successfulTranslates H0 G r _).mp (Finset.min'_mem _ hs)
  · intro q hq
    apply lt_of_not_ge
    intro hgood
    have hmin := Finset.min'_le (successfulTranslates H0 G r) q
      ((mem_successfulTranslates H0 G r q).mpr hgood)
    exact (not_lt_of_ge hmin) hq

/-- Frozen minimum-existence export, witnessed by the fixed graph-only choice. -/
theorem leastSuccessfulTranslate : Targets.LeastSuccessfulTranslate := by
  intro N H0 G r h
  exact ⟨chosenTranslate H0 G r, chosenTranslate_spec H0 G r h⟩

/-- Every such finite graph-only choice is measurable for the discrete graph space. -/
theorem chosenTranslate_measurable {N : ℕ} (H0 : Finset ℤ) (r : ℝ)
    [MeasurableSpace (PathEdges N)] [MeasurableSingletonClass (PathEdges N)]
    [MeasurableSpace (Fin (N+1))] : Measurable (fun G : PathEdges N => chosenTranslate H0 G r) :=
  measurable_of_finite _

end RiffleLowerV2.Ascent
