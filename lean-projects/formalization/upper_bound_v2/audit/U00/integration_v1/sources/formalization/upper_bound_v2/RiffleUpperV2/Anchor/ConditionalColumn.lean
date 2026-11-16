import RiffleUpperV2.Anchor.PartialColumn

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile RiffleLowerV2.Thinning RiffleLowerV2.Thinning.Compat

/-- Exposing a nonempty fiber of a uniform law gives its literal uniform law.
This PMF adapter uses the finite-sum argument of the immutable residual-law proof. -/
theorem uniform_conditional_expect_subtype {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (E : Ω → Prop) [Nonempty {ω // E ω}] (f : Ω → ℝ) :
    RiffleLowerV2.conditionalExpect (PMF.uniformOfFintype Ω) f E =
      expect (PMF.uniformOfFintype {ω // E ω}) (fun ω => f ω.val) := by
  have hs : (∑ ω, if E ω then f ω else 0) = ∑ ω : {ω // E ω}, f ω.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) f
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  change RiffleLowerV2.conditionalExpect (PMF.uniformOfFintype Ω) f E =
    RiffleLowerV2.expect (PMF.uniformOfFintype {ω // E ω}) (fun ω => f ω.val)
  rw [RiffleLowerV2.conditionalExpect, uniform_expect, uniform_probability, hs, uniform_expect]
  field_simp

/-- Every specified fiber here is realizable: it is represented by the valid
fixed-count assignment c₀. No law is assigned to an impossible history. -/
theorem partialColumnFiber_positive {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d)
    (A : Finset (Fin n)) (c₀ : ColumnAssignments cuts j) :
    0 < probability (columnPMF cuts j) (columnFiber A c₀) := by
  change 0 < RiffleLowerV2.probability (PMF.uniformOfFintype (ColumnAssignments cuts j)) _
  rw [uniform_probability]
  apply div_pos
  · exact_mod_cast (Fintype.card_pos_iff.mpr
      (⟨⟨c₀, fun _ _ => rfl⟩⟩ : Nonempty {c : ColumnAssignments cuts j // columnFiber A c₀ c}))
  · exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (ColumnAssignments cuts j))

/-- Exact hypergeometric law of any residual labeled row count, after partial
column exposure. The sampling convention marks B and draws the remaining
allowed positions; both size factors remain explicit. -/
theorem partialColumnConditionalExpect {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d)
    (A B : Finset (Fin n)) (D : Finset (Fin k)) (c₀ : ColumnAssignments cuts j)
    (hB : B ⊆ Finset.univ \ A) (f : ℕ → ℝ) :
    RiffleLowerV2.conditionalExpect (columnPMF cuts j)
      (fun c => f (B ∩ residualAllowed A D c).card) (columnFiber A c₀) =
    expect (samplingParams (Finset.univ \ A) B (residualMarked A D c₀) hB
      (residualMarked_le A D c₀)).law.toPMF (fun q => f q.val) := by
  letI : Nonempty {c : ColumnAssignments cuts j // columnFiber A c₀ c} :=
    ⟨⟨c₀, fun _ _ => rfl⟩⟩
  calc
    _ = expect (PMF.uniformOfFintype {c : ColumnAssignments cuts j // columnFiber A c₀ c})
        (fun c => f (B ∩ residualAllowed A D c.val).card) :=
      uniform_conditional_expect_subtype (columnFiber A c₀)
        (fun c => f (B ∩ residualAllowed A D c).card)
    _ = (sampleLaw (Finset.univ \ A) (residualMarked A D c₀)
          (residualMarked_le A D c₀)).expect (fun S => f (B ∩ S.val).card) :=
      partialColumnUniform cuts j A D c₀ (fun S => f (B ∩ S.val).card)
    _ = (samplingParams (Finset.univ \ A) B (residualMarked A D c₀) hB
          (residualMarked_le A D c₀)).law.expect (fun q => f q.val) :=
      sample_expect_intersection_eq_hypergeom _ _ _ _ hB f
    _ = _ := (Hypergeometric.finiteLaw_expect _ _).symm

/-- The exact law transfers every event, not only moments or point masses. -/
theorem partialColumnConditionalProbability {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d)
    (A B : Finset (Fin n)) (D : Finset (Fin k)) (c₀ : ColumnAssignments cuts j)
    (hB : B ⊆ Finset.univ \ A) (E : ℕ → Prop) :
    RiffleLowerV2.conditionalProbability (columnPMF cuts j)
      (fun c => E (B ∩ residualAllowed A D c).card) (columnFiber A c₀) =
    probability (samplingParams (Finset.univ \ A) B (residualMarked A D c₀) hB
      (residualMarked_le A D c₀)).law.toPMF (fun q => E q.val) := by
  have he := partialColumnConditionalExpect cuts j A B D c₀ hB
    (fun q => if E q then 1 else 0)
  simpa [RiffleLowerV2.conditionalExpect, RiffleLowerV2.conditionalProbability,
    RiffleLowerV2.probability, RiffleLowerV2.expect, mul_ite, and_comm, ite_and] using he

end RiffleUpperV2.Anchor
