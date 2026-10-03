import RiffleUpperV2.Anchor.ConditionalColumn

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile RiffleLowerV2.Thinning RiffleLowerV2.Thinning.Compat

/-- Every other future column and exactly the values on A in column j are
exposed. A may be selected from the other columns before this fiber is fixed. -/
def partialRevealFiber {k n d : ℕ} {cuts : Cuts k n d} (j : Fin d)
    (A : Finset (Fin n)) (ω₀ : Sample cuts) (ω : Sample cuts) : Prop :=
  (∀ t : Fin d, t ≠ j → ω t = ω₀ t) ∧ columnFiber A (ω₀ j) (ω j)

/-- The remaining degrees of freedom are precisely valid completions of the
partially exposed column; all other columns are fixed, including continuations. -/
def partialRevealEquiv {k n d : ℕ} {cuts : Cuts k n d} (j : Fin d)
    (A : Finset (Fin n)) (ω₀ : Sample cuts) :
    {ω : Sample cuts // partialRevealFiber j A ω₀ ω} ≃
      {c : ColumnAssignments cuts j // columnFiber A (ω₀ j) c} where
  toFun ω := ⟨ω.val j, ω.property.2⟩
  invFun c := ⟨Function.update ω₀ j c.val, by
    constructor
    · intro t ht
      exact Function.update_of_ne ht _ _
    · exact Eq.mpr (congrArg (columnFiber A (ω₀ j))
        (Function.update_self j c.val ω₀)) c.property⟩
  left_inv ω := by
    apply Subtype.ext
    funext t
    by_cases ht : t = j
    · subst t
      exact Function.update_self _ _ _
    · exact (Function.update_of_ne ht (ω.val j) ω₀).trans (ω.property.1 t ht).symm
  right_inv c := by
    apply Subtype.ext
    exact Function.update_self _ _ _

/-- Exact fixed-count matrix conditional law after the full partial reveal. -/
theorem partialRevealConditionalExpect {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d)
    (A B : Finset (Fin n)) (D : Finset (Fin k)) (ω₀ : Sample cuts)
    (hB : B ⊆ Finset.univ \ A) (f : ℕ → ℝ) :
    RiffleLowerV2.conditionalExpect (fixedCountPMF cuts)
      (fun ω => f (B ∩ residualAllowed A D (ω j)).card) (partialRevealFiber j A ω₀) =
    expect (samplingParams (Finset.univ \ A) B (residualMarked A D (ω₀ j)) hB
      (residualMarked_le A D (ω₀ j))).law.toPMF (fun q => f q.val) := by
  letI : Nonempty {ω : Sample cuts // partialRevealFiber j A ω₀ ω} :=
    ⟨⟨ω₀, ⟨fun _ _ => rfl, fun _ _ => rfl⟩⟩⟩
  letI : Nonempty {c : ColumnAssignments cuts j // columnFiber A (ω₀ j) c} :=
    ⟨⟨ω₀ j, fun _ _ => rfl⟩⟩
  calc
    _ = expect (PMF.uniformOfFintype {ω : Sample cuts // partialRevealFiber j A ω₀ ω})
        (fun ω => f (B ∩ residualAllowed A D (ω.val j)).card) :=
      uniform_conditional_expect_subtype (partialRevealFiber j A ω₀)
        (fun ω => f (B ∩ residualAllowed A D (ω j)).card)
    _ = expect (PMF.uniformOfFintype {c : ColumnAssignments cuts j // columnFiber A (ω₀ j) c})
        (fun c => f (B ∩ residualAllowed A D c.val).card) :=
      uniform_expect_equiv (partialRevealEquiv j A ω₀)
        (fun c => f (B ∩ residualAllowed A D c.val).card)
    _ = RiffleLowerV2.conditionalExpect (columnPMF cuts j)
        (fun c => f (B ∩ residualAllowed A D c).card) (columnFiber A (ω₀ j)) :=
      (uniform_conditional_expect_subtype (columnFiber A (ω₀ j))
        (fun c => f (B ∩ residualAllowed A D c).card)).symm
    _ = _ := partialColumnConditionalExpect cuts j A B D (ω₀ j) hB f

/-- All count events share the same exact conditional law on this matrix fiber. -/
theorem partialRevealConditionalProbability {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d)
    (A B : Finset (Fin n)) (D : Finset (Fin k)) (ω₀ : Sample cuts)
    (hB : B ⊆ Finset.univ \ A) (E : ℕ → Prop) :
    RiffleLowerV2.conditionalProbability (fixedCountPMF cuts)
      (fun ω => E (B ∩ residualAllowed A D (ω j)).card) (partialRevealFiber j A ω₀) =
    probability (samplingParams (Finset.univ \ A) B (residualMarked A D (ω₀ j)) hB
      (residualMarked_le A D (ω₀ j))).law.toPMF (fun q => E q.val) := by
  have he := partialRevealConditionalExpect cuts j A B D ω₀ hB
    (fun q => if E q then 1 else 0)
  simpa [RiffleLowerV2.conditionalExpect, RiffleLowerV2.conditionalProbability,
    RiffleLowerV2.probability, RiffleLowerV2.expect, mul_ite, and_comm, ite_and] using he

end RiffleUpperV2.Anchor
