import RiffleUpperV2.Anchor.ConditionalColumn
import RiffleUpperV2.Shared.Conditioning

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2

/-- Equinumerous target fibers make the pushforward of a finite uniform law
uniform. The fiber equivalences are mathematical inputs, not an assumed law. -/
theorem uniformProjectionExpect {Ω Γ : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype Γ] [Nonempty Γ] (X : Ω → Γ)
    (e : ∀ z z' : Γ, {ω : Ω // X ω = z} ≃ {ω : Ω // X ω = z'})
    (f : Γ → ℝ) :
    expect (PMF.uniformOfFintype Ω) (fun ω => f (X ω)) =
      expect (PMF.uniformOfFintype Γ) f := by
  let ω₀ : Ω := Classical.choice inferInstance
  let F := {ω : Ω // X ω = X ω₀}
  letI : Nonempty F := ⟨⟨ω₀,rfl⟩⟩
  let t : Ω ≃ Γ × F := (Equiv.sigmaFiberEquiv X).symm.trans
    (Equiv.sigmaEquivProdOfEquiv (fun z => e z (X ω₀)))
  have hf (ω : Ω) : (t ω).1 = X ω := rfl
  calc
    _ = expect (PMF.uniformOfFintype (Γ × F)) (fun z => f z.1) := by
      simpa only [hf] using RiffleLowerV2.Model.uniform_expect_equiv t (fun z => f z.1)
    _ = _ := by
      change RiffleLowerV2.expect (PMF.uniformOfFintype (Γ × F)) (fun z => f z.1) =
        RiffleLowerV2.expect (PMF.uniformOfFintype Γ) f
      rw [RiffleLowerV2.Model.expect_uniform, RiffleLowerV2.Model.expect_uniform]
      simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, ← Finset.mul_sum, Fintype.card_prod, Nat.cast_mul]
      have hF : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp

/-- The same uniform projection as an equality of actual PMFs. -/
theorem uniformProjectionLaw {Ω Γ : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype Γ] [Nonempty Γ] (X : Ω → Γ)
    (e : ∀ z z' : Γ, {ω : Ω // X ω = z} ≃ {ω : Ω // X ω = z'}) :
    (PMF.uniformOfFintype Ω).map X = PMF.uniformOfFintype Γ := by
  ext z
  apply (ENNReal.toReal_eq_toReal_iff'
    (((PMF.uniformOfFintype Ω).map X).apply_ne_top z)
    ((PMF.uniformOfFintype Γ).apply_ne_top z)).mp
  rw [← RiffleLowerV2.Model.expect_singleton, RiffleLowerV2.Model.expect_map]
  exact (uniformProjectionExpect X e (fun y => if y=z then 1 else 0)).trans
    (RiffleLowerV2.Model.expect_singleton _ z)

/-- Conditional projection from a genuine nonempty event. The target may
be defined only on the conditioning fiber, as for induced-count matrices.
An observable on the original space need agree only on that fiber. -/
theorem conditionalUniformProjectionExpect {Ω Γ : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype Γ] [Nonempty Γ]
    (E : Ω → Prop) [Nonempty {ω : Ω // E ω}]
    (X : {ω : Ω // E ω} → Γ)
    (e : ∀ z z' : Γ,
      {ω : {v : Ω // E v} // X ω = z} ≃ {ω : {v : Ω // E v} // X ω = z'})
    (f : Ω → ℝ) (g : Γ → ℝ) (hf : ∀ (ω : Ω) (h : E ω), f ω = g (X ⟨ω,h⟩)) :
    conditionalExpect (PMF.uniformOfFintype Ω) f E =
      expect (PMF.uniformOfFintype Γ) g := by
  change RiffleLowerV2.conditionalExpect (PMF.uniformOfFintype Ω) f E = _
  rw [Anchor.uniform_conditional_expect_subtype]
  have he : (fun ω : {ω : Ω // E ω} => f ω.val) = fun ω => g (X ω) := by
    funext ω
    exact hf ω.val ω.property
  rw [he]
  exact uniformProjectionExpect X e g

end RiffleUpperV2
