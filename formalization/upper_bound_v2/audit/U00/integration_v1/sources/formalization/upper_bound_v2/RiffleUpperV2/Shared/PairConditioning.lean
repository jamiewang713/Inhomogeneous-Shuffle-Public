import RiffleUpperV2.Shared.Conditioning
import RiffleLowerV2.Thinning.PMFTools

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2
open RiffleLowerV2.Thinning

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] [Nonempty Ω] [Nonempty Γ]

theorem uniformProductExpect_mul (f : Ω → ℝ) (g : Γ → ℝ) :
    expect (PMF.uniformOfFintype (Ω × Γ)) (fun ω => f ω.1*g ω.2) =
      expect (PMF.uniformOfFintype Ω) f * expect (PMF.uniformOfFintype Γ) g := by
  change RiffleLowerV2.expect (PMF.uniformOfFintype (Ω × Γ)) _ =
    RiffleLowerV2.expect (PMF.uniformOfFintype Ω) f * RiffleLowerV2.expect (PMF.uniformOfFintype Γ) g
  rw [uniform_product_expect (fun ω : Ω × Γ => f ω.1*g ω.2)]
  simp_rw [expect_const_mul]
  simp only [RiffleLowerV2.expect,Finset.sum_mul,mul_assoc]

theorem uniformProductProbability (A : Ω → Prop) (B : Γ → Prop) :
    probability (PMF.uniformOfFintype (Ω × Γ)) (fun ω => A ω.1 ∧ B ω.2) =
      probability (PMF.uniformOfFintype Ω) A * probability (PMF.uniformOfFintype Γ) B := by
  have h := uniformProductExpect_mul (fun a => if A a then 1 else 0)
    (fun b => if B b then 1 else 0)
  change expect _ _ = expect _ _ * expect _ _
  rw [← h]
  congr 1
  funext ω
  by_cases ha : A ω.1 <;> by_cases hb : B ω.2 <;> simp [ha,hb]

/-- Separate conditioning events preserve the independent uniform product.
The identity also holds for null fibers, using the existing zero convention. -/
theorem uniformProductConditionalExpect (f : Ω → ℝ) (g : Γ → ℝ)
    (A : Ω → Prop) (B : Γ → Prop) :
    conditionalExpect (PMF.uniformOfFintype (Ω × Γ)) (fun ω => f ω.1*g ω.2)
        (fun ω => A ω.1 ∧ B ω.2) =
      conditionalExpect (PMF.uniformOfFintype Ω) f A *
        conditionalExpect (PMF.uniformOfFintype Γ) g B := by
  unfold conditionalExpect RiffleLowerV2.conditionalExpect
  change expect (PMF.uniformOfFintype (Ω × Γ))
      (fun ω => if A ω.1 ∧ B ω.2 then f ω.1*g ω.2 else 0) /
      probability (PMF.uniformOfFintype (Ω × Γ)) (fun ω => A ω.1 ∧ B ω.2) =
    expect (PMF.uniformOfFintype Ω) (fun a => if A a then f a else 0) /
      probability (PMF.uniformOfFintype Ω) A *
    (expect (PMF.uniformOfFintype Γ) (fun b => if B b then g b else 0) /
      probability (PMF.uniformOfFintype Γ) B)
  have h : (fun ω : Ω × Γ => if A ω.1 ∧ B ω.2 then f ω.1*g ω.2 else 0) =
      (fun ω => (if A ω.1 then f ω.1 else 0)*(if B ω.2 then g ω.2 else 0)) := by
    funext ω
    by_cases ha : A ω.1 <;> by_cases hb : B ω.2 <;> simp [ha,hb]
  rw [h,uniformProductExpect_mul (fun a => if A a then f a else 0)
    (fun b => if B b then g b else 0),uniformProductProbability A B]
  exact mul_div_mul_comm _ _ _ _

theorem uniformProductConditionalProbability (E A : Ω → Prop) (F B : Γ → Prop) :
    conditionalProbability (PMF.uniformOfFintype (Ω × Γ))
        (fun ω => E ω.1 ∧ F ω.2) (fun ω => A ω.1 ∧ B ω.2) =
      conditionalProbability (PMF.uniformOfFintype Ω) E A *
        conditionalProbability (PMF.uniformOfFintype Γ) F B := by
  unfold conditionalProbability RiffleLowerV2.conditionalProbability
  have h : (fun ω : Ω × Γ => (E ω.1 ∧ F ω.2) ∧ A ω.1 ∧ B ω.2) =
      (fun ω => (E ω.1 ∧ A ω.1) ∧ (F ω.2 ∧ B ω.2)) := by
    funext ω
    exact propext (by tauto)
  rw [h]
  rw [show RiffleLowerV2.probability (PMF.uniformOfFintype (Ω × Γ))
      (fun ω => (E ω.1 ∧ A ω.1) ∧ (F ω.2 ∧ B ω.2)) = _ from
    uniformProductProbability (fun a => E a ∧ A a) (fun b => F b ∧ B b)]
  rw [show RiffleLowerV2.probability (PMF.uniformOfFintype (Ω × Γ))
      (fun ω => A ω.1 ∧ B ω.2) = _ from uniformProductProbability A B]
  exact mul_div_mul_comm _ _ _ _

/-- A positive pair history has two positive individual histories. -/
theorem uniformProductProbability_pos_iff (A : Ω → Prop) (B : Γ → Prop) :
    0 < probability (PMF.uniformOfFintype (Ω × Γ)) (fun ω => A ω.1 ∧ B ω.2) ↔
      0 < probability (PMF.uniformOfFintype Ω) A ∧
      0 < probability (PMF.uniformOfFintype Γ) B := by
  rw [uniformProductProbability]
  constructor
  · intro h
    exact ⟨pos_of_mul_pos_left h (probability_nonneg _ _),
      pos_of_mul_pos_right h (probability_nonneg _ _)⟩
  · rintro ⟨ha,hb⟩
    exact mul_pos ha hb

end RiffleUpperV2
