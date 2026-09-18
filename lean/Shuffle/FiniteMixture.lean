import Shuffle.Conditioning

noncomputable section
open scoped BigOperators

namespace Shuffle.FiniteLaw

variable {Θ Ω : Type*} [Fintype Θ] [Fintype Ω]

/-- D2: an arbitrary finite mixture. The mixing coordinates need not be independent. -/
def mixture (p : FiniteLaw Θ) (q : Θ → FiniteLaw Ω) : FiniteLaw Ω where
  mass ω := ∑ θ, p.mass θ * (q θ).mass ω
  mass_nonneg ω := Finset.sum_nonneg fun θ _ =>
    mul_nonneg (p.mass_nonneg θ) ((q θ).mass_nonneg ω)
  mass_sum := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, mass_sum, mul_one]
    exact p.mass_sum

theorem mixture_prob (p : FiniteLaw Θ) (q : Θ → FiniteLaw Ω) (E : Ω → Prop) :
    (mixture p q).prob E = ∑ θ, p.mass θ * (q θ).prob E := by
  classical
  unfold prob mixture
  simp only
  calc
    _ = ∑ ω, ∑ θ, p.mass θ * (if E ω then (q θ).mass ω else 0) := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h : E ω <;> simp [h]
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

theorem mixture_expect (p : FiniteLaw Θ) (q : Θ → FiniteLaw Ω) (f : Ω → ℝ) :
    (mixture p q).expect f = ∑ θ, p.mass θ * (q θ).expect f := by
  unfold expect mixture
  simp only
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- D2/D6: keep the full latent parameter and the sampled outcome. -/
def joint (p : FiniteLaw Θ) (q : Θ → FiniteLaw Ω) : FiniteLaw (Θ × Ω) where
  mass x := p.mass x.1 * (q x.1).mass x.2
  mass_nonneg x := mul_nonneg (p.mass_nonneg x.1) ((q x.1).mass_nonneg x.2)
  mass_sum := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, mass_sum, mul_one]
    exact p.mass_sum

theorem joint_atom_rectangle (p : FiniteLaw Θ) (q : Θ → FiniteLaw Ω)
    (θ : Θ) (B : Ω → Prop) :
    (joint p q).prob (fun x => x.1 = θ ∧ B x.2) = p.mass θ * (q θ).prob B := by
  classical
  unfold prob joint
  simp only
  rw [Fintype.sum_prod_type]
  have hinner : ∀ a : Θ,
      (∑ b : Ω, if a = θ ∧ B b then p.mass a * (q a).mass b else 0) =
      if a = θ then p.mass a * (∑ b : Ω, if B b then (q a).mass b else 0) else 0 := by
    intro a
    by_cases h : a = θ
    · simp [h, Finset.mul_sum, mul_ite]
    · simp [h]
  simp_rw [hinner]
  simp

theorem joint_first_prob (p : FiniteLaw Θ) (q : Θ → FiniteLaw Ω) (θ : Θ) :
    (joint p q).prob (fun x => x.1 = θ) = p.mass θ := by
  simpa using joint_atom_rectangle p q θ (fun _ => True)

/-- Only positive parameter atoms define conditional laws. -/
theorem joint_conditional_second (p : FiniteLaw Θ) (q : Θ → FiniteLaw Ω)
    (θ : Θ) (hθ : 0 < p.mass θ) (B : Ω → Prop) :
    (joint p q).conditionalProb (fun x => x.1 = θ) (fun x => B x.2) =
      (q θ).prob B := by
  unfold conditionalProb
  have he : (fun x : Θ × Ω => B x.2 ∧ x.1 = θ) =
      (fun x : Θ × Ω => x.1 = θ ∧ B x.2) := by
    funext x
    exact propext and_comm
  rw [he, joint_atom_rectangle, joint_first_prob]
  exact mul_div_cancel_left₀ _ (ne_of_gt hθ)

theorem joint_condition_second_map (p : FiniteLaw Θ) (q : Θ → FiniteLaw Ω)
    (θ : Θ) (hθ : 0 < p.mass θ) :
    ((joint p q).condition (fun x => x.1 = θ) (by
      rw [joint_first_prob]
      exact hθ)).map Prod.snd = q θ := by
  classical
  apply ext_mass
  intro ω
  change ((joint p q).condition _ _).prob (fun x => x.2 = ω) = (q θ).mass ω
  rw [condition_prob, joint_conditional_second p q θ hθ (fun b => b = ω)]
  simp [prob]

theorem joint_second_map (p : FiniteLaw Θ) (q : Θ → FiniteLaw Ω) :
    (joint p q).map Prod.snd = mixture p q := by
  classical
  apply ext_mass
  intro ω
  change (joint p q).prob (fun x => x.2 = ω) = ∑ θ, p.mass θ * (q θ).mass ω
  simp [prob, joint, Fintype.sum_prod_type]

end Shuffle.FiniteLaw
