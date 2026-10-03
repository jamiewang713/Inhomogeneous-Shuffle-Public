import RiffleUpperV2.Shared.FiniteLawAdapters

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2
open RiffleLowerV2.Thinning.Compat

/-- Erase auxiliary information when every positive fine fiber inside the
chosen coarse fiber has the same expectation. Null fibers contribute zero. -/
theorem conditionalExpect_eq_of_finite_fine_fibers {Ω Γ Δ : Type*}
    [Fintype Ω] [Fintype Γ] (P : PMF Ω)
    (Z : Ω → Γ) (U : Ω → Δ)
    (href : ∀ ω ω', Z ω = Z ω' → U ω = U ω')
    (f : Ω → ℝ) (u : Δ) (c : ℝ)
    (hu : 0 < probability P (fun ω => U ω = u))
    (hpoint : ∀ ω, U ω = u →
      0 < probability P (fun v => Z v = Z ω) →
      conditionalExpect P f (fun v => Z v = Z ω) = c) :
    conditionalExpect P f (fun ω => U ω = u) = c := by
  let p := toCompatFiniteLaw P
  let H : Ω → Prop := fun ω => U ω = u
  let F : Ω → ℝ := fun ω => if H ω then f ω else 0
  obtain ⟨g,hg⟩ := history_refinement_factors Z U u href
  have hu' : 0 < p.prob H := by simpa only [p,H,toCompatFiniteLaw_probability] using hu
  have hatom (z : Γ) : p.conditionalExpect (fun ω => Z ω=z) F =
      c * p.conditionalProb (fun ω => Z ω=z) H := by
    by_cases hz : 0 < p.prob (fun ω => Z ω=z)
    · by_cases hzu : g z=u
      · have hsub (ω : Ω) (hω : Z ω=z) : H ω := by
          dsimp [H]
          rw [hg ω,hω,hzu]
        have hmask : p.conditionalExpect (fun ω => Z ω=z) F =
            p.conditionalExpect (fun ω => Z ω=z) f := by
          unfold FiniteLaw.conditionalExpect
          congr 1
          apply Finset.sum_congr rfl
          intro ω _
          by_cases hω : Z ω=z
          · simp only [if_pos hω,F,if_pos (hsub ω hω)]
          · simp only [if_neg hω]
        obtain ⟨ω,hω⟩ := probability_pos_exists P (fun ω => Z ω=z)
          (by simpa only [p,toCompatFiniteLaw_probability] using hz)
        have hvalue : p.conditionalExpect (fun ω => Z ω=z) f = c := by
          have h := hpoint ω (hsub ω hω) (by
            simpa only [hω,p,toCompatFiniteLaw_probability] using hz)
          simpa only [hω,p,toCompatFiniteLaw_conditionalExpect] using h
        have he : (fun ω => H ω ∧ Z ω=z) = (fun ω => Z ω=z) := by
          funext ω
          exact propext ⟨And.right,fun h => ⟨hsub ω h,h⟩⟩
        rw [hmask,hvalue,FiniteLaw.conditionalProb,he,div_self (ne_of_gt hz),mul_one]
      · have hdis (ω : Ω) (hω : Z ω=z) : ¬ H ω := by
          intro h
          apply hzu
          simpa only [H,hg ω,hω] using h
        have he : (fun ω => H ω ∧ Z ω=z) = (fun _ => False) := by
          funext ω
          exact propext ⟨fun h => hdis ω h.2 h.1,False.elim⟩
        unfold FiniteLaw.conditionalExpect FiniteLaw.conditionalProb
        rw [he,p.prob_false,zero_div,mul_zero]
        have hsum : (∑ ω, if Z ω=z then p.mass ω * F ω else 0)=0 := by
          apply Finset.sum_eq_zero
          intro ω _
          by_cases hω : Z ω=z
          · simp only [if_pos hω,F,if_neg (hdis ω hω),mul_zero]
          · simp only [if_neg hω]
        rw [hsum,zero_div]
    · have hz0 : p.prob (fun ω => Z ω=z)=0 :=
        le_antisymm (le_of_not_gt hz) (p.prob_nonneg _)
      simp only [FiniteLaw.conditionalExpect,FiniteLaw.conditionalProb,hz0,div_zero,mul_zero]
  have htotal : p.expect F = c * p.prob H := by
    rw [p.total_expectation Z F,p.total_probability Z H]
    simp_rw [hatom]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  have he : p.conditionalExpect H f = p.expect F / p.prob H := by
    unfold FiniteLaw.conditionalExpect FiniteLaw.expect
    congr 1
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : H ω <;> simp only [F,h,if_true,if_false,mul_zero]
  have hfinal : p.conditionalExpect H f = c := by
    rw [he,htotal,mul_div_cancel_right₀ c (ne_of_gt hu')]
  simpa only [p,H,toCompatFiniteLaw_conditionalExpect] using hfinal

/-- The same averaging for arbitrary information codomains, using only the
finite image of the sampled fine information. Counts may be natural numbers. -/
theorem conditionalExpect_eq_of_fine_fibers {Ω Γ Δ : Type*}
    [Fintype Ω] (P : PMF Ω) (Z : Ω → Γ) (U : Ω → Δ)
    (href : ∀ ω ω', Z ω = Z ω' → U ω = U ω')
    (f : Ω → ℝ) (u : Δ) (c : ℝ)
    (hu : 0 < probability P (fun ω => U ω = u))
    (hpoint : ∀ ω, U ω = u →
      0 < probability P (fun v => Z v = Z ω) →
      conditionalExpect P f (fun v => Z v = Z ω) = c) :
    conditionalExpect P f (fun ω => U ω = u) = c := by
  classical
  let S := Finset.univ.image Z
  let Z' : Ω → S := fun ω => ⟨Z ω,Finset.mem_image.mpr ⟨ω,Finset.mem_univ _,rfl⟩⟩
  apply conditionalExpect_eq_of_finite_fine_fibers P Z' U
    (fun ω ω' h => href ω ω' (congrArg Subtype.val h)) f u c hu
  intro ω hω hz
  have he : (fun v => Z' v=Z' ω) = (fun v => Z v=Z ω) := by
    funext v
    exact propext Subtype.ext_iff
  rw [he] at hz ⊢
  exact hpoint ω hω hz

end RiffleUpperV2
