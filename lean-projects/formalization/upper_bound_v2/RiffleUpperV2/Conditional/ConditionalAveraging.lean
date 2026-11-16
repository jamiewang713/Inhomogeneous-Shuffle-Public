import RiffleUpperV2.Conditional.AuxiliaryJensen
import RiffleUpperV2.Reservoir.ExtraCopies

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional
open RiffleLowerV2.Thinning.Compat

theorem conditionalExpect_atoms {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (f : Ω → ℝ) (H : Ω → Prop) :
    conditionalExpect P f H=∑ω,conditionalProbability P (fun v => v=ω) H*f ω := by
  unfold conditionalExpect conditionalProbability RiffleLowerV2.conditionalExpect
    RiffleLowerV2.conditionalProbability RiffleLowerV2.probability RiffleLowerV2.expect
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  have hs : (∑v:Ω,(P v).toReal*(if v=ω ∧ H v then (1:ℝ) else 0))=
      (P ω).toReal*(if H ω then 1 else 0) := by
    rw [Finset.sum_eq_single ω]
    · simp
    · intro v _ hv
      simp [hv]
    · simp
  rw [hs]
  by_cases h : H ω <;> simp [h,div_mul_eq_mul_div]

theorem conditionalExpect_finite_tower {Ω Γ Δ : Type*}
    [Fintype Ω] [Fintype Γ] [Fintype Δ] (P : PMF Ω)
    (Z : Ω → Γ) (U : Ω → Δ) (g : Γ → Δ) (hU : ∀ω,U ω=g (Z ω))
    (u : Δ) (hu : 0<probability P (fun ω => U ω=u)) (f : Ω → ℝ) :
    conditionalExpect P f (fun ω => U ω=u)=
      ∑z,conditionalProbability P (fun ω => Z ω=z) (fun ω => U ω=u)*
        conditionalExpect P f (fun ω => Z ω=z) := by
  simp_rw [conditionalExpect_atoms]
  have ht (v : Ω) := (toCompatFiniteLaw P).coarse_total_probability Z U g hU u
    (show 0<(toCompatFiniteLaw P).prob (fun ω => U ω=u) by simpa only [toCompatFiniteLaw_probability] using hu)
    (fun ω => ω=v)
  simp only [toCompatFiniteLaw_conditionalProbability] at ht
  simp_rw [ht,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem conditionalExpect_finite_image {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (P : PMF Ω) (Z : Ω → Γ) (H : Ω → Prop) (hH : 0<probability P H) (f : Γ → ℝ) :
    conditionalExpect P (fun ω => f (Z ω)) H=
      ∑z,conditionalProbability P (fun ω => Z ω=z) H*f z := by
  let p := toCompatFiniteLaw P
  have hp : 0<p.prob H := by simpa only [p,toCompatFiniteLaw_probability] using hH
  have hm := (p.condition H hp).map_expect Z f
  rw [p.condition_expect H hp] at hm
  simp only [FiniteLaw.expect,FiniteLaw.map,p.condition_prob H _ hp,
    p,toCompatFiniteLaw_conditionalProbability,toCompatFiniteLaw_conditionalExpect] at hm
  exact hm.symm

theorem conditionalExpect_image {Ω Γ : Type*} [Fintype Ω]
    (P : PMF Ω) (Z : Ω → Γ) (H : Ω → Prop) (hH : 0<probability P H) (f : Γ → ℝ) :
    conditionalExpect P (fun ω => f (Z ω)) H=
      ∑z:↥(Finset.univ.image Z),conditionalProbability P (fun ω => Z ω=z.val) H*f z.val := by
  let Z' : Ω → ↥(Finset.univ.image Z) := fun ω => ⟨Z ω,Finset.mem_image.mpr ⟨ω,Finset.mem_univ _,rfl⟩⟩
  have hh := conditionalExpect_finite_image P Z' H hH (fun z => f z.val)
  have hf (z : ↥(Finset.univ.image Z)) : (fun ω => Z' ω=z)=(fun ω => Z ω=z.val) := by
    funext ω
    exact propext Subtype.ext_iff
  simp_rw [hf] at hh
  exact hh

/-- Square Jensen as an expectation under the original coarse history. -/
theorem selfIntersectionJensen_expect {Ω Γ Δ E : Type*}
    [Fintype Ω] [Fintype Δ] [Fintype E] (P : PMF Ω)
    (Z : Ω → Γ) (U : Ω → Δ) (g : Γ → Δ) (hU : ∀ω,U ω=g (Z ω))
    (u : Δ) (hu : 0<probability P (fun ω => U ω=u)) (event : E → Ω → Prop) :
    (∑e,(conditionalProbability P (event e) (fun ω => U ω=u))^2)≤
      conditionalExpect P (fun ω => ∑e,(conditionalProbability P (event e) (fun v => Z v=Z ω))^2)
        (fun ω => U ω=u) := by
  rw [conditionalExpect_image P Z _ hu (fun z => ∑e,(conditionalProbability P (event e) (fun v => Z v=z))^2)]
  exact selfIntersectionJensen_image P Z U g hU u hu event

/-- Erasing a finite-image refinement returns precisely the natural-history
expectation, including all null-fiber terms. -/
theorem conditionalExpect_tower {Ω Γ Δ : Type*} [Fintype Ω] [Fintype Δ]
    (P : PMF Ω) (Z : Ω → Γ) (U : Ω → Δ) (g : Γ → Δ) (hU : ∀ω,U ω=g (Z ω))
    (u : Δ) (hu : 0<probability P (fun ω => U ω=u)) (f : Ω → ℝ) :
    conditionalExpect P (fun ω => conditionalExpect P f (fun v => Z v=Z ω)) (fun ω => U ω=u)=
      conditionalExpect P f (fun ω => U ω=u) := by
  rw [conditionalExpect_image P Z _ hu (fun z => conditionalExpect P f (fun v => Z v=z))]
  let Z' : Ω → ↥(Finset.univ.image Z) := fun ω => ⟨Z ω,Finset.mem_image.mpr ⟨ω,Finset.mem_univ _,rfl⟩⟩
  have hh := conditionalExpect_finite_tower P Z' U (fun z => g z.val) hU u hu f
  have hf (z : ↥(Finset.univ.image Z)) : (fun ω => Z' ω=z)=(fun ω => Z ω=z.val) := by
    funext ω
    exact propext Subtype.ext_iff
  simp_rw [hf] at hh
  exact hh.symm

end RiffleUpperV2.Conditional
