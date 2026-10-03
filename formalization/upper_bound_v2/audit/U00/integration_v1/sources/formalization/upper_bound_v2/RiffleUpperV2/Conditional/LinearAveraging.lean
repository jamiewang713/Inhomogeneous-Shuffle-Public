import RiffleUpperV2.Conditional.ConditionalAveraging
import RiffleUpperV2.Reservoir.ConditionalFutureCylinderLaw

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional

theorem conditionalExpect_add {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (f g : Ω → ℝ) (H : Ω → Prop) :
    conditionalExpect P (fun ω => f ω+g ω) H=conditionalExpect P f H+conditionalExpect P g H := by
  simp only [conditionalExpect_atoms,mul_add,Finset.sum_add_distrib]

theorem conditionalExpect_mul_const {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (f : Ω → ℝ) (H : Ω → Prop) (c : ℝ) :
    conditionalExpect P (fun ω => c*f ω) H=c*conditionalExpect P f H := by
  simp only [conditionalExpect_atoms,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem conditionalExpect_sum {Ω I : Type*} [Fintype Ω] [Fintype I] (P : PMF Ω)
    (f : I → Ω → ℝ) (H : Ω → Prop) :
    conditionalExpect P (fun ω => ∑i,f i ω) H=∑i,conditionalExpect P (f i) H := by
  simp only [conditionalExpect_atoms,Finset.mul_sum]
  exact Finset.sum_comm

theorem conditionalExpect_congr_on {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (f g : Ω → ℝ) (H : Ω → Prop) (h : ∀ω,H ω → f ω=g ω) :
    conditionalExpect P f H=conditionalExpect P g H :=
  le_antisymm (Reservoir.conditionalExpect_mono_on P f g H (fun ω hω => (h ω hω).le))
    (Reservoir.conditionalExpect_mono_on P g f H (fun ω hω => (h ω hω).ge))

theorem conditionalExpect_bad_cost {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (H bad : Ω → Prop) (hH : 0<probability P H) (b c : ℝ) :
    conditionalExpect P (fun ω => b+c*(if bad ω then 1 else 0)) H=
      b+c*conditionalProbability P bad H := by
  rw [conditionalExpect_add,conditionalExpect_mul_const,Reservoir.conditionalExpect_const_pos P H hH]
  rw [← Reservoir.conditionalProbability_indicator]

end RiffleUpperV2.Conditional
