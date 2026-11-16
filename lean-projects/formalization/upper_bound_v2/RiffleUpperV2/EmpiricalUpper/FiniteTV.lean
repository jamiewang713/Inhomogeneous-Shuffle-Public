import RiffleUpperV2.Shared.Model
import RiffleLowerV2.Model.FiniteLaws

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.EmpiricalUpper
open RiffleLowerV2.Model

/-- Finite total variation is convex when the same law mixes both families. -/
theorem tv_bind_le {α β : Type*} [Fintype α] [Fintype β]
    (P : PMF α) (Q R : α → PMF β) :
    tv (P.bind Q) (P.bind R) ≤ expect P (fun a => tv (Q a) (R a)) := by
  have happ (S : α → PMF β) (b : β) :
      ((P.bind S) b).toReal = ∑ a, (P a).toReal * (S a b).toReal := by
    simp only [PMF.bind_apply, tsum_fintype,
      ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top (P.apply_ne_top a)
        ((S a).apply_ne_top b)), ENNReal.toReal_mul]
  unfold tv expect RiffleLowerV2.tv RiffleLowerV2.expect
  simp only [happ, ← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ (∑ b, ∑ a, (P a).toReal * |(Q a b).toReal - (R a b).toReal|) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply Finset.sum_le_sum
      intro b _
      calc
        _ ≤ ∑ a, |(P a).toReal * ((Q a b).toReal - (R a b).toReal)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum, mul_div_assoc,
      Finset.sum_div]

/-- Translation by any permutation preserves distance to the uniform law. -/
theorem tv_map_equiv_uniform {α : Type*} [Fintype α] [Nonempty α]
    (P : PMF α) (e : α ≃ α) :
    tv (P.map e) (PMF.uniformOfFintype α) = tv P (PMF.uniformOfFintype α) := by
  unfold tv RiffleLowerV2.tv
  simp only [map_equiv_apply, PMF.uniformOfFintype_apply]
  congr 1
  exact e.symm.sum_comp (fun a => |(P a).toReal -
    ((Fintype.card α : ENNReal)⁻¹).toReal|)

/-- Independent composition with arbitrary random bijections contracts distance
to uniform. This does not require identical column distributions. -/
theorem randomEquivTVContraction {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty β] (P : PMF α) (Q : PMF β) (e : α → β ≃ β) :
    tv (P.bind fun a => Q.map (e a)) (PMF.uniformOfFintype β) ≤
      tv Q (PMF.uniformOfFintype β) := by
  have hu : (P.bind fun a => (PMF.uniformOfFintype β).map (e a)) =
      PMF.uniformOfFintype β := by simp only [map_uniform_equiv, PMF.bind_const]
  have hh := tv_bind_le P (fun a => Q.map (e a))
    (fun a => (PMF.uniformOfFintype β).map (e a))
  simp only [map_uniform_equiv, tv_map_equiv_uniform, expect_const] at hh
  simpa only [PMF.bind_const] using hh

end RiffleUpperV2.EmpiricalUpper
