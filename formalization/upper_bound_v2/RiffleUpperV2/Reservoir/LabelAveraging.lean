import RiffleUpperV2.Reservoir.ErasedLabels
import RiffleUpperV2.Shared.ExpectationAveraging

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open TimeProfile Exploration
attribute [local instance 2000] wordDecEq

theorem fixedCount_event_positive {k n d : ℕ} (cuts : Cuts k n d)
    (E : Sample cuts → Prop) (ω₀ : Sample cuts) (he : E ω₀) :
    0<probability (fixedCountPMF cuts) E := by
  unfold probability RiffleLowerV2.probability RiffleLowerV2.expect
  apply Finset.sum_pos'
  · intro ω _
    positivity
  · refine ⟨ω₀,Finset.mem_univ _,?_⟩
    simp only [he,if_true,mul_one]
    change 0<((PMF.uniformOfFintype (Sample cuts)) ω₀).toReal
    simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast]
    exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)

/-- Averaging every labeled cylinder set out of the auxiliary information
retains exactly the same fixed-count graph law under the natural forward history. -/
theorem unlabeledCylinderGraphExpect_forward {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1))
    (p : Fin k) (ω₀ : Sample cuts) (j : Fin (pileSize cuts p)) (x : I → Prefix k (L+1))
    (hsep : ∀ a b, a≠b → prefixSeparated (x a) (x b)) (a : I)
    (hfuture : ∀ w : Word k (L+1), w.toList.take (x a).1.val=(x a).2.toList → pileWords cuts p ω₀ j<w)
    (F : Finset ℤ → ℝ) :
    conditionalExpect (fixedCountPMF cuts) (fun ω => F (absoluteBlockGraph (x a) ω))
      (fun ω => unlabeledFamilyView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω=
        unlabeledFamilyView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x ω₀)=
      inducedGraphExpectation cuts (x a) ω₀ F := by
  let Z := futureFamilyView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x
  let U := unlabeledFamilyView cuts p .forward (j.val+1) (pileWords cuts p ω₀ j) x
  apply conditionalExpect_eq_of_fine_fibers (fixedCountPMF cuts) Z U
    (futureFamilyView_refines_unlabeled cuts p .forward _ _ x)
    (fun ω => F (absoluteBlockGraph (x a) ω)) (U ω₀) (inducedGraphExpectation cuts (x a) ω₀ F)
    (fixedCount_event_positive cuts _ ω₀ rfl)
  intro ω hU _
  have hhist : historyFiber cuts p .forward (j.val+1) ω₀ ω := congrArg Prod.fst hU
  have hs : pileWords cuts p ω j=pileWords cuts p ω₀ j :=
    revealed_word_eq cuts p .forward (j.val+1) hhist j (by omega)
  have hh := futureCylinderGraphExpect_forward cuts p ω j x hsep a
    (fun w hw => by rw [hs]; exact hfuture w hw) F
  rw [hs] at hh
  exact hh.trans (inducedGraphExpectation_record_eq cuts (x a) ω ω₀ (congrArg (fun z => z.2.1 a) hU) F)

/-- Averaging every labeled cylinder set out of the auxiliary information
retains exactly the same fixed-count graph law under the natural backward history. -/
theorem unlabeledCylinderGraphExpect_backward {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1))
    (p : Fin k) (ω₀ : Sample cuts) (j : Fin (pileSize cuts p)) (x : I → Prefix k (L+1))
    (hsep : ∀ a b, a≠b → prefixSeparated (x a) (x b)) (a : I)
    (hfuture : ∀ w : Word k (L+1), w.toList.take (x a).1.val=(x a).2.toList → w<backwardWords cuts p ω₀ j)
    (F : Finset ℤ → ℝ) :
    conditionalExpect (fixedCountPMF cuts) (fun ω => F (absoluteBlockGraph (x a) ω))
      (fun ω => unlabeledFamilyView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω=
        unlabeledFamilyView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x ω₀)=
      inducedGraphExpectation cuts (x a) ω₀ F := by
  let Z := futureFamilyView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x
  let U := unlabeledFamilyView cuts p .backward (j.val+1) (backwardWords cuts p ω₀ j) x
  apply conditionalExpect_eq_of_fine_fibers (fixedCountPMF cuts) Z U
    (futureFamilyView_refines_unlabeled cuts p .backward _ _ x)
    (fun ω => F (absoluteBlockGraph (x a) ω)) (U ω₀) (inducedGraphExpectation cuts (x a) ω₀ F)
    (fixedCount_event_positive cuts _ ω₀ rfl)
  intro ω hU _
  have hhist : historyFiber cuts p .backward (j.val+1) ω₀ ω := congrArg Prod.fst hU
  have hs : backwardWords cuts p ω j=backwardWords cuts p ω₀ j :=
    revealed_word_eq cuts p .backward (j.val+1) hhist j (by omega)
  have hh := futureCylinderGraphExpect_backward cuts p ω j x hsep a
    (fun w hw => by rw [hs]; exact hfuture w hw) F
  rw [hs] at hh
  exact hh.trans (inducedGraphExpectation_record_eq cuts (x a) ω ω₀ (congrArg (fun z => z.2.1 a) hU) F)

end RiffleUpperV2.Reservoir
