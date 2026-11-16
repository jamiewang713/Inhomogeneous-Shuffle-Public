import RiffleUpperV2.Conditional.PairReduction

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional
open Exploration

/-- Auxiliary records may contain unbounded natural counts and ranks. Only
their finite image under the original finite sample space is averaged. Every
conditioning fiber remains literally Z=v, without additional information. -/
theorem selfIntersectionJensen_image {Ω Γ Δ I : Type*}
    [Fintype Ω] [Fintype Δ] [Fintype I] (P : PMF Ω)
    (Z : Ω → Γ) (U : Ω → Δ) (g : Γ → Δ) (hU : ∀ ω, U ω = g (Z ω))
    (u : Δ) (hu : 0 < probability P (fun ω => U ω = u)) (E : I → Ω → Prop) :
    (∑ e, (conditionalProbability P (E e) (fun ω => U ω = u))^2) ≤
      ∑ z : ↥(Finset.univ.image Z),
        conditionalProbability P (fun ω => Z ω = z.val) (fun ω => U ω = u) *
          ∑ e, (conditionalProbability P (E e) (fun ω => Z ω = z.val))^2 := by
  let Z' : Ω → ↥(Finset.univ.image Z) := fun ω =>
    ⟨Z ω,Finset.mem_image.mpr ⟨ω,Finset.mem_univ _,rfl⟩⟩
  have h := selfIntersectionJensen P Z' U (fun z => g z.val) hU u hu E
  have hf (z : ↥(Finset.univ.image Z)) :
      (fun ω => Z' ω = z) = (fun ω => Z ω = z.val) := by
    funext ω
    exact propext Subtype.ext_iff
  simp_rw [hf] at h
  exact h

/-- Auxiliary information is attached solely for this Jensen calculation;
the original conditioning remains the one natural history. -/
theorem historySelfIntersection_auxiliary {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g : ℝ) (p : Fin k) (d : Direction) (i : ℕ) (ω : Sample cuts)
    (hpos : positiveHistory cuts p d i ω) {Z : Type*} (aux : Sample cuts → Z) :
    historySelfIntersection cuts D g p d i ω ≤
      ∑ z : ↥(Finset.univ.image (fun v => (naturalHistory cuts p d i v,aux v))),
        conditionalProbability (fixedCountPMF cuts)
          (fun v => (naturalHistory cuts p d i v,aux v) = z.val) (historyFiber cuts p d i ω) *
            ∑ e, (conditionalProbability (fixedCountPMF cuts)
              (remainingEdgeEvent cuts D g p d i e)
              (fun v => (naturalHistory cuts p d i v,aux v) = z.val))^2 := by
  exact selfIntersectionJensen_image (fixedCountPMF cuts)
    (fun v => (naturalHistory cuts p d i v,aux v))
    (naturalHistory cuts p d i) Prod.fst (fun _ => rfl)
    (naturalHistory cuts p d i ω) hpos (remainingEdgeEvent cuts D g p d i)

end RiffleUpperV2.Conditional
