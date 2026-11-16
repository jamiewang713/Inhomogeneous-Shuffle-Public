import RiffleUpperV2.Conditional.FinePartition
import RiffleUpperV2.Reservoir.ConditionalFutureCylinderLaw
import RiffleUpperV2.Shared.FirstMomentAPI

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional
open Exploration Reservoir

/-- Injective relabeling and restriction of observed edge positions cannot
increase the squared-marginal sum of a finite graph law. -/
theorem imageProbabilitySquares_le {Ω E F Z : Type*} [Fintype Ω] [Fintype E] [Fintype F]
    [DecidableEq Z] (P : PMF Ω) (G : Ω → Finset F)
    (a : E → Z) (b : F → Z) (ha : Function.Injective a) (hb : Function.Injective b) :
    (∑e,(probability P (fun ω => a e∈(G ω).image b))^2)≤
      ∑f,(probability P (fun ω => f∈G ω))^2 := by
  classical
  let q : Z → ℝ := fun z => (probability P (fun ω => z∈(G ω).image b))^2
  let A := Finset.univ.image a
  let B := Finset.univ.image b
  have hout (z : Z) (hz : z∉B) : q z=0 := by
    have hn (ω : Ω) : z∉(G ω).image b := by
      intro hmem
      obtain ⟨f,hf,hfz⟩ := Finset.mem_image.mp hmem
      exact hz (Finset.mem_image.mpr ⟨f,Finset.mem_univ _,hfz⟩)
    simp only [q,probability,RiffleLowerV2.probability,RiffleLowerV2.expect,hn,if_false,mul_zero,
      Finset.sum_const_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]
  have hq (f : F) : q (b f)=(probability P (fun ω => f∈G ω))^2 := by
    dsimp [q]
    congr 2
    funext ω
    apply propext
    constructor
    · intro hmem
      obtain ⟨a,ha,hab⟩ := Finset.mem_image.mp hmem
      simpa only [hb hab] using ha
    · intro hf
      exact Finset.mem_image.mpr ⟨f,hf,rfl⟩
  calc
    _ = ∑z∈A,q z := (Finset.sum_image (fun _ _ _ _ h => ha h)).symm
    _ ≤ ∑z∈A∪B,q z := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left)
      (fun _ _ _ => sq_nonneg _)
    _ = ∑z∈B,q z := (Finset.sum_subset Finset.subset_union_right (fun z _ hz => hout z hz)).symm
    _ = ∑f,q (b f) := Finset.sum_image (fun _ _ _ _ h => hb h)
    _ = _ := Finset.sum_congr rfl (fun f _ => hq f)

/-- The accepted actual future-cylinder law controls the fine-history
block square sum by the concrete induced-cut first moment. -/
theorem fineBlockSquares_le_firstMoment {k n L : ℕ} {I : Type*}
    (cuts : Cuts k n (L+1)) (p : Fin k) (d : Direction)
    (ω : Sample cuts) (j : Fin (pileSize cuts p)) (x : I → Prefix k (L+1))
    (hsep : ∀a b,a≠b → prefixSeparated (x a) (x b)) (a : I)
    (hfuture : ∀w,inCylinder (x a) w → strictFuture d (revealWords cuts p d ω j) w) :
    (∑e:Fin (pileSize cuts p-1),
      (conditionalProbability (fixedCountPMF cuts)
        (fun v => ((directionalGlobalEdge cuts p d e).val:ℤ)∈absoluteBlockGraph (x a) v)
        (fun v => futureFamilyView cuts p d (j.val+1) (revealWords cuts p d ω j) x v=
          futureFamilyView cuts p d (j.val+1) (revealWords cuts p d ω j) x ω))^2)≤
      expectedCommonEdges (inducedCuts cuts (cylinderRows (x a) ω) (x a) ω) := by
  have hf : ∀w:Word k (L+1),w.toList.take (x a).1.val=(x a).2.toList →
      strictlyFuture d (directionalWord cuts p d ω j) w := by
    intro w hw
    apply hfuture
    exact List.prefix_iff_eq_take.mpr (by simpa only [List.Vector.toList_length] using hw.symm)
  have he (e : Fin (pileSize cuts p-1)) := conditionalFutureCylinderLaw cuts p d ω j x hsep a hf
    (fun G => ((directionalGlobalEdge cuts p d e).val:ℤ)∈G)
  have hsum : (∑e:Fin (pileSize cuts p-1),
      (conditionalProbability (fixedCountPMF cuts)
        (fun v => ((directionalGlobalEdge cuts p d e).val:ℤ)∈absoluteBlockGraph (x a) v)
        (fun v => futureFamilyView cuts p d (j.val+1) (revealWords cuts p d ω j) x v=
          futureFamilyView cuts p d (j.val+1) (revealWords cuts p d ω j) x ω))^2) =
      ∑e:Fin (pileSize cuts p-1),
        (probability (fixedCountPMF (inducedCuts cuts (cylinderRows (x a) ω) (x a) ω))
          (fun σ => ((directionalGlobalEdge cuts p d e).val:ℤ)∈
            (shuffleEdges σ).image (fun t => (lowerRank (x a) ω:ℤ)+t.val)))^2 := by
    apply Finset.sum_congr rfl
    intro e _
    exact congrArg (fun z:ℝ => z^2) (he e)
  rw [hsum]
  have ha : Function.Injective (fun e:Fin (pileSize cuts p-1) => ((directionalGlobalEdge cuts p d e).val:ℤ)) := by
    intro e f h
    dsimp only at h
    apply directionalGlobalEdge_injective cuts p d
    exact Fin.ext (by exact_mod_cast h)
  have hb : Function.Injective (fun e:Fin ((cylinderRows (x a) ω).card-1) => (lowerRank (x a) ω:ℤ)+e.val) := by
    intro e f h
    apply Fin.ext
    exact_mod_cast add_left_cancel h
  apply (imageProbabilitySquares_le
    (fixedCountPMF (inducedCuts cuts (cylinderRows (x a) ω) (x a) ω)) shuffleEdges
    (fun e:Fin (pileSize cuts p-1) => ((directionalGlobalEdge cuts p d e).val:ℤ))
    (fun e => (lowerRank (x a) ω:ℤ)+e.val) ha hb).trans_eq
  rw [expectedCommonEdges_eq_sum_sq]
  apply Finset.sum_congr rfl
  intro e _
  simp only [probability,RiffleLowerV2.probability,RiffleLowerV2.expect,
    InhomogeneousShuffle.FirstMoment.FiniteGraphLaw.edgeMarginal,toFirstMomentLaw]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hh : e∈shuffleEdges σ <;> simp only [hh,if_true,if_false]

end RiffleUpperV2.Conditional
