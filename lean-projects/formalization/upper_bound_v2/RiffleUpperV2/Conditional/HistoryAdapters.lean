import RiffleUpperV2.Conditional.FineMoments

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional
open Exploration Reservoir

theorem currentWord_history {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (d : Direction) (j : Fin (pileSize cuts p)) (ω v : Sample cuts)
    (hv : historyFiber cuts p d (j.val+1) ω v) :
    revealWords cuts p d v j=revealWords cuts p d ω j :=
  revealed_word_eq cuts p d (j.val+1) hv j (Nat.lt_succ_self _)

theorem familyFiber_on_history {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (j : Fin (pileSize cuts p)) (x : I → Prefix k (L+1))
    (ω v : Sample cuts) (hv : historyFiber cuts p d (j.val+1) ω v) :
    familyFiber cuts p d j x v=(fun z =>
      futureFamilyView cuts p d (j.val+1) (revealWords cuts p d ω j) x z=
        futureFamilyView cuts p d (j.val+1) (revealWords cuts p d ω j) x v) := by
  unfold familyFiber
  rw [currentWord_history cuts p d j ω v hv]

theorem currentExcess_on_history {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (j : Fin (pileSize cuts p))
    (ω v : Sample cuts) (hv : historyFiber cuts p d (j.val+1) ω v) :
    currentExcess cuts p d j v=currentExcess cuts p d j ω := by
  funext z
  unfold currentExcess
  rw [currentWord_history cuts p d j ω v hv]
  congr 2
  apply congrArg Finset.card
  ext r
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hr : r.val<j.val+1
  · rw [show revealWords cuts p d v r=revealWords cuts p d ω r from
      revealed_word_eq cuts p d (j.val+1) hv r hr]
  · simp [hr]

theorem historySelfIntersection_zero_of_not_direction {k n L : ℕ}
    (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ) (p : Fin k) (d : Direction)
    (ω : Sample cuts) (j : Fin (pileSize cuts p))
    (hdir : ¬hasDirection cuts D g d (revealWords cuts p d ω j)) :
    historySelfIntersection cuts D g p d (j.val+1) ω=0 := by
  apply Finset.sum_eq_zero
  intro e _
  have hfalse : (fun v => remainingEdgeEvent cuts D g p d (j.val+1) e v ∧
      historyFiber cuts p d (j.val+1) ω v)=(fun _ => False) := by
    funext v
    apply propext
    constructor
    · rintro ⟨he,hv⟩
      exact hdir (current_hasDirection_of_remaining cuts D g p d ω v j hv e he.1 he.2)
    · exact False.elim
  unfold conditionalProbability RiffleLowerV2.conditionalProbability
  rw [hfalse]
  simp [probability,RiffleLowerV2.probability,RiffleLowerV2.expect]

end RiffleUpperV2.Conditional
