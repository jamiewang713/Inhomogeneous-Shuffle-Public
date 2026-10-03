import RiffleUpperV2.Conditional.PairReduction
import RiffleUpperV2.Exploration.CoverageCount
import RiffleUpperV2.Exploration.Histories

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional
open Exploration

def directionalGlobalEdge {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (d : Direction) (e : Fin (pileSize cuts p-1)) : Fin (n-1) :=
  spatialPileEdge cuts p (match d with | .forward => e | .backward => reversePileEdge e)

theorem directionalGlobalEdge_injective {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) : Function.Injective (directionalGlobalEdge cuts p d) := by
  have hsp : Function.Injective (spatialPileEdge cuts p) := by
    intro a b hab
    apply Fin.ext
    have h := congrArg Fin.val hab
    dsimp [spatialPileEdge] at h
    omega
  cases d
  · exact hsp
  · exact hsp.comp (Function.LeftInverse.injective (fun e => reversePileEdge_involutive e))

theorem directionalEdge_global {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ)
    (g : ℝ) (p : Fin k) (d : Direction) (e : Fin (pileSize cuts p-1)) (ω : Sample cuts)
    (he : directionalEdge cuts D g p d e ω) : directionalGlobalEdge cuts p d e ∈ shuffleEdges ω := by
  cases d with
  | forward =>
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      simp only [directionalGlobalEdge]
      rw [spatialPileEdge_left,spatialPileEdge_right]
      exact he.1⟩
  | backward =>
    have hh := (directionalEdge_backward_iff cuts D g p (reversePileEdge e) ω).mp
      (by simpa using he)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      simp only [directionalGlobalEdge]
      rw [spatialPileEdge_left,spatialPileEdge_right]
      exact hh.1⟩

/-- Every directional remainder injects into the actual full common-edge graph. -/
theorem remainingCount_le_common {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ : ℝ) (p : Fin k) (d : Direction) (i : ℕ) (ω ω' : Sample cuts) :
    remainingDirectionalCount cuts D g ξ p d i ω ω' ≤ (shuffleEdges ω ∩ shuffleEdges ω').card := by
  rw [remainingDirectionalCount_eq]
  split_ifs with h
  · apply Finset.card_le_card_of_injOn (f := directionalGlobalEdge cuts p d)
    · intro e he
      obtain ⟨_,h₁,h₂⟩ := (Finset.mem_filter.mp he).2
      exact Finset.mem_inter.mpr ⟨directionalEdge_global cuts D g p d e ω h₁,
        directionalEdge_global cuts D g p d e ω' h₂⟩
    · exact (directionalGlobalEdge_injective cuts p d).injOn
  · exact Nat.zero_le _

/-- Empty histories impose no conditioning, and their directional count is
controlled by the exact whole-deck first moment. -/
theorem remaining_initial_le_firstMoment {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ : ℝ) (p : Fin k) (d : Direction) (ω : Sample cuts × Sample cuts) :
    conditionalExpect (independentPairLaw cuts)
      (fun v => (remainingDirectionalCount cuts D g ξ p d 0 v.1 v.2 : ℝ))
      (fun v => pairHistory cuts p d 0 v = pairHistory cuts p d 0 ω) ≤ expectedCommonEdges cuts := by
  have hf : (fun v => pairHistory cuts p d 0 v = pairHistory cuts p d 0 ω) = (fun _ => True) := by
    funext v
    simp [pairHistory]
  rw [hf]
  have htrue : ∀ f : Sample cuts × Sample cuts → ℝ,
      conditionalExpect (independentPairLaw cuts) f (fun _ => True) = expect (independentPairLaw cuts) f := by
    intro f
    simp [conditionalExpect,RiffleLowerV2.conditionalExpect,RiffleLowerV2.probability,
      RiffleLowerV2.Model.expect_const]
  rw [htrue]
  apply (RiffleLowerV2.Thinning.expect_mono (independentPairLaw cuts)
    (g := fun v => ((shuffleEdges v.1 ∩ shuffleEdges v.2).card : ℝ)) (fun v => by
    exact_mod_cast remainingCount_le_common cuts D g ξ p d 0 v.1 v.2)).trans_eq
  exact independentPair_expect cuts (fun a b => ((shuffleEdges a ∩ shuffleEdges b).card : ℝ))

end RiffleUpperV2.Conditional
