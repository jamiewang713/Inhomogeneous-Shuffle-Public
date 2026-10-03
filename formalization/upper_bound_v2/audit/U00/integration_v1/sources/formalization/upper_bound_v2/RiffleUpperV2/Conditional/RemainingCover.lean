import RiffleUpperV2.Conditional.PileFutureCylinders
import RiffleUpperV2.Conditional.BlockEdges
import RiffleUpperV2.Conditional.RefinedCylinders

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional
open Exploration Reservoir

theorem directionalGlobalEdge_word {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g : ℝ) (p : Fin k) (d : Direction) (e : Fin (pileSize cuts p-1))
    (ω : Sample cuts) (he : directionalEdge cuts D g p d e ω) :
    sortedWord ω (RiffleLowerV2.edgeLeft (directionalGlobalEdge cuts p d e))=
      revealWords cuts p d ω ⟨e.val,by omega⟩ := by
  cases d
  · rfl
  · have hpos : RiffleLowerV2.edgeLeft (directionalGlobalEdge cuts p .backward e)=
        pilePosition cuts p .backward ⟨e.val+1,by omega⟩ := by
      apply Fin.ext
      simp only [RiffleLowerV2.edgeLeft,directionalGlobalEdge,spatialPileEdge,reversePileEdge,
        pilePosition,spatialIndex]
      omega
    rw [hpos]
    exact he.1.symm

/-- Any covering family of the actual strict future words gives a cover of
the literal directional remainder, with the exposed run treated separately. -/
theorem remainingEdge_cover {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g : ℝ) (p : Fin k) (d : Direction) (ω v : Sample cuts)
    (j : Fin (pileSize cuts p)) (hv : historyFiber cuts p d (j.val+1) ω v)
    (B : Finset (Prefix k (L+1)))
    (hB : ∀w:Word k (L+1),w.get 0=p → strictFuture d (revealWords cuts p d ω j) w →
      ∃x∈B,inCylinder x w)
    (e : Fin (pileSize cuts p-1)) (he : remainingEdgeEvent cuts D g p d (j.val+1) e v) :
    e∈currentRunEdges cuts p d (j.val+1) (revealWords cuts p d ω j) v ∨
      ∃x∈B,((directionalGlobalEdge cuts p d e).val:ℤ)∈absoluteBlockGraph x v := by
  let r : Fin (pileSize cuts p) := ⟨e.val,by omega⟩
  have hi := he.1
  have hfuture := revealWords_future_or_current cuts p d ω v j hv r (by change j.val≤e.val; omega)
  rcases hfuture with hcurrent | hfuture
  · apply Or.inl
    simpa only [currentRunEdges,Finset.mem_filter,Finset.mem_univ,true_and,revealWords,r] using And.intro he.1 (And.intro he.2.1 hcurrent)
  · obtain ⟨x,hx,hxw⟩ := hB (revealWords cuts p d v r) (revealWords_first cuts p d v r) hfuture
    refine Or.inr ⟨x,hx,(absoluteBlockGraph_edge_iff cuts x v _ (directionalEdge_global cuts D g p d e v he.2)).mpr ?_⟩
    rwa [directionalGlobalEdge_word cuts D g p d e v he.2]

/-- Actual refined future family, retaining same-pile support and strictness. -/
theorem refinedPileFuture_cover {k L : ℕ} (p : Fin k) (d : Direction)
    (s : Word k (L+1)) (hs : s.get 0=p)
    (m : pileFutureCylinders p d s hs → ℕ)
    (hm : ∀x:pileFutureCylinders p d s hs,x.val.1.val+m x≤L+1) (w : Word k (L+1)) :
    (w.get 0=p ∧ strictFuture d s w) ↔
      ∃x∈refineFamily (pileFutureCylinders p d s hs) m hm,inCylinder x w :=
  (pileFutureCylinders_cover p d s hs w).trans (refineFamily_cover _ m hm w)

theorem refinedPileFuture_depth_pos {k L : ℕ} (p : Fin k) (d : Direction)
    (s : Word k (L+1)) (hs : s.get 0=p)
    (m : pileFutureCylinders p d s hs → ℕ)
    (hm : ∀x:pileFutureCylinders p d s hs,x.val.1.val+m x≤L+1)
    {y : Prefix k (L+1)} (hy : y∈refineFamily (pileFutureCylinders p d s hs) m hm) : 0<y.1.val := by
  obtain ⟨x,_,hxy⟩ := Finset.mem_biUnion.mp hy
  have he := (refineCylinder_extension x.val (hm x) hxy).1
  have hp := pileFutureCylinders_depth_pos p d s hs x.property
  omega

theorem refinedPileFuture_card {k L N : ℕ} {ρ T : ℝ} (hk : 1≤k) (hN : 1≤N)
    (hρ : 0≤ρ) (hL : ((L+1:ℕ):ℝ)≤T*Real.log (N:ℝ)) (p : Fin k) (d : Direction)
    (s : Word k (L+1)) (hs : s.get 0=p)
    (m : pileFutureCylinders p d s hs → ℕ)
    (hm : ∀x:pileFutureCylinders p d s hs,x.val.1.val+m x≤L+1)
    (hb : ∀x:pileFutureCylinders p d s hs,m x≤windowLength N ρ) :
    ((refineFamily (pileFutureCylinders p d s hs) m hm).card:ℝ)≤
      (2*(k:ℝ)^3*T)*Real.log (N:ℝ)*(N:ℝ)^(ρ*Real.log (k:ℝ)) := by
  apply refinementCount hk hN hρ hL
  exact (refineFamily_card hk _ m hm hb).trans
    (Nat.mul_le_mul_right _ (pileFutureCylinders_card p d s hs))

end RiffleUpperV2.Conditional
