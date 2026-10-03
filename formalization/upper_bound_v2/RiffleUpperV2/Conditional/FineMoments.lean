import RiffleUpperV2.Conditional.GraphSquares
import RiffleUpperV2.Conditional.BlockCounts
import RiffleUpperV2.Conditional.ConditionalAveraging

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional
open Exploration Reservoir

def blockSquares {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k) (d : Direction)
    (x : Prefix k (L+1)) (H : Sample cuts → Prop) : ℝ :=
  ∑e:Fin (pileSize cuts p-1),(conditionalProbability (fixedCountPMF cuts)
    (fun v => ((directionalGlobalEdge cuts p d e).val:ℤ)∈absoluteBlockGraph x v) H)^2

def familyFiber {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1)) (p : Fin k)
    (d : Direction) (j : Fin (pileSize cuts p)) (x : I → Prefix k (L+1)) (ω : Sample cuts) :
    Sample cuts → Prop := fun v =>
  futureFamilyView cuts p d (j.val+1) (revealWords cuts p d ω j) x v=
    futureFamilyView cuts p d (j.val+1) (revealWords cuts p d ω j) x ω

def currentExcess {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k) (d : Direction)
    (j : Fin (pileSize cuts p)) (ω v : Sample cuts) : ℝ :=
  (wordCount v (revealWords cuts p d ω j)-
    @observedCount (Word k (L+1)) Reservoir.wordDecEq (pileSize cuts p) (revealWords cuts p d ω) (j.val+1) (revealWords cuts p d ω j):ℕ)

theorem blockSquares_le_graphCount {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (x : Prefix k (L+1)) (H : Sample cuts → Prop) :
    blockSquares cuts p d x H≤conditionalExpect (fixedCountPMF cuts)
      (fun ω => ((absoluteBlockGraph x ω).card:ℝ)) H := by
  apply (conditionalSquares_le_card (fixedCountPMF cuts) H
    (fun e:Fin (pileSize cuts p-1) => fun ω => ((directionalGlobalEdge cuts p d e).val:ℤ)∈absoluteBlockGraph x ω)).trans
  apply conditionalExpect_mono_on
  intro ω _
  apply Nat.cast_le.mpr
  apply Finset.card_le_card_of_injOn (f := fun e:Fin (pileSize cuts p-1) => ((directionalGlobalEdge cuts p d e).val:ℤ))
  · intro e he
    simpa only [Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and] using he
  · intro e _ f _ h
    dsimp only at h
    apply directionalGlobalEdge_injective cuts p d
    exact Fin.ext (by exact_mod_cast h)

theorem blockSquares_le_count {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (x : Prefix k (L+1)) (H : Sample cuts → Prop) :
    blockSquares cuts p d x H≤conditionalExpect (fixedCountPMF cuts)
      (fun ω => (RiffleUpperV2.prefixCount x ω:ℝ)) H := by
  apply (blockSquares_le_graphCount cuts p d x H).trans
  apply conditionalExpect_mono_on
  intro ω _
  exact_mod_cast absoluteBlockGraph_card_le_count cuts x ω

theorem blockSquares_le_collisions {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (x : Prefix k (L+1)) (H : Sample cuts → Prop) :
    blockSquares cuts p d x H≤conditionalExpect (fixedCountPMF cuts)
      (fun ω => ∑w:Word k (L+1),if w.toList.take x.1.val=x.2.toList then ((wordCount ω w).choose 2:ℝ) else 0) H := by
  apply (blockSquares_le_graphCount cuts p d x H).trans
  apply conditionalExpect_mono_on
  intro ω _
  apply (absoluteBlockGraph_card_le_collisions cuts x ω).trans_eq
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w.toList.take x.1.val=x.2.toList <;> simp only [hw,if_true,if_false]

theorem blockSquares_le_n {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (x : Prefix k (L+1)) (H : Sample cuts → Prop) :
    blockSquares cuts p d x H≤n := by
  have hh : blockSquares cuts p d x H≤∑_:Fin (pileSize cuts p-1),(1:ℝ) := by
    apply Finset.sum_le_sum
    intro e _
    have h0 := conditionalProbability_nonneg (fixedCountPMF cuts)
      (fun v => ((directionalGlobalEdge cuts p d e).val:ℤ)∈absoluteBlockGraph x v) H
    have h1 := conditionalProbability_le_one (fixedCountPMF cuts)
      (fun v => ((directionalGlobalEdge cuts p d e).val:ℤ)∈absoluteBlockGraph x v) H
    nlinarith
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hh
  exact hh.trans (by exact_mod_cast (show pileSize cuts p-1≤n from (Nat.sub_le _ _).trans ((Nat.le_add_left (pileSize cuts p) (pileOffset cuts p)).trans (pileOffset_add_size_le cuts p))))

/-- Exact fine-history geometric reduction. The exposed run is charged
linearly; the other blocks retain squared probabilities. -/
theorem fineSelfIntersection_le {k n L : ℕ} {I : Type*} [Fintype I]
    (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ) (p : Fin k) (d : Direction)
    (ω : Sample cuts) (j : Fin (pileSize cuts p)) (x : I → Prefix k (L+1))
    (hsep : ∀a b,a≠b → prefixSeparated (x a) (x b))
    (hfuture : ∀a w,inCylinder (x a) w → strictFuture d (revealWords cuts p d ω j) w)
    (hcover : ∀w:Word k (L+1),w.get 0=p → strictFuture d (revealWords cuts p d ω j) w → ∃a,inCylinder (x a) w) :
    (∑e,(conditionalProbability (fixedCountPMF cuts) (remainingEdgeEvent cuts D g p d (j.val+1) e)
      (familyFiber cuts p d j x ω))^2)≤
      conditionalExpect (fixedCountPMF cuts) (currentExcess cuts p d j ω) (familyFiber cuts p d j x ω)+
        ∑a,blockSquares cuts p d (x a) (familyFiber cuts p d j x ω) := by
  obtain ⟨assign,hassign⟩ := finePartition_exists cuts D g p d ω j x hsep hfuture hcover
  have hh := conditionalSquare_partition (fixedCountPMF cuts) (familyFiber cuts p d j x ω)
    (remainingEdgeEvent cuts D g p d (j.val+1))
    (fun e v => e∈currentRunEdges cuts p d (j.val+1) (revealWords cuts p d ω j) v)
    (fun a e v => ((directionalGlobalEdge cuts p d e).val:ℤ)∈absoluteBlockGraph (x a) v) assign hassign
  apply hh.trans
  apply add_le_add _ le_rfl
  apply conditionalExpect_mono_on
  intro v hv
  have hf : (Finset.univ.filter fun e => e∈currentRunEdges cuts p d (j.val+1) (revealWords cuts p d ω j) v)=
      currentRunEdges cuts p d (j.val+1) (revealWords cuts p d ω j) v := by ext e; simp
  rw [hf]
  unfold currentExcess
  exact_mod_cast currentRunEdges_card_le cuts p d (j.val+1) ω v (congrArg Prod.fst hv)
    (revealWords cuts p d ω j) (revealWords_first cuts p d ω j)

end RiffleUpperV2.Conditional
