import RiffleUpperV2.Conditional.RemainingCover
import RiffleUpperV2.Conditional.DisjointSquares
import RiffleUpperV2.Reservoir.FutureGraphLaw

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional
open Exploration Reservoir

def blockSlots {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k) (d : Direction)
    (x : Prefix k (L+1)) (ω : Sample cuts) : Finset (Fin (pileSize cuts p-1)) :=
  Finset.univ.filter fun e => lowerRank x ω≤(directionalGlobalEdge cuts p d e).val ∧
    (directionalGlobalEdge cuts p d e).val+1<upperRank x ω

theorem blockSlots_word {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k) (d : Direction)
    (x : Prefix k (L+1)) (ω : Sample cuts) (e : Fin (pileSize cuts p-1))
    (he : e∈blockSlots cuts p d x ω) :
    inCylinder x (sortedWord ω (RiffleLowerV2.edgeLeft (directionalGlobalEdge cuts p d e))) := by
  have hh := (Finset.mem_filter.mp he).2
  have hr : lowerRank x ω≤(RiffleLowerV2.edgeLeft (directionalGlobalEdge cuts p d e)).val ∧
      (RiffleLowerV2.edgeLeft (directionalGlobalEdge cuts p d e)).val<upperRank x ω := by
    dsimp [RiffleLowerV2.edgeLeft]
    omega
  have hp := ((RiffleLowerV2.Model.prefixRanks cuts ω x).1 _).mpr hr
  exact List.prefix_iff_eq_take.mpr (by simpa only [List.Vector.toList_length] using hp.symm)

theorem blockSlots_disjoint {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k) (d : Direction)
    (x y : Prefix k (L+1)) (ω : Sample cuts) (hsep : prefixSeparated x y) :
    Disjoint (blockSlots cuts p d x ω) (blockSlots cuts p d y ω) := by
  apply Finset.disjoint_left.mpr
  intro e hx hy
  rcases List.prefix_or_prefix_of_prefix (blockSlots_word cuts p d x ω e hx)
    (blockSlots_word cuts p d y ω e hy) with h | h
  · exact hsep.1 h
  · exact hsep.2 h

theorem blockSlots_view {k n L : ℕ} {I : Type*} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (i : ℕ) (s : Word k (L+1))
    (x : I → Prefix k (L+1)) (a : I) (ω v : Sample cuts)
    (hv : futureFamilyView cuts p d i s x v=futureFamilyView cuts p d i s x ω) :
    blockSlots cuts p d (x a) v=blockSlots cuts p d (x a) ω := by
  have hlo : lowerRank (x a) v=lowerRank (x a) ω := congrArg (fun z => (z.2.1 a).2.1) hv
  have hhi : upperRank (x a) v=upperRank (x a) ω := congrArg (fun z => (z.2.1 a).2.2.1) hv
  unfold blockSlots
  rw [hlo,hhi]

theorem absoluteBlockGraph_in_slots {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (x : Prefix k (L+1)) (ω : Sample cuts)
    (e : Fin (pileSize cuts p-1))
    (he : ((directionalGlobalEdge cuts p d e).val:ℤ)∈absoluteBlockGraph x ω) :
    e∈blockSlots cuts p d x ω := by
  obtain ⟨b,hb,heq,hlo,hhi⟩ := (absoluteBlockGraph_mem_iff cuts x ω _).mp he
  have hbe : b=directionalGlobalEdge cuts p d e := Fin.ext (by exact_mod_cast heq.symm)
  subst b
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlo,hhi⟩

/-- The rank slots are fixed by the auxiliary record. They identify a unique
cylinder whenever the edge is outside the currently exposed run. -/
theorem finePartition_exists {k n L : ℕ} {I : Type*} [Fintype I]
    (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ) (p : Fin k) (d : Direction)
    (ω : Sample cuts) (j : Fin (pileSize cuts p)) (x : I → Prefix k (L+1))
    (hsep : ∀a b,a≠b → prefixSeparated (x a) (x b))
    (hfuture : ∀a w,inCylinder (x a) w → strictFuture d (revealWords cuts p d ω j) w)
    (hcover : ∀w:Word k (L+1),w.get 0=p → strictFuture d (revealWords cuts p d ω j) w →
      ∃a,inCylinder (x a) w) :
    ∃assign : Fin (pileSize cuts p-1) → Option I,
      ∀e v,futureFamilyView cuts p d (j.val+1) (revealWords cuts p d ω j) x v=
        futureFamilyView cuts p d (j.val+1) (revealWords cuts p d ω j) x ω →
      remainingEdgeEvent cuts D g p d (j.val+1) e v →
      match assign e with
      | none => e∈currentRunEdges cuts p d (j.val+1) (revealWords cuts p d ω j) v
      | some a => ((directionalGlobalEdge cuts p d e).val:ℤ)∈absoluteBlockGraph (x a) v := by
  let assign : Fin (pileSize cuts p-1) → Option I := fun e =>
    if h : ∃a,e∈blockSlots cuts p d (x a) ω then some h.choose else none
  refine ⟨assign,?_⟩
  intro e v hv he
  have hhist : historyFiber cuts p d (j.val+1) ω v := congrArg Prod.fst hv
  have hslot (a : I) : blockSlots cuts p d (x a) v=blockSlots cuts p d (x a) ω :=
    blockSlots_view cuts p d _ _ x a ω v hv
  have hi := he.1
  let r : Fin (pileSize cuts p) := ⟨e.val,by omega⟩
  have hh := revealWords_future_or_current cuts p d ω v j hhist r (by change j.val≤e.val; omega)
  by_cases hs : ∃a,e∈blockSlots cuts p d (x a) ω
  · dsimp only [assign]
    rw [dif_pos hs]
    let a := hs.choose
    have ha : e∈blockSlots cuts p d (x a) v := (hslot a).symm ▸ hs.choose_spec
    rcases hh with hcurrent | hf
    · have hp := blockSlots_word cuts p d (x a) v e ha
      rw [directionalGlobalEdge_word cuts D g p d e v he.2] at hp
      change inCylinder (x a) (revealWords cuts p d v r) at hp
      rw [hcurrent] at hp
      have hbad := hfuture a _ hp
      cases d <;> exact False.elim (lt_irrefl _ hbad)
    · obtain ⟨b,hb⟩ := hcover (revealWords cuts p d v r) (revealWords_first cuts p d v r) hf
      have hbg : ((directionalGlobalEdge cuts p d e).val:ℤ)∈absoluteBlockGraph (x b) v := by
        apply (absoluteBlockGraph_edge_iff cuts (x b) v _ (directionalEdge_global cuts D g p d e v he.2)).mpr
        rwa [directionalGlobalEdge_word cuts D g p d e v he.2]
      have hab : a=b := by
        by_contra hab
        exact Finset.disjoint_left.mp (blockSlots_disjoint cuts p d (x a) (x b) v (hsep a b hab))
          ha (absoluteBlockGraph_in_slots cuts p d (x b) v e hbg)
      simpa only [←hab] using hbg
  · dsimp only [assign]
    rw [dif_neg hs]
    rcases hh with hcurrent | hf
    · simpa only [currentRunEdges,Finset.mem_filter,Finset.mem_univ,true_and,revealWords,r]
        using And.intro he.1 (And.intro he.2.1 hcurrent)
    · obtain ⟨a,ha⟩ := hcover (revealWords cuts p d v r) (revealWords_first cuts p d v r) hf
      have hag : ((directionalGlobalEdge cuts p d e).val:ℤ)∈absoluteBlockGraph (x a) v := by
        apply (absoluteBlockGraph_edge_iff cuts (x a) v _ (directionalEdge_global cuts D g p d e v he.2)).mpr
        rwa [directionalGlobalEdge_word cuts D g p d e v he.2]
      exact False.elim (hs ⟨a,hslot a ▸ absoluteBlockGraph_in_slots cuts p d (x a) v e hag⟩)

end RiffleUpperV2.Conditional
