import RiffleUpperV2.Reservoir.BackwardHistory
import RiffleUpperV2.Reservoir.CurrentRemoval

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile
attribute [local instance 2000] wordDecEq

def backwardTupleHistoryConstraint {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) (j : Fin (pileSize cuts p))
    (w : Fin (pileSize cuts p) → Word k (L+1)) : Prop :=
  (∀ q, (w q).get 0 = p) ∧
  (∀ u : Word k (L+1), u.get 0 = p → backwardWords cuts p ω j < u →
    tupleCount w u = observedCount (backwardWords cuts p ω) (j.val+1) u) ∧
  observedCount (backwardWords cuts p ω) (j.val+1) (backwardWords cuts p ω j) ≤
    tupleCount w (backwardWords cuts p ω j)

theorem backwardTupleHistoryConstraint_iff {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (e : Fin (pileSize cuts p) ↪ Fin n) (ω v : Sample cuts)
    (j : Fin (pileSize cuts p)) :
    backwardTupleHistoryConstraint cuts p ω j (tupleWords e v) ↔
      (∀ q, (tupleWords e v q).get 0 = p) ∧
        historyFiber cuts p .backward (j.val+1) ω v := by
  rw [historyAtom_backward]
  unfold backwardTupleHistoryConstraint
  apply and_congr_right
  intro he
  apply and_congr
  · apply forall_congr'
    intro u
    apply imp_congr_right
    intro hu
    rw [tuplePile_wordCount cuts p e v he u hu]
  · rw [tuplePile_wordCount cuts p e v he _ (backwardWords_first cuts p ω j)]

def backwardUnmarkedHistoryConstraint {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) (j : Fin (pileSize cuts p)) (A : Finset (Fin (pileSize cuts p)))
    (a : Fin (pileSize cuts p) → Word k (L+1)) : Prop :=
  (∀ q ∈ A, (a q).get 0 = p) ∧
  (∀ u : Word k (L+1), u.get 0 = p → backwardWords cuts p ω j < u →
    selectedWordCount A a u = observedCount (backwardWords cuts p ω) (j.val+1) u) ∧
  observedCount (backwardWords cuts p ω) (j.val+1) (backwardWords cuts p ω j) ≤
    selectedWordCount A a (backwardWords cuts p ω j)

theorem backward_tupleCount_eq_selected_of_future {k L r : ℕ} (A : Finset (Fin r))
    (w : Fin r → Word k L) (s u : Word k L) (hu : s ≤ u)
    (hf : ∀ q, q ∉ A → w q < s) :
    tupleCount w u = selectedWordCount A w u := by
  apply congrArg Finset.card
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hq
    refine ⟨?_, hq⟩
    by_contra hqa
    have hh := hf q hqa
    rw [hq] at hh
    exact not_lt_of_ge hu hh
  · exact And.right

/-- Deleting marked words strictly below the current word leaves exactly
the entire history constraint. This proves both the impossible-target case
and the allowed-reserve implication without discarding lexical conditioning. -/
theorem backwardTupleHistoryConstraint_future_iff {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) (j : Fin (pileSize cuts p)) (A : Finset (Fin (pileSize cuts p)))
    (a w : Fin (pileSize cuts p) → Word k (L+1))
    (hfix : ∀ q ∈ A, w q = a q) (hfirst : ∀ q, (w q).get 0 = p)
    (hf : ∀ q, q ∉ A → w q < backwardWords cuts p ω j) :
    backwardTupleHistoryConstraint cuts p ω j w ↔ backwardUnmarkedHistoryConstraint cuts p ω j A a := by
  have ha : ∀ q ∈ A, (a q).get 0 = p := by
    intro q hq
    rw [← hfix q hq]
    exact hfirst q
  have hc (u : Word k (L+1)) (hu : backwardWords cuts p ω j ≤ u) :
      tupleCount w u = selectedWordCount A a u := by
    rw [backward_tupleCount_eq_selected_of_future A w _ u hu hf, selectedWordCount_congr A a w hfix]
  constructor
  · rintro ⟨_, hlo, hterm⟩
    refine ⟨ha, ?_, ?_⟩
    · intro u hp hu
      rw [← hc u hu.le]
      exact hlo u hp hu
    · rwa [hc _ le_rfl] at hterm
  · rintro ⟨_, hlo, hterm⟩
    refine ⟨hfirst, ?_, ?_⟩
    · intro u hp hu
      rw [hc u hu.le]
      exact hlo u hp hu
    · rwa [hc _ le_rfl]

theorem backward_reserve_tuple_allowed {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) (j : Fin (pileSize cuts p)) (A : Finset (Fin (pileSize cuts p)))
    (a w : Fin (pileSize cuts p) → Word k (L+1))
    (ha : backwardUnmarkedHistoryConstraint cuts p ω j A a)
    (hfix : ∀ q ∈ A, w q = a q) (hfirst : ∀ q, (w q).get 0 = p)
    (hf : ∀ q, q ∉ A → w q < backwardWords cuts p ω j) :
    backwardTupleHistoryConstraint cuts p ω j w :=
  (backwardTupleHistoryConstraint_future_iff cuts p ω j A a w hfix hfirst hf).mpr ha

/-- The actual chosen left reserve is a compatible completion in every
backward history whose terminal word has the backward direction. -/
theorem backward_chosenReserve_tuple_allowed {k n L D : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (g : ℝ) (ω : Sample cuts) (j : Fin (pileSize cuts p))
    (A : Finset (Fin (pileSize cuts p)))
    (a w : Fin (pileSize cuts p) → Word k (L+1))
    (v : Word k (min D L) ×ₗ Word k (min D L) ×ₗ Word k (min D L))
    (hv : chosenReserves cuts D g = some v)
    (hd : hasDirection cuts D g .backward (backwardWords cuts p ω j))
    (ha : backwardUnmarkedHistoryConstraint cuts p ω j A a)
    (hfix : ∀ q ∈ A, w q = a q) (hfirst : ∀ q, (w q).get 0 = p)
    (hreserve : ∀ q, q ∉ A → tailPrefix D (w q) = v.1) :
    backwardTupleHistoryConstraint cuts p ω j w := by
  apply backward_reserve_tuple_allowed cuts p ω j A a w ha hfix hfirst
  intro q hq
  apply fullWord_lt_of_tailPrefix_lt D
  · rw [hfirst q]
    exact (backwardWords_first cuts p ω j).symm
  · have hdir : v.2.1 ≤ tailPrefix D (backwardWords cuts p ω j) := by
      simpa only [hasDirection, hv] using hd
    rw [hreserve q hq]
    exact (chosenReserves_spec cuts D g v hv).1.trans_le hdir

/-- A removable terminal copy leaves exactly the history's forced terminal
multiplicity in the unmarked rows; it is not counted as a fresh observed copy. -/
theorem backwardUnmarkedHistoryConstraint_of_current_removal {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (ω : Sample cuts) (j : Fin (pileSize cuts p))
    (A : Finset (Fin (pileSize cuts p))) (a w : Fin (pileSize cuts p) → Word k (L+1))
    (hm : (Finset.univ \ A).card=1) (hfix : ∀ q∈A, w q=a q)
    (hh : backwardTupleHistoryConstraint cuts p ω j w)
    (hs : ∀ q, q∉A → w q=backwardWords cuts p ω j)
    (hremove : observedCount (backwardWords cuts p ω) (j.val+1) (backwardWords cuts p ω j) ≤
      tupleCount w (backwardWords cuts p ω j)-1) :
    backwardUnmarkedHistoryConstraint cuts p ω j A a := by
  have hconst : ∀ q∈Finset.univ \ A, w q=backwardWords cuts p ω j :=
    fun q hq => hs q (Finset.mem_sdiff.mp hq).2
  have hcount (u : Word k (L+1)) : tupleCount w u=selectedWordCount A a u+
      (if backwardWords cuts p ω j=u then 1 else 0) := by
    rw [tupleCount_split A w u,selectedWordCount_congr A a w hfix,
      selectedWordCount_of_constant _ w _ hconst,hm]
  refine ⟨?_,?_,?_⟩
  · intro q hq
    rw [← hfix q hq]
    exact hh.1 q
  · intro u hp hu
    have hx := hh.2.1 u hp hu
    rw [hcount u,if_neg (ne_of_lt hu),add_zero] at hx
    exact hx
  · rw [hcount _,if_pos rfl] at hremove
    omega

end RiffleUpperV2.Reservoir
