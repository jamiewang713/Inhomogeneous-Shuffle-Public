import RiffleUpperV2.Reservoir.FirstColumn
import RiffleUpperV2.Exploration.DirectionalRanks

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration
attribute [local instance 2000] wordDecEq

def selectedWordCount {k L r : ℕ} (A : Finset (Fin r))
    (w : Fin r → Word k L) (u : Word k L) : ℕ := (A.filter fun q => w q = u).card

def unmarkedHistoryConstraint {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) (j : Fin (pileSize cuts p)) (A : Finset (Fin (pileSize cuts p)))
    (a : Fin (pileSize cuts p) → Word k (L+1)) : Prop :=
  (∀ q ∈ A, (a q).get 0 = p) ∧
  (∀ u : Word k (L+1), u.get 0 = p → u < pileWords cuts p ω j →
    selectedWordCount A a u = observedCount (pileWords cuts p ω) (j.val+1) u) ∧
  observedCount (pileWords cuts p ω) (j.val+1) (pileWords cuts p ω j) ≤
    selectedWordCount A a (pileWords cuts p ω j)

theorem selectedWordCount_congr {k L r : ℕ} (A : Finset (Fin r))
    (a w : Fin r → Word k L) (h : ∀ q ∈ A, w q = a q) (u : Word k L) :
    selectedWordCount A w u = selectedWordCount A a u := by
  apply congrArg Finset.card
  exact Finset.filter_congr (fun q hq => by rw [h q hq])

theorem tupleCount_eq_selected_of_future {k L r : ℕ} (A : Finset (Fin r))
    (w : Fin r → Word k L) (s u : Word k L) (hu : u ≤ s)
    (hf : ∀ q, q ∉ A → s < w q) :
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

/-- Deleting marked words strictly beyond the current word leaves exactly
the entire history constraint. This proves both the impossible-target case
and the allowed-reserve implication without discarding lexical conditioning. -/
theorem tupleHistoryConstraint_future_iff {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) (j : Fin (pileSize cuts p)) (A : Finset (Fin (pileSize cuts p)))
    (a w : Fin (pileSize cuts p) → Word k (L+1))
    (hfix : ∀ q ∈ A, w q = a q) (hfirst : ∀ q, (w q).get 0 = p)
    (hf : ∀ q, q ∉ A → pileWords cuts p ω j < w q) :
    tupleHistoryConstraint cuts p ω j w ↔ unmarkedHistoryConstraint cuts p ω j A a := by
  have ha : ∀ q ∈ A, (a q).get 0 = p := by
    intro q hq
    rw [← hfix q hq]
    exact hfirst q
  have hc (u : Word k (L+1)) (hu : u ≤ pileWords cuts p ω j) :
      tupleCount w u = selectedWordCount A a u := by
    rw [tupleCount_eq_selected_of_future A w _ u hu hf, selectedWordCount_congr A a w hfix]
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

theorem reserve_tuple_allowed {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) (j : Fin (pileSize cuts p)) (A : Finset (Fin (pileSize cuts p)))
    (a w : Fin (pileSize cuts p) → Word k (L+1))
    (ha : unmarkedHistoryConstraint cuts p ω j A a)
    (hfix : ∀ q ∈ A, w q = a q) (hfirst : ∀ q, (w q).get 0 = p)
    (hf : ∀ q, q ∉ A → pileWords cuts p ω j < w q) :
    tupleHistoryConstraint cuts p ω j w :=
  (tupleHistoryConstraint_future_iff cuts p ω j A a w hfix hfirst hf).mpr ha

/-- The actual chosen right reserve is a compatible completion in every
forward history whose terminal word has the forward direction. -/
theorem chosenReserve_tuple_allowed {k n L D : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (g : ℝ) (ω : Sample cuts) (j : Fin (pileSize cuts p))
    (A : Finset (Fin (pileSize cuts p)))
    (a w : Fin (pileSize cuts p) → Word k (L+1))
    (v : Word k (min D L) ×ₗ Word k (min D L) ×ₗ Word k (min D L))
    (hv : chosenReserves cuts D g = some v)
    (hd : hasDirection cuts D g .forward (pileWords cuts p ω j))
    (ha : unmarkedHistoryConstraint cuts p ω j A a)
    (hfix : ∀ q ∈ A, w q = a q) (hfirst : ∀ q, (w q).get 0 = p)
    (hreserve : ∀ q, q ∉ A → tailPrefix D (w q) = v.2.2) :
    tupleHistoryConstraint cuts p ω j w := by
  apply reserve_tuple_allowed cuts p ω j A a w ha hfix hfirst
  intro q hq
  apply fullWord_lt_of_tailPrefix_lt D
  · rw [hfirst q]
    exact pileWords_first cuts p ω j
  · have hdir : tailPrefix D (pileWords cuts p ω j) ≤ v.2.1 := by
      simpa only [hasDirection, hv] using hd
    rw [hreserve q hq]
    exact hdir.trans_lt (chosenReserves_spec cuts D g v hv).2.1

end RiffleUpperV2.Reservoir
