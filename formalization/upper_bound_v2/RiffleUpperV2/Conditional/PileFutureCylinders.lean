import RiffleUpperV2.Conditional.PastCylinders
import RiffleUpperV2.Conditional.CurrentRunGeometry
import RiffleUpperV2.Exploration.DirectionalRanks

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional
open Exploration Reservoir
attribute [local instance 2000] Reservoir.wordDecEq

/-- Future means later in the spatial revelation order; word coordinates
remain in chronological order in both directions. -/
def strictFuture {k K : ℕ} (d : Direction) (s w : Word k K) : Prop :=
  match d with | .forward => s < w | .backward => w < s

theorem firstDigit_prefix {k L : ℕ} (w : Word k (L+1)) (p : Fin k) :
    w.get 0=p ↔ [p] <+: w.toList := by
  rcases w with ⟨l,hl⟩
  cases l with
  | nil => simp at hl
  | cons a l => simp [List.Vector.get,eq_comm]

theorem firstDigit_interval {k L : ℕ} {s t w : Word k (L+1)} {p : Fin k}
    (hs : s.get 0=p) (ht : t.get 0=p) (hsw : s≤w) (hwt : w≤t) : w.get 0=p :=
  (firstDigit_prefix w p).mpr (RiffleShuffle.prefix_lex_convex hsw hwt
    ((firstDigit_prefix s p).mp hs) ((firstDigit_prefix t p).mp ht))

def pileWordSet {k L : ℕ} (p : Fin k) : Finset (Word k (L+1)) :=
  Finset.univ.filter fun w => w.get 0=p

def pileTop {k L : ℕ} (p : Fin k) (s : Word k (L+1)) (hs : s.get 0=p) : Word k (L+1) :=
  (pileWordSet p).max' ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩⟩

def pileBottom {k L : ℕ} (p : Fin k) (s : Word k (L+1)) (hs : s.get 0=p) : Word k (L+1) :=
  (pileWordSet p).min' ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩⟩

theorem pileTop_first {k L : ℕ} (p : Fin k) (s : Word k (L+1)) (hs : s.get 0=p) :
    (pileTop p s hs).get 0=p := by
  exact (Finset.mem_filter.mp (Finset.max'_mem (pileWordSet p)
    ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩⟩)).2

theorem pileBottom_first {k L : ℕ} (p : Fin k) (s : Word k (L+1)) (hs : s.get 0=p) :
    (pileBottom p s hs).get 0=p := by
  exact (Finset.mem_filter.mp (Finset.min'_mem (pileWordSet p)
    ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩⟩)).2

/-- A maximal strict-future cover of the whole first-column pile. Enlarging
the directional part of the pile does not change its logarithmic cost. -/
def pileFutureCylinders {k L : ℕ} (p : Fin k) (d : Direction)
    (s : Word k (L+1)) (hs : s.get 0=p) : Finset (Prefix k (L+1)) :=
  match d with
  | .forward => futureCylinders s (pileTop p s hs)
  | .backward => pastCylinders (pileBottom p s hs) s

theorem pileFutureCylinders_cover {k L : ℕ} (p : Fin k) (d : Direction)
    (s : Word k (L+1)) (hs : s.get 0=p) (w : Word k (L+1)) :
    (w.get 0=p ∧ strictFuture d s w) ↔ ∃x∈pileFutureCylinders p d s hs,inCylinder x w := by
  cases d
  · rw [pileFutureCylinders,← futureCylinders_cover]
    constructor
    · rintro ⟨hw,hfuture⟩
      exact ⟨hfuture,Finset.le_max' _ w (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩)⟩
    · rintro ⟨hsw,hwt⟩
      exact ⟨firstDigit_interval hs (pileTop_first p s hs) hsw.le hwt,hsw⟩
  · rw [pileFutureCylinders,← pastCylinders_cover]
    constructor
    · rintro ⟨hw,hfuture⟩
      exact ⟨Finset.min'_le _ w (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩),hfuture⟩
    · rintro ⟨hsw,hwt⟩
      exact ⟨firstDigit_interval (pileBottom_first p s hs) hs hsw hwt.le,hwt⟩

theorem pileFutureCylinders_card {k L : ℕ} (p : Fin k) (d : Direction)
    (s : Word k (L+1)) (hs : s.get 0=p) : (pileFutureCylinders p d s hs).card≤2*k*(L+1) := by
  cases d
  · exact futureCylinders_card _ _
  · exact pastCylinders_card _ _

theorem pileFutureCylinders_depth_pos {k L : ℕ} (p : Fin k) (d : Direction)
    (s : Word k (L+1)) (hs : s.get 0=p) {x : Prefix k (L+1)}
    (hx : x∈pileFutureCylinders p d s hs) : 0<x.1.val := by
  cases d
  · exact futureCylinders_depth_pos _ _ hx
  · exact pastCylinders_depth_pos _ _ hx

theorem pileFutureCylinders_antichain {k L : ℕ} (p : Fin k) (d : Direction)
    (s : Word k (L+1)) (hs : s.get 0=p) {x y : Prefix k (L+1)}
    (hx : x∈pileFutureCylinders p d s hs) (hy : y∈pileFutureCylinders p d s hs) (hne : x≠y) :
    ¬x.2.toList <+: y.2.toList ∧ ¬y.2.toList <+: x.2.toList := by
  cases d
  · exact futureCylinders_antichain _ _ hx hy hne
  · exact pastCylinders_antichain _ _ hx hy hne

theorem revealWords_future_or_current {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (ω v : Sample cuts) (j : Fin (pileSize cuts p))
    (hv : historyFiber cuts p d (j.val+1) ω v) (r : Fin (pileSize cuts p)) (hjr : j≤r) :
    revealWords cuts p d v r=revealWords cuts p d ω j ∨
      strictFuture d (revealWords cuts p d ω j) (revealWords cuts p d v r) := by
  have hj : revealWords cuts p d v j=revealWords cuts p d ω j :=
    revealed_word_eq cuts p d (j.val+1) hv j (by omega)
  cases d
  · have hm := pileWords_monotone cuts p v hjr
    change revealWords cuts p .forward v j≤revealWords cuts p .forward v r at hm
    rw [hj] at hm
    rcases eq_or_lt_of_le hm with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  · have hm := backwardWords_antitone cuts p v hjr
    change revealWords cuts p .backward v r≤revealWords cuts p .backward v j at hm
    rw [hj] at hm
    rcases eq_or_lt_of_le hm with h | h
    · exact Or.inl h
    · exact Or.inr h

/-- If any remaining directional edge exists then its last revealed word
has that direction, so the reservoir estimate applies to this history. -/
theorem current_hasDirection_of_remaining {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g : ℝ) (p : Fin k) (d : Direction) (ω v : Sample cuts)
    (j : Fin (pileSize cuts p)) (hv : historyFiber cuts p d (j.val+1) ω v)
    (e : Fin (pileSize cuts p-1)) (hi : j.val+1≤e.val+1)
    (he : directionalEdge cuts D g p d e v) :
    hasDirection cuts D g d (revealWords cuts p d ω j) := by
  let r : Fin (pileSize cuts p) := ⟨e.val,by omega⟩
  have hjr : j≤r := by change j.val≤e.val; omega
  have hj : revealWords cuts p d v j=revealWords cuts p d ω j :=
    revealed_word_eq cuts p d (j.val+1) hv j (by omega)
  have hr : hasDirection cuts D g d (revealWords cuts p d v r) := he.2
  have hh : (revealWords cuts p d ω j).get 0=(revealWords cuts p d v r).get 0 := by
    rw [revealWords_first,revealWords_first]
  cases hd : chosenReserves cuts D g with
  | none => simp [hasDirection,hd] at hr
  | some a =>
    simp only [hasDirection,hd]
    cases d
    · have hm := pileWords_monotone cuts p v hjr
      change revealWords cuts p .forward v j≤revealWords cuts p .forward v r at hm
      rw [hj] at hm
      exact (tailPrefix_mono_same_head D hh hm).trans (by simpa [hasDirection,hd] using hr)
    · have hm := backwardWords_antitone cuts p v hjr
      change revealWords cuts p .backward v r≤revealWords cuts p .backward v j at hm
      rw [hj] at hm
      exact (show a.2.1≤tailPrefix D (revealWords cuts p .backward v r) from by simpa [hasDirection,hd] using hr).trans
        (tailPrefix_mono_same_head D hh.symm hm)

end RiffleUpperV2.Conditional
