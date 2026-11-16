import RiffleUpperV2.Localization.Boundary
import RiffleUpperV2.Localization.IntervalCounting

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.Localization

/-- Counts all depths, including the empty local word. -/
theorem prefix_card_bound (k d : ℕ) (hk : 0 < k) :
    Fintype.card (Prefix k d) ≤ (d+1)*k^d := by
  change Fintype.card (Σ i : Fin (d+1), List.Vector (Fin k) i.val) ≤ _
  rw [Fintype.card_sigma]
  simp only [card_vector, Fintype.card_fin]
  calc
    _ ≤ ∑ _i : Fin (d+1), k^d := Finset.sum_le_sum (fun i _ =>
      Nat.pow_le_pow_right hk (Nat.le_of_lt_succ i.isLt))
    _ = _ := by simp

def lastDigit {k d : ℕ} (hk : 0 < k) (x : Prefix k d) : Fin k :=
  x.2.toList.getLast?.getD ⟨0,hk⟩

theorem parent_last_reconstruct {k d : ℕ} (hk : 0 < k) (x : Prefix k d)
    (hx : 0 < x.1.val) :
    (parent x).2.toList ++ [lastDigit hk x] = x.2.toList := by
  have hne : x.2.toList ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [List.Vector.toList_length, List.length_nil] at this
    omega
  have h := List.dropLast_append_getLast hne
  change x.2.toList.take (x.1.val-1) ++ [x.2.toList.getLast?.getD ⟨0,hk⟩] = x.2.toList
  rw [List.getLast?_eq_some_getLast hne]
  simpa [List.dropLast_eq_take] using h

theorem child_eq_of_last_eq {k d : ℕ} (hk : 0 < k) {x y : Prefix k d}
    (hx : 0 < x.1.val) (hy : 0 < y.1.val) (hparent : parent x = parent y)
    (hlast : lastDigit hk x = lastDigit hk y) : x = y := by
  apply prefix_ext
  rw [← parent_last_reconstruct hk x hx, ← parent_last_reconstruct hk y hy, hparent, hlast]

theorem children_card_le {k d : ℕ} (hk : 0 < k) (s : Finset (Prefix k d))
    (p : Prefix k d) (hs : ∀ x ∈ s, 0 < x.1.val ∧ parent x = p) : s.card ≤ k := by
  classical
  have hinj : (s : Set (Prefix k d)).InjOn (lastDigit hk) := by
    intro x hx y hy hxy
    exact child_eq_of_last_eq hk (hs x hx).1 (hs y hy).1
      ((hs x hx).2.trans (hs y hy).2.symm) hxy
  have h := Finset.card_le_card_of_injOn (lastDigit hk)
    (show Set.MapsTo (lastDigit hk) (s : Set (Prefix k d)) (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)) from
      fun _ _ => Finset.mem_univ _) hinj
  simpa using h

/-- Once the geometric two-parent bound holds at each depth, children cost k,
and at most d future parent depths remain. -/
theorem per_edge_multiplicity {k d : ℕ} (hk : 0 < k) (s : Finset (Prefix k d))
    (hpositive : ∀ x ∈ s, 0 < x.1.val)
    (hparents : ∀ j < d, ((s.image parent).filter (fun p => p.1.val = j)).card ≤ 2) :
    s.card ≤ 2*k*d := by
  classical
  have hchildren : ∀ p ∈ s.image parent, (s.filter (fun x => parent x = p)).card ≤ k := by
    intro p hp
    apply children_card_le hk _ p
    intro x hx
    obtain ⟨hxs,hxp⟩ := Finset.mem_filter.mp hx
    exact ⟨hpositive x hxs,hxp⟩
  have hc := Finset.card_le_mul_card_image s k hchildren
  have hdepth : ∀ p ∈ s.image parent, p.1.val ∈ Finset.range d := by
    intro p hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    apply Finset.mem_range.mpr
    change x.1.val-1 < d
    have := x.1.isLt
    have := hpositive x hx
    omega
  have hp := Finset.card_le_mul_card_image_of_maps_to hdepth 2
    (fun j hj => hparents j (Finset.mem_range.mp hj))
  rw [Finset.card_range] at hp
  calc
    s.card ≤ k * (s.image parent).card := hc
    _ ≤ k * (2*d) := Nat.mul_le_mul_left _ hp
    _ = 2*k*d := by ring

end RiffleUpperV2.Localization
