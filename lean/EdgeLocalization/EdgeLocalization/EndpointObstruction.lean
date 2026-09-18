import EdgeLocalization.FiniteLaw
import EdgeLocalization.FirstColumn

/-! Frozen F29–F30 and F33: fixed first-column endpoints cannot acquire
small atoms by intersecting with a good event. This file does not redefine
the manuscript's fluctuation exponent or assume a conditional atom bound. -/

noncomputable section

namespace EdgeLocalization

theorem balanced_endpoint_atom {a b : ℕ}
    (w : FiniteLaw (BalancedColumn a b)) :
    w.probability (fun c => lowerEndpoint c.val = a) = 1 ∧
      w.probability (fun c => upperEndpoint c.val = a + b) = 1 := by
  constructor
  · exact w.probability_of_forall _ (fun c => balanced_left_endpoint c)
  · exact w.probability_of_forall _ (fun c => balanced_right_endpoint c)

theorem balanced_endpoint_good_event {a b : ℕ}
    (w : FiniteLaw (BalancedColumn a b))
    (S : BalancedColumn a b → Prop) :
    w.probability (fun c => lowerEndpoint c.val = a ∧ S c) = w.probability S ∧
      w.probability (fun c => upperEndpoint c.val = a + b ∧ S c) = w.probability S := by
  constructor
  · exact w.probability_event_of_constant (fun c => lowerEndpoint c.val) a S
      (fun c => balanced_left_endpoint c)
  · exact w.probability_event_of_constant (fun c => upperEndpoint c.val) (a + b) S
      (fun c => balanced_right_endpoint c)

theorem no_atom_bound_below_good_mass {a b : ℕ}
    (w : FiniteLaw (BalancedColumn a b))
    (S : BalancedColumn a b → Prop) (q : ℝ) (hq : q < w.probability S) :
    ¬w.probability (fun c => lowerEndpoint c.val = a ∧ S c) ≤ q ∧
      ¬w.probability (fun c => upperEndpoint c.val = a + b ∧ S c) ≤ q := by
  rcases balanced_endpoint_good_event w S with ⟨hl, hu⟩
  rw [hl, hu]
  exact ⟨not_le_of_gt hq, not_le_of_gt hq⟩

end EdgeLocalization
