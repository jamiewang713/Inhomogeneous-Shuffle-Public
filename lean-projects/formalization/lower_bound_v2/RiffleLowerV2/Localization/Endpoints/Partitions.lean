import RiffleLowerV2.Localization.WordOrder

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Localization

def sideMatch {α β : Type*} [LT α] (x y : α → β) (j : α) (d : β) : Prop :=
  y j = d ∧ ∀ h, h < j → y h = x h

theorem sideMatch_unique {α β : Type*} [LinearOrder α]
    {x y : α → β} {j q : α} {d e : β}
    (hj : sideMatch x y j d) (hq : sideMatch x y q e)
    (hd : d ≠ x j) (he : e ≠ x q) : j = q := by
  rcases lt_trichotomy j q with h | h | h
  · exact (hd (hj.1.symm.trans (hq.2 j h))).elim
  · exact h
  · exact (he (hq.1.symm.trans (hj.2 q h))).elim

/-- Unique first differences give an exact pointwise indicator partition. -/
theorem sum_sideMatch {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β]
    [DecidableEq β] (x y : α → β) (R : β → β → Prop)
    (hR : ∀ d e, R d e → d ≠ e) :
    (∑ j : α, ∑ d ∈ Finset.univ.filter (fun d => R d (x j)),
      if sideMatch x y j d then (1 : ℝ) else 0) =
      if ∃ j, R (y j) (x j) ∧ ∀ h, h < j → y h = x h then 1 else 0 := by
  classical
  by_cases hex : ∃ j, R (y j) (x j) ∧ ∀ h, h < j → y h = x h
  · rw [if_pos hex]
    obtain ⟨j, hjR, hjpre⟩ := hex
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single (y j)]
      · exact if_pos ⟨rfl, hjpre⟩
      · intro d _ hd
        exact if_neg (fun hm => hd hm.1.symm)
      · intro hn
        exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjR⟩)).elim
    · intro q _ hqj
      apply Finset.sum_eq_zero
      intro d hd
      have hdR := (Finset.mem_filter.mp hd).2
      apply if_neg
      intro hq
      exact hqj (sideMatch_unique hq ⟨rfl, hjpre⟩ (hR _ _ hdR) (hR _ _ hjR))
    · simp
  · rw [if_neg hex]
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro d hd
    apply if_neg
    intro hside
    exact hex ⟨j, hside.1.symm ▸ (Finset.mem_filter.mp hd).2, hside.2⟩

/-- Weighted rows split into disjoint first-difference side cylinders. -/
theorem weighted_side_partition {α β Ω : Type*} [Fintype α] [LinearOrder α]
    [Fintype β] [DecidableEq β] [Fintype Ω] (x : α → β) (y : Ω → α → β)
    (A : Ω → Prop) (f : Ω → ℝ) (R : β → β → Prop)
    (hR : ∀ d e, R d e → d ≠ e) :
    (∑ ω, if A ω ∧ (∃ j, R (y ω j) (x j) ∧ ∀ h, h < j → y ω h = x h)
      then f ω else 0) =
    ∑ j : α, ∑ d ∈ Finset.univ.filter (fun d => R d (x j)),
      ∑ ω, if A ω ∧ sideMatch x (y ω) j d then f ω else 0 := by
  classical
  calc
    _ = ∑ ω, ∑ j : α, ∑ d ∈ Finset.univ.filter (fun d => R d (x j)),
        if A ω ∧ sideMatch x (y ω) j d then f ω else 0 := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hA : A ω
      · simp only [hA, true_and]
        have h := congrArg (fun t : ℝ => t * f ω) (sum_sideMatch x (y ω) R hR)
        simpa only [Finset.sum_mul, ite_mul, one_mul, zero_mul] using h.symm
      · simp [hA]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm

end RiffleLowerV2.Localization
