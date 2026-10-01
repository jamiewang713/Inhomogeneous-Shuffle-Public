import RiffleLowerV2.Localization.Endpoints.Partitions

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Localization

theorem prod_subtype_dite {α : Type*} [Fintype α] (I : Finset α) (f : I → ℝ) :
    (∏ j : α, if hj : j ∈ I then f ⟨j, hj⟩ else 1) = ∏ j : I, f j := by
  classical
  symm
  apply Finset.prod_bij_ne_one (fun (j : I) _ _ => j.val)
  · intros; exact Finset.mem_univ _
  · intro a _ _ b _ _ hab
    exact Subtype.ext hab
  · intro b _ hb
    have hbi : b ∈ I := by
      by_contra h
      simp [h] at hb
    exact ⟨⟨b, hbi⟩, Finset.mem_univ _, by simpa [hbi] using hb, rfl⟩
  · intro a _ _
    simp [a.property]

def functionMass {α β : Type*} [Fintype α] (p : α → β → ℝ) (y : α → β) : ℝ :=
  ∏ j, p j (y j)

def sideWeight {α β : Type*} [Fintype α] [LinearOrder α]
    (p : α → β → ℝ) (x : α → β) (j : α) (d : β) : ℝ :=
  ∏ h, if h ≤ j then p h (if h = j then d else x h) else 1

theorem functionMass_sum {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (p : α → β → ℝ) (hp : ∀ j, ∑ d, p j d = 1) :
    ∑ y, functionMass p y = 1 := by
  classical
  simp only [functionMass]
  rw [← Fintype.prod_sum]
  simp [hp]

/-- Summing unused independent coordinates removes their normalized factors. -/
theorem cylinder_mass {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (p : α → β → ℝ) (hp : ∀ j, ∑ d, p j d = 1)
    (S : α → Prop) (z : α → β) :
    (∑ y : α → β, if ∀ h, S h → y h = z h then functionMass p y else 0) =
      ∏ h, if S h then p h (z h) else 1 := by
  classical
  let f : α → β → ℝ := fun h d => if S h then if d = z h then p h d else 0 else p h d
  have hprod (y : α → β) :
      (∏ h, f h (y h)) = if ∀ h, S h → y h = z h then functionMass p y else 0 := by
    by_cases hy : ∀ h, S h → y h = z h
    · rw [if_pos hy]
      apply Finset.prod_congr rfl
      intro h _
      by_cases hh : S h
      · simp [f, hh, hy h hh]
      · simp [f, hh]
    · rw [if_neg hy]
      push Not at hy
      obtain ⟨h, hh, hne⟩ := hy
      exact Finset.prod_eq_zero (Finset.mem_univ h) (by simp [f, hh, hne])
  simp_rw [← hprod]
  rw [← Fintype.prod_sum]
  apply Finset.prod_congr rfl
  intro h _
  by_cases hh : S h
  · simp [f, hh]
  · simp [f, hh, hp]

theorem sideMatch_iff_coordinates {α β : Type*} [LinearOrder α]
    (x y : α → β) (j : α) (d : β) :
    sideMatch x y j d ↔ ∀ h, h ≤ j → y h = if h = j then d else x h := by
  constructor
  · rintro ⟨hj, hpre⟩ h hh
    by_cases he : h = j
    · subst h; simpa using hj
    · simpa [he] using hpre h (lt_of_le_of_ne hh he)
  · intro h
    refine ⟨by simpa using h j le_rfl, ?_⟩
    intro q hq
    simpa [ne_of_lt hq] using h q hq.le

theorem sideWeight_eq_sum {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β]
    (p : α → β → ℝ) (hp : ∀ j, ∑ d, p j d = 1)
    (x : α → β) (j : α) (d : β) :
    sideWeight p x j d =
      ∑ y, if sideMatch x y j d then functionMass p y else 0 := by
  simp_rw [sideMatch_iff_coordinates]
  exact (cylinder_mass p hp (fun h => h ≤ j) (fun h => if h = j then d else x h)).symm

theorem sideWeight_nonneg {α β : Type*} [Fintype α] [LinearOrder α]
    (p : α → β → ℝ) (hp : ∀ j d, 0 ≤ p j d) (x : α → β) (j : α) (d : β) :
    0 ≤ sideWeight p x j d := by
  unfold sideWeight
  apply Finset.prod_nonneg
  intro h _
  split_ifs <;> first | exact hp _ _ | norm_num

theorem sum_sideWeight_le_one {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β]
    [DecidableEq β] (p : α → β → ℝ) (hp : ∀ j, ∑ d, p j d = 1)
    (hp0 : ∀ j d, 0 ≤ p j d) (x : α → β) (R : β → β → Prop)
    (hR : ∀ d e, R d e → d ≠ e) :
    (∑ j : α, ∑ d ∈ Finset.univ.filter (fun d => R d (x j)), sideWeight p x j d) ≤ 1 := by
  simp_rw [sideWeight_eq_sum p hp]
  have hs := weighted_side_partition x (fun y : α → β => y) (fun _ => True)
    (functionMass p) R hR
  simp only [true_and] at hs
  rw [← hs, ← functionMass_sum p hp]
  apply Finset.sum_le_sum
  intro y _
  split_ifs
  · exact le_rfl
  · exact Finset.prod_nonneg (fun h _ => hp0 h (y h))

end RiffleLowerV2.Localization
