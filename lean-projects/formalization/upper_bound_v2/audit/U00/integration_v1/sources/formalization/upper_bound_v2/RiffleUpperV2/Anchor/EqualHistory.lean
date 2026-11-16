import RiffleUpperV2.Anchor.EqualReveal
import RiffleUpperV2.Anchor.History

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile

/-- A finite history of all future columns except one selected column. -/
def otherColumnHistory {k n d : ℕ} {cuts : Cuts k n d} (j : Fin d) (ω : Sample cuts) :
    Fin d → Option (Fin n → Fin k) := fun t => if t = j then none else some (ω t).val

/-- The exact source reveal in the coincident-side-maximizer case. -/
def equalRevealHistory {k n d : ℕ} {cuts : Cuts k n d} (j : Fin d) (a : Fin k)
    (ω : Sample cuts) := (otherColumnHistory j ω, equalityRows a (ω j))

theorem otherColumnHistory_eq_iff {k n d : ℕ} {cuts : Cuts k n d}
    (j : Fin d) (ω₀ ω : Sample cuts) :
    otherColumnHistory j ω = otherColumnHistory j ω₀ ↔
      ∀ t : Fin d, t ≠ j → ω t = ω₀ t := by
  constructor
  · intro h t ht
    have hh := congrFun h t
    simp only [otherColumnHistory, ht, if_false, Option.some.injEq] at hh
    exact Subtype.ext hh
  · intro h
    funext t
    by_cases ht : t = j
    · simp only [otherColumnHistory, ht, if_true]
    · simp only [otherColumnHistory, ht, if_false, h t ht]

theorem equalRevealHistory_eq_iff {k n d : ℕ} {cuts : Cuts k n d}
    (j : Fin d) (a : Fin k) (ω₀ ω : Sample cuts) :
    equalRevealHistory j a ω = equalRevealHistory j a ω₀ ↔ equalRevealFiber j a ω₀ ω := by
  simp only [equalRevealHistory, Prod.mk.injEq, otherColumnHistory_eq_iff, equalRevealFiber]

private theorem entry_eq_of_other {k n d : ℕ} {cuts : Cuts k n d}
    {j t : Fin d} {ω₀ ω : Sample cuts} {a : Fin k}
    (hf : equalRevealFiber j a ω₀ ω) (ht : t ≠ j) (r : Fin n) :
    sampleEntry ω r t = sampleEntry ω₀ r t := congrArg (fun c => c.val r) (hf.1 t ht)

/-- The labeled internal cylinder is fixed by the equal-set reveal, even when
x is the boundary join itself or a full-word continuation. -/
theorem prefixRows_eq_of_equalReveal {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω₀ ω : Sample cuts)
    (hf : equalRevealFiber (prefixColumn x j) (x.2.get j) ω₀ ω) :
    prefixRows R x ω = prefixRows R x ω₀ := by
  ext r
  simp only [prefixRows, Finset.mem_filter,
    RiffleLowerV2.Thinning.prefix_coordinates_iff]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  by_cases hi : i = j
  · subst i
    change ((ω (prefixColumn x j)).val r = x.2.get j) ↔
      ((ω₀ (prefixColumn x j)).val r = x.2.get j)
    constructor
    · intro hh
      have hm : r ∈ equalityRows (x.2.get j) (ω (prefixColumn x j)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ r, hh⟩
      have hm' : r ∈ equalityRows (x.2.get j) (ω₀ (prefixColumn x j)) := hf.2 ▸ hm
      change r ∈ Finset.univ.filter (fun r => (ω₀ (prefixColumn x j)).val r = x.2.get j) at hm'
      have hh' := Finset.mem_filter.mp hm'
      exact hh'.2
    · intro hh
      have hm : r ∈ equalityRows (x.2.get j) (ω₀ (prefixColumn x j)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ r, hh⟩
      have hm' : r ∈ equalityRows (x.2.get j) (ω (prefixColumn x j)) := hf.2.symm ▸ hm
      change r ∈ Finset.univ.filter (fun r => (ω (prefixColumn x j)).val r = x.2.get j) at hm'
      have hh' := Finset.mem_filter.mp hm'
      exact hh'.2
  · have ht : prefixColumn x i ≠ prefixColumn x j := by
      intro ht
      apply hi
      exact Fin.ext (congrArg (fun q : Fin d => q.val) ht)
    have he := entry_eq_of_other hf ht r
    exact iff_of_eq (congrArg (fun a => a = x.2.get i) he)

/-- The fine equal-case history contains the source U_x, with no restriction
that x must be a proper descendant of its join. -/
theorem equalReveal_refines_internal {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) :
    Refines (equalRevealHistory (cuts := cuts) (prefixColumn x j) (x.2.get j))
      (internalHistory R x) := by
  intro ω ω' he
  have hf := (equalRevealHistory_eq_iff (prefixColumn x j) (x.2.get j) ω' ω).mp he
  have hr := prefixRows_eq_of_equalReveal R x j ω' ω hf
  funext r
  by_cases h : r ∈ prefixRows R x ω'
  · have h' : r ∈ prefixRows R x ω := hr.symm ▸ h
    simp only [internalHistory, h, h', if_pos, Option.some.injEq]
    funext t
    by_cases ht : t = prefixColumn x j
    · subst t
      exact (prefixRows_coordinates R x ω r h' j).trans
        (prefixRows_coordinates R x ω' r h j).symm
    · exact entry_eq_of_other hf ht r
  · have h' : r ∉ prefixRows R x ω := by simpa only [hr] using h
    simp only [internalHistory, h, h', if_false]

end RiffleUpperV2.Anchor
