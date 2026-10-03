import RiffleUpperV2.Anchor.Definitions
import RiffleLowerV2.Thinning.PrefixCoordinates

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile

abbrev SuffixHistory (k n d : ℕ) := Fin n → Option (Fin d → Option (Fin k))

/-- The literal U_x history: the labeled cylinder and only its future digits. -/
def suffixHistory {k n d : ℕ} {cuts : Cuts k n d} (R : Finset (Fin n))
    (x : Prefix k d) (ω : Sample cuts) : SuffixHistory k n d :=
  fun r => if r ∈ prefixRows R x ω then
    some (fun j => if x.1.val ≤ j.val then some (sampleEntry ω r j) else none) else none

theorem prefixRows_coordinates {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) (r : Fin n)
    (hr : r ∈ prefixRows R x ω) (j : Fin x.1.val) :
    sampleEntry ω r (prefixColumn x j) = x.2.get j := by
  exact (RiffleLowerV2.Thinning.prefix_coordinates_iff x ω r).mp
    (Finset.mem_filter.mp hr).2 j

/-- Storing the already known prefix adds no information to the finite history. -/
theorem internalHistory_refines_suffix {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (x : Prefix k d) :
    Refines (internalHistory (cuts := cuts) R x) (suffixHistory R x) := by
  intro ω ω' h
  funext r
  have hr := congrFun h r
  by_cases ha : r ∈ prefixRows R x ω <;> by_cases hb : r ∈ prefixRows R x ω'
  · simp only [internalHistory, ha, hb, if_pos, Option.some.injEq] at hr
    simp only [suffixHistory, ha, hb, if_pos]
    congr 1
    funext j
    rw [congrFun hr j]
  · simp [internalHistory, ha, hb] at hr
  · simp [internalHistory, ha, hb] at hr
  · simp [suffixHistory, ha, hb]

/-- Conversely the source's labeled suffix history determines each stored word. -/
theorem suffixHistory_refines_internal {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (x : Prefix k d) :
    Refines (suffixHistory (cuts := cuts) R x) (internalHistory R x) := by
  intro ω ω' h
  funext r
  have hr := congrFun h r
  by_cases ha : r ∈ prefixRows R x ω <;> by_cases hb : r ∈ prefixRows R x ω'
  · simp only [suffixHistory, ha, hb, if_pos, Option.some.injEq] at hr
    simp only [internalHistory, ha, hb, if_pos]
    congr 1
    funext j
    by_cases hj : x.1.val ≤ j.val
    · have hh := congrFun hr j
      simpa only [hj, if_pos, Option.some.injEq] using hh
    · let i : Fin x.1.val := ⟨j.val, by omega⟩
      have hi : prefixColumn x i = j := by apply Fin.ext; rfl
      rw [← hi]
      exact (prefixRows_coordinates R x ω r ha i).trans
        (prefixRows_coordinates R x ω' r hb i).symm
  · simp [suffixHistory, ha, hb] at hr
  · simp [suffixHistory, ha, hb] at hr
  · simp [internalHistory, ha, hb]

/-- The cylinder size is measurable in either equivalent history. -/
theorem internalHistory_count {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (x : Prefix k d) :
    Refines (internalHistory (cuts := cuts) R x) (fun ω => (prefixRows R x ω).card) := by
  intro ω ω' h
  apply congrArg Finset.card
  ext r
  have hr := congrFun h r
  by_cases ha : r ∈ prefixRows R x ω <;> by_cases hb : r ∈ prefixRows R x ω'
  · exact iff_of_true ha hb
  · simp [internalHistory, ha, hb] at hr
  · simp [internalHistory, ha, hb] at hr
  · exact iff_of_false ha hb

end RiffleUpperV2.Anchor
