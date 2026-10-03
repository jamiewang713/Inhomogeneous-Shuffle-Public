import RiffleUpperV2.Anchor.EqualHistory
import RiffleUpperV2.Anchor.LexSplit

noncomputable section
namespace RiffleUpperV2.Anchor
open TimeProfile

/-- Coordinates lo,...,hi-1 of a row, always in local post-anchor time. -/
def rowSlice {k n d : ℕ} {cuts : Cuts k n d} (ω : Sample cuts) (r : Fin n)
    (lo hi : ℕ) : List (Fin k) := ((rowWord ω r).toList.take hi).drop lo

theorem rowSlice_eq {k n d : ℕ} {cuts : Cuts k n d} (ω ω' : Sample cuts)
    (r : Fin n) (lo hi : ℕ) (hlh : lo ≤ hi) (hhi : hi ≤ d)
    (h : ∀ t : Fin d, lo ≤ t.val → t.val < hi → sampleEntry ω r t = sampleEntry ω' r t) :
    rowSlice ω r lo hi = rowSlice ω' r lo hi := by
  apply List.ext_getElem
  · simp [rowSlice]
  · intro i hi₁ hi₂
    have hit : i + lo < hi := by
      simp only [rowSlice, List.length_drop, List.length_take, List.Vector.toList_length,
        Nat.min_eq_left hhi] at hi₁
      omega
    have hid : lo + i < d := by omega
    let t : Fin d := ⟨lo+i,hid⟩
    have he := h t (by change lo ≤ lo+i; omega) (by change lo+i < hi; omega)
    have h₁ := RiffleLowerV2.rowWord_get ω r t
    have h₂ := RiffleLowerV2.rowWord_get ω' r t
    have hall := h₁.trans (he.trans h₂.symm)
    simpa only [rowSlice, List.getElem_drop, List.getElem_take,
      List.Vector.get, List.Vector.toList, Fin.cast, List.get_eq_getElem, t] using hall

theorem rowSlice_get {k n d : ℕ} {cuts : Cuts k n d} (ω : Sample cuts)
    (r : Fin n) (x : Prefix k d) (i : Fin x.1.val) :
    ((rowWord ω r).toList.take x.1.val)[i.val]'(by simp; have := x.1.isLt; omega) =
      sampleEntry ω r (prefixColumn x i) := by
  have he := RiffleLowerV2.rowWord_get ω r (prefixColumn x i)
  simpa only [List.getElem_take, List.Vector.get, List.Vector.toList,
    Fin.cast, List.get_eq_getElem, prefixColumn] using he

/-- Exact lexicographic classification by the digit at j and its two sides. -/
theorem row_precedes_split {k n d : ℕ} {cuts : Cuts k n d} (ω : Sample cuts)
    (r : Fin n) (x : Prefix k d) (j : Fin x.1.val) :
    (rowWord ω r).toList.take x.1.val < x.2.toList ↔
      rowSlice ω r 0 j.val < x.2.toList.take j.val ∨
      (rowSlice ω r 0 j.val = x.2.toList.take j.val ∧
        (sampleEntry ω r (prefixColumn x j) < x.2.get j ∨
          (sampleEntry ω r (prefixColumn x j) = x.2.get j ∧
            rowSlice ω r (j.val+1) x.1.val < x.2.toList.drop (j.val+1)))) := by
  have hju : j.val < ((rowWord ω r).toList.take x.1.val).length := by
    simp only [List.length_take, List.Vector.toList_length]
    have := x.1.isLt
    omega
  have hjv : j.val < x.2.toList.length := by simpa using j.isLt
  have he := list_split_lt_iff ((rowWord ω r).toList.take x.1.val) x.2.toList j.val hju hjv
  rw [rowSlice_get] at he
  simpa only [rowSlice, List.drop_zero, List.take_take, Nat.min_eq_left j.isLt.le,
    List.Vector.get, List.Vector.toList, Fin.cast, List.get_eq_getElem] using he

end RiffleUpperV2.Anchor
