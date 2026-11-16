import RiffleUpperV2.Shared.Model
import RiffleLowerV2.Thinning.PrefixCoordinates

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.Localization

/-- Future-only truncation; the anchor has already been exposed. -/
def takePrefix {k d : ℕ} (x : Prefix k d) (m : ℕ) (hm : m ≤ x.1.val) : Prefix k d :=
  ⟨⟨m, by have := x.1.isLt; omega⟩, RiffleShuffle.truncate hm x.2⟩

def parent {k d : ℕ} (x : Prefix k d) : Prefix k d :=
  takePrefix x (x.1.val-1) (Nat.sub_le _ _)

theorem prefix_ext {k d : ℕ} {x y : Prefix k d} (h : x.2.toList = y.2.toList) : x = y := by
  have hlen : x.1 = y.1 := by
    apply Fin.ext
    have := congrArg List.length h
    simpa using this
  rcases x with ⟨i,x⟩
  rcases y with ⟨j,y⟩
  dsimp at hlen
  subst j
  congr 1
  exact Subtype.ext h

theorem prefix_length_le {k d : ℕ} {x y : Prefix k d}
    (h : x.2.toList <+: y.2.toList) : x.1.val ≤ y.1.val := by
  simpa using h.length_le

theorem prefix_eq_of_length {k d : ℕ} {x y : Prefix k d}
    (h : x.2.toList <+: y.2.toList) (hlen : x.1.val = y.1.val) : x = y := by
  apply prefix_ext
  exact h.eq_of_length (by simpa using hlen)

@[simp] theorem takePrefix_length {k d : ℕ} (x : Prefix k d) (m : ℕ) (hm : m ≤ x.1.val) :
    (takePrefix x m hm).1.val = m := rfl

@[simp] theorem takePrefix_list {k d : ℕ} (x : Prefix k d) (m : ℕ) (hm : m ≤ x.1.val) :
    (takePrefix x m hm).2.toList = x.2.toList.take m := rfl

theorem takePrefix_isPrefix {k d : ℕ} (x : Prefix k d) (m : ℕ) (hm : m ≤ x.1.val) :
    (takePrefix x m hm).2.toList <+: x.2.toList := List.take_prefix _ _

theorem takePrefix_self {k d : ℕ} (x : Prefix k d) : takePrefix x x.1.val le_rfl = x := by
  apply prefix_ext
  rw [takePrefix_list]
  exact List.take_of_length_le (by simp)

theorem prefix_parent {k d : ℕ} {v x : Prefix k d} (hvx : v.2.toList <+: x.2.toList)
    (hlt : v.1.val < x.1.val) : v.2.toList <+: (parent x).2.toList := by
  apply List.prefix_of_prefix_length_le hvx (takePrefix_isPrefix _ _ _)
  simp only [parent, takePrefix_list, List.length_take, List.Vector.toList_length]
  omega

/-- Prefix extension can only decrease the fixed-column row probability. -/
theorem prefixMass_antitone {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    {x y : Prefix k d} (hxy : x.2.toList <+: y.2.toList) :
    prefixMass cuts y ≤ prefixMass cuts x := by
  change RiffleLowerV2.prefixMass cuts y ≤ RiffleLowerV2.prefixMass cuts x
  rw [← RiffleLowerV2.Thinning.prefixColumnFraction_product cuts x,
    ← RiffleLowerV2.Thinning.prefixColumnFraction_product cuts y]
  apply Finset.prod_le_prod
  · intro j _
    exact (RiffleLowerV2.Thinning.prefixColumnFraction_bounds cuts hn y j).1
  · intro j _
    by_cases hj : j.val < x.1.val
    · have hjy : j.val < y.1.val := lt_of_lt_of_le hj (prefix_length_le hxy)
      have hd : x.2.get ⟨j.val,hj⟩ = y.2.get ⟨j.val,hjy⟩ := by
        simpa [List.Vector.get, List.Vector.toList] using hxy.getElem (by simpa using hj)
      simp [RiffleLowerV2.Thinning.prefixColumnFraction, hj, hjy, hd]
    · simpa [RiffleLowerV2.Thinning.prefixColumnFraction, hj] using
        (RiffleLowerV2.Thinning.prefixColumnFraction_bounds cuts hn y j).2

end RiffleUpperV2.Localization
