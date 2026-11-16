import RiffleUpperV2.Reservoir.InteriorCounts

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open TimeProfile Exploration
attribute [local instance 2000] wordDecEq

def prefixSeparated {k d : ℕ} (x y : Prefix k d) : Prop :=
  ¬x.2.toList <+: y.2.toList ∧ ¬y.2.toList <+: x.2.toList

theorem prefixSeparated_not_both {k d : ℕ} (x y : Prefix k d) (h : prefixSeparated x y)
    (w : Word k d) (hx : w.toList.take x.1.val=x.2.toList)
    (hy : w.toList.take y.1.val=y.2.toList) : False := by
  have hxp : x.2.toList <+: w.toList := by rw [← hx]; exact List.take_prefix _ _
  have hyp : y.2.toList <+: w.toList := by rw [← hy]; exact List.take_prefix _ _
  exact (List.prefix_or_prefix_of_prefix hxp hyp).elim h.1 h.2

theorem list_lt_iff_of_equal_take {k : ℕ} (m : ℕ) (a b c : List (Fin k))
    (hab : a.take m=b.take m) (hne : a.take m≠c.take m) : (a<c ↔ b<c) := by
  have hf (u v : List (Fin k)) (huv : u.take m=v.take m) (hne : u.take m≠c.take m)
      (huc : u<c) : v<c := by
    have ht : u.take m<c.take m := lt_of_le_of_ne (RiffleShuffle.take_lex_monotone m huc.le) hne
    by_contra hvc
    have hv := RiffleShuffle.take_lex_monotone m (le_of_not_gt hvc)
    rw [← huv] at hv
    exact not_lt_of_ge hv ht
  exact ⟨hf a b hab hne, hf b a hab.symm (by rwa [← hab])⟩

/-- Relative order with a disjoint prefix cylinder is constant throughout
the entire selected cylinder, even when the prefix lengths differ. -/
theorem separated_prefix_comparison {k d : ℕ} (x y : Prefix k d) (hsep : prefixSeparated x y)
    (w z : Word k d) (hw : w.toList.take x.1.val=x.2.toList) (hz : z.toList.take x.1.val=x.2.toList) :
    ((w.toList.take y.1.val<y.2.toList) ↔ (z.toList.take y.1.val<y.2.toList)) ∧
    ((w.toList.take y.1.val≤y.2.toList) ↔ (z.toList.take y.1.val≤y.2.toList)) ∧
    ((w.toList.take y.1.val=y.2.toList) ↔ (z.toList.take y.1.val=y.2.toList)) := by
  by_cases hyx : y.1.val≤x.1.val
  · have he := congrArg (List.take y.1.val) (hw.trans hz.symm)
    simp only [List.take_take,Nat.min_eq_left hyx] at he
    rw [he]
    exact ⟨Iff.rfl,Iff.rfl,Iff.rfl⟩
  · have hxy : x.1.val≤y.1.val := by omega
    have hne : x.2.toList≠y.2.toList.take x.1.val := by
      intro he
      apply hsep.1
      rw [he]
      exact List.take_prefix _ _
    have hew : (w.toList.take y.1.val).take x.1.val=x.2.toList := by
      simpa only [List.take_take,Nat.min_eq_left hxy] using hw
    have hez : (z.toList.take y.1.val).take x.1.val=x.2.toList := by
      simpa only [List.take_take,Nat.min_eq_left hxy] using hz
    have hlt := list_lt_iff_of_equal_take x.1.val (w.toList.take y.1.val) (z.toList.take y.1.val) y.2.toList
      (hew.trans hez.symm) (by rwa [hew])
    have hwne : w.toList.take y.1.val≠y.2.toList := fun hy => prefixSeparated_not_both x y hsep w hw hy
    have hzne : z.toList.take y.1.val≠y.2.toList := fun hy => prefixSeparated_not_both x y hsep z hz hy
    refine ⟨hlt,?_,iff_of_false hwne hzne⟩
    simpa only [le_iff_lt_or_eq,hwne,hzne,or_false] using hlt

end RiffleUpperV2.Reservoir
