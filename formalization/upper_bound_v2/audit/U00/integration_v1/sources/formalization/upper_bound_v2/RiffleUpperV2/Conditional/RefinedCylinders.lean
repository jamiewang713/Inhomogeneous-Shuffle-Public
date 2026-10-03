import RiffleUpperV2.Conditional.FutureCylinders
import RiffleUpperV2.Conditional.RefinementCount

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional

/-- Append an arbitrary finite block of new digits to a bounded prefix. -/
def extendPrefix {k K : ℕ} (x : Prefix k K) (m : ℕ) (hm : x.1.val+m ≤ K)
    (v : Word k m) : Prefix k K :=
  ⟨⟨x.1.val+m, by omega⟩, ⟨x.2.toList++v.toList, by simp⟩⟩

def refineCylinder {k K : ℕ} (x : Prefix k K) (m : ℕ) (hm : x.1.val+m ≤ K) :
    Finset (Prefix k K) := Finset.univ.image (extendPrefix x m hm)

def refineFamily {k K : ℕ} (B : Finset (Prefix k K)) (m : B → ℕ)
    (hm : ∀ x : B, x.val.1.val + m x ≤ K) : Finset (Prefix k K) :=
  B.attach.biUnion fun x => refineCylinder x.val (m x) (hm x)

theorem refineCylinder_card {k K : ℕ} (x : Prefix k K) (m : ℕ) (hm : x.1.val+m ≤ K) :
    (refineCylinder x m hm).card ≤ k^m := by
  apply Finset.card_image_le.trans
  rw [Finset.card_univ, Fintype.card_congr (Equiv.vectorEquivFin (Fin k) m)]
  simp

theorem refineFamily_card {k K b : ℕ} (hk : 1 ≤ k) (B : Finset (Prefix k K))
    (m : B → ℕ) (hm : ∀ x : B, x.val.1.val+m x ≤ K) (hb : ∀ x : B, m x ≤ b) :
    (refineFamily B m hm).card ≤ B.card*k^b := by
  calc
    _ ≤ ∑ x ∈ B.attach, (refineCylinder x.val (m x) (hm x)).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ B.attach, k^b := Finset.sum_le_sum fun x _ =>
      (refineCylinder_card x.val (m x) (hm x)).trans (Nat.pow_le_pow_right hk (hb x))
    _ = _ := by simp

/-- Actual refinement of a future-cylinder family discharges the finite
combinatorial input of refinementCount. -/
theorem refinedFuture_card {k K N : ℕ} {ρ T : ℝ} (hk : 1 ≤ k) (hN : 1 ≤ N)
    (hρ : 0 ≤ ρ) (hK : (K : ℝ) ≤ T*Real.log (N : ℝ)) (s t : Word k K)
    (m : futureCylinders s t → ℕ)
    (hm : ∀ x : futureCylinders s t, x.val.1.val+m x ≤ K)
    (hb : ∀ x : futureCylinders s t, m x ≤ Exploration.windowLength N ρ) :
    ((refineFamily (futureCylinders s t) m hm).card : ℝ) ≤
      (2*(k : ℝ)^3*T)*Real.log (N : ℝ)*(N : ℝ)^(ρ*Real.log (k : ℝ)) := by
  apply refinementCount hk hN hρ hK
  exact (refineFamily_card hk _ m hm hb).trans
    (Nat.mul_le_mul_right _ (futureCylinders_card s t))

theorem refineCylinder_extension {k K m : ℕ} (x : Prefix k K) (hm : x.1.val+m ≤ K)
    {y : Prefix k K} (hy : y ∈ refineCylinder x m hm) :
    y.1.val = x.1.val+m ∧ x.2.toList <+: y.2.toList := by
  obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hy
  exact ⟨rfl,List.prefix_append _ _⟩

/-- A parent cylinder is exactly partitioned by all its fixed-length extensions. -/
theorem refineCylinder_cover {k K m : ℕ} (x : Prefix k K) (hm : x.1.val+m ≤ K)
    (w : Word k K) :
    inCylinder x w ↔ ∃ y ∈ refineCylinder x m hm, inCylinder y w := by
  constructor
  · intro hx
    let v : Word k m := ⟨(w.toList.drop x.1.val).take m, by
      simp only [List.length_take,List.length_drop,List.Vector.toList_length]
      exact Nat.min_eq_left (by omega)⟩
    refine ⟨extendPrefix x m hm v,Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩,?_⟩
    have he : x.2.toList = w.toList.take x.1.val := by
      simpa only [List.Vector.toList_length] using List.prefix_iff_eq_take.mp hx
    change x.2.toList ++ (w.toList.drop x.1.val).take m <+: w.toList
    rw [he, ← List.take_add]
    exact List.take_prefix _ _
  · rintro ⟨y,hy,hyw⟩
    exact (refineCylinder_extension x hm hy).2.trans hyw

/-- Refining an antichain preserves the exact covered word set. -/
theorem refineFamily_cover {k K : ℕ} (B : Finset (Prefix k K)) (m : B → ℕ)
    (hm : ∀ x : B, x.val.1.val+m x ≤ K) (w : Word k K) :
    (∃ x ∈ B, inCylinder x w) ↔ ∃ y ∈ refineFamily B m hm, inCylinder y w := by
  constructor
  · rintro ⟨x,hx,hxw⟩
    obtain ⟨y,hy,hyw⟩ := (refineCylinder_cover x (hm ⟨x,hx⟩) w).mp hxw
    exact ⟨y,Finset.mem_biUnion.mpr ⟨⟨x,hx⟩,by simp,hy⟩,hyw⟩
  · rintro ⟨y,hy,hyw⟩
    obtain ⟨x,_,hxy⟩ := Finset.mem_biUnion.mp hy
    exact ⟨x.val,x.property,(refineCylinder_cover x.val (hm x) w).mpr ⟨y,hxy,hyw⟩⟩

/-- Bounded-length refinements preserve the structural prefix antichain. -/
theorem refineFamily_antichain {k K : ℕ} (B : Finset (Prefix k K)) (m : B → ℕ)
    (hm : ∀ x : B, x.val.1.val+m x ≤ K)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → ¬ (x.2.toList <+: y.2.toList))
    {a b : Prefix k K} (ha : a ∈ refineFamily B m hm) (hb : b ∈ refineFamily B m hm)
    (hab : a.2.toList <+: b.2.toList) : a = b := by
  obtain ⟨x,_,hxa⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨y,_,hyb⟩ := Finset.mem_biUnion.mp hb
  obtain ⟨hla,hpa⟩ := refineCylinder_extension x.val (hm x) hxa
  obtain ⟨hlb,hpb⟩ := refineCylinder_extension y.val (hm y) hyb
  have hxy : x = y := by
    apply Subtype.ext
    by_contra hne
    rcases List.prefix_or_prefix_of_prefix (hpa.trans hab) hpb with h | h
    · exact hB x.val x.property y.val y.property hne h
    · exact hB y.val y.property x.val x.property (Ne.symm hne) h
  subst y
  apply prefix_ext
  exact hab.eq_of_length (by simpa only [List.Vector.toList_length] using hla.trans hlb.symm)

end RiffleUpperV2.Conditional
