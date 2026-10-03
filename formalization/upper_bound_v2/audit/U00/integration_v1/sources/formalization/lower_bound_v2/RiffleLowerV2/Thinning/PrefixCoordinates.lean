import RiffleLowerV2.Thinning.PMFTools

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Thinning
open TimeProfile

/-- Prefix equality uses precisely the available coordinates, without a suffix. -/
theorem vector_take_eq_iff {k d K : ℕ} (hd : d ≤ K) (v : Word k K) (w : Word k d) :
    v.toList.take d = w.toList ↔ ∀ j : Fin d, v.get (Fin.castLE hd j) = w.get j := by
  constructor
  · intro h j
    have hj : j.val < (v.toList.take d).length := by simp [min_eq_left hd, j.isLt]
    have hj' : j.val < w.toList.length := by simp
    have he := (List.ext_getElem_iff.mp h).2 j.val hj hj'
    simpa [List.Vector.get, List.Vector.toList] using he
  · intro h
    apply List.ext_getElem (by simp [min_eq_left hd])
    intro j hj hj'
    have hsmall : j < d := by simpa using hj'
    simpa [List.Vector.get, List.Vector.toList] using h ⟨j, hsmall⟩

theorem prefix_coordinates_iff {k N K : ℕ} {cuts : Cuts k N K}
    (w : Prefix k K) (ω : Sample cuts) (i : Fin N) :
    (rowWord ω i).toList.take w.1.val = w.2.toList ↔
      ∀ j : Fin w.1.val, sampleEntry ω i (Fin.castLE (Nat.le_of_lt_succ w.1.isLt) j) = w.2.get j := by
  simpa only [rowWord_get] using vector_take_eq_iff (Nat.le_of_lt_succ w.1.isLt) (rowWord ω i) w.2

/-- Extending a product by neutral factors introduces no suffix multiplicity. -/
theorem prod_prefix_extension {d K : ℕ} (hd : d ≤ K) (f : Fin d → ℝ) :
    (∏ j : Fin K, if hj : j.val < d then f ⟨j.val,hj⟩ else 1) = ∏ j : Fin d, f j := by
  symm
  apply Finset.prod_bij_ne_one (fun (j : Fin d) _ _ => Fin.castLE hd j)
  · intros; exact Finset.mem_univ _
  · intro a _ _ b _ _ hab
    apply Fin.ext
    exact congrArg (fun j : Fin K => j.val) hab
  · intro b _ hb
    have hbd : b.val < d := by
      by_contra h
      simp [h] at hb
    refine ⟨⟨b.val,hbd⟩, Finset.mem_univ _, ?_, ?_⟩
    · simpa [hbd] using hb
    · rfl
  · intro a _ _
    simp [a.isLt]

def prefixColumnSet {k N K : ℕ} (cuts : Cuts k N K) (w : Prefix k K)
    (j : Fin K) (c : ColumnAssignments cuts j) : Finset (Fin N) :=
  if h : j.val < w.1.val then Finset.univ.filter (fun i => c.val i = w.2.get ⟨j.val,h⟩)
  else Finset.univ

def prefixColumnFraction {k N K : ℕ} (cuts : Cuts k N K) (w : Prefix k K) (j : Fin K) : ℝ :=
  if h : j.val < w.1.val then (cuts.count j (w.2.get ⟨j.val,h⟩) : ℝ)/N else 1

theorem prefixColumnFraction_product {k N K : ℕ} (cuts : Cuts k N K) (w : Prefix k K) :
    (∏ j, prefixColumnFraction cuts w j) = prefixMass cuts w := by
  exact prod_prefix_extension (Nat.le_of_lt_succ w.1.isLt)
    (fun j => (cuts.count (Fin.castLE (Nat.le_of_lt_succ w.1.isLt) j) (w.2.get j) : ℝ)/N)

theorem prefixColumnFraction_bounds {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (w : Prefix k K) (j : Fin K) :
    0 ≤ prefixColumnFraction cuts w j ∧ prefixColumnFraction cuts w j ≤ 1 := by
  unfold prefixColumnFraction
  split_ifs with h
  · have hc : cuts.count j (w.2.get ⟨j.val,h⟩) ≤ N := by
      calc
        _ ≤ ∑ a, cuts.count j a :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
        _ = N := cuts.sum_count j
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    constructor
    · positivity
    · apply (div_le_one hNr).2
      exact_mod_cast hc
  · norm_num

/-- A zero-mass prefix has zero count in every valid matrix, without a
probabilistic exception. -/
theorem prefixCount_eq_zero_of_mass_zero {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (w : Prefix k K) (hz : prefixMass cuts w = 0) (ω : Sample cuts) :
    prefixCount w ω = 0 := by
  by_contra hc
  have hp : 0 < prefixCount w ω := Nat.pos_of_ne_zero hc
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hp
  have he := (prefix_coordinates_iff w ω i).mp (Finset.mem_filter.mp hi).2
  have hm : 0 < prefixMass cuts w := by
    apply Finset.prod_pos
    intro j _
    have hd := sample_entry_count_pos ω i (Fin.castLE (Nat.le_of_lt_succ w.1.isLt) j)
    rw [he j] at hd
    apply div_pos
    · exact_mod_cast hd
    · exact_mod_cast hN
  linarith

end RiffleLowerV2.Thinning
