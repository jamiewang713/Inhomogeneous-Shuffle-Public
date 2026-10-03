import RiffleUpperV2.Anchor.Definitions
import RiffleUpperV2.Localization.Prefixes

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.Anchor
open RiffleUpperV2.Localization

/-- A side's prefix mass is the ordinary mass before its selected column. -/
theorem sidePrefixMass_eq {k n d : ℕ} (cuts : Cuts k n d) (x : Prefix k d)
    (i : Fin x.1.val) :
    sidePrefixMass cuts x i = prefixMass cuts (takePrefix x i.val (Nat.le_of_lt i.isLt)) := by
  unfold sidePrefixMass RiffleUpperV2.prefixMass RiffleLowerV2.prefixMass
  apply Finset.prod_congr rfl
  intro j _
  simp [digitProbability, prefixColumn, takePrefix, RiffleShuffle.truncate,
    List.Vector.get, List.Vector.toList, Fin.cast]

theorem sidePrefixMass_nonneg {k n d : ℕ} (cuts : Cuts k n d) (x : Prefix k d)
    (i : Fin x.1.val) : 0 ≤ sidePrefixMass cuts x i := by
  unfold sidePrefixMass digitProbability
  exact Finset.prod_nonneg (fun j _ => by positivity)

theorem leftMean_nonneg {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (x : Prefix k d) (i : Fin x.1.val) : 0 ≤ leftMean cuts R x i := by
  unfold leftMean leftProbability
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sidePrefixMass_nonneg cuts x i))
    (by positivity)

theorem rightMean_nonneg {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (x : Prefix k d) (i : Fin x.1.val) : 0 ≤ rightMean cuts R x i := by
  unfold rightMean rightProbability
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sidePrefixMass_nonneg cuts x i))
    (by positivity)

theorem leftMean_le_scale {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (x : Prefix k d) (i : Fin x.1.val) : leftMean cuts R x i ≤ leftScale cuts R x := by
  classical
  unfold leftScale
  apply Finset.le_sup' id
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem rightMean_le_scale {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (x : Prefix k d) (i : Fin x.1.val) : rightMean cuts R x i ≤ rightScale cuts R x := by
  classical
  unfold rightScale
  apply Finset.le_sup' id
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

private theorem mass_le_sidePrefixMass {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (x : Prefix k d) (i : Fin x.1.val) :
    prefixMass cuts x ≤ sidePrefixMass cuts x i := by
  rw [sidePrefixMass_eq]
  exact prefixMass_antitone cuts hn (takePrefix_isPrefix x i.val (Nat.le_of_lt i.isLt))

/-- A genuine left crossing gives a positive left scale for every continuation,
including the join itself. -/
theorem left_crossing_scale {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) {χ : ℝ} (hχ : 0 ≤ χ) {y v : Prefix k d}
    (hyv : IsPrefix y v) (hy : LeftCrossing cuts χ y) :
    χ * anchoredMean cuts R v ≤ leftScale cuts R v := by
  obtain ⟨hy, hc⟩ := hy
  have hlen := prefix_length_le hyv
  let iy : Fin y.1.val := ⟨y.1.val-1, by omega⟩
  let iv : Fin v.1.val := ⟨y.1.val-1, by omega⟩
  have hd : y.2.get iy = v.2.get iv := by
    simpa [List.Vector.get, List.Vector.toList] using hyv.getElem (by simpa using iy.isLt)
  have hcol : prefixColumn y iy = prefixColumn v iv := by apply Fin.ext; rfl
  have hc' : χ ≤ leftProbability cuts (prefixColumn v iv) (v.2.get iv) := by
    change χ ≤ leftProbability cuts (prefixColumn y iy) (y.2.get iy) at hc
    simpa only [hcol, hd] using hc
  have hm := mass_le_sidePrefixMass cuts hn v iv
  calc
    χ * anchoredMean cuts R v ≤ χ * (R.card * sidePrefixMass cuts v iv) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)) hχ
    _ ≤ leftMean cuts R v iv := by
      unfold leftMean
      rw [mul_comm χ]
      exact mul_le_mul_of_nonneg_left hc'
        (mul_nonneg (Nat.cast_nonneg _) (sidePrefixMass_nonneg cuts v iv))
    _ ≤ leftScale cuts R v := leftMean_le_scale cuts R v iv

theorem right_crossing_scale {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) {χ : ℝ} (hχ : 0 ≤ χ) {z v : Prefix k d}
    (hzv : IsPrefix z v) (hz : RightCrossing cuts χ z) :
    χ * anchoredMean cuts R v ≤ rightScale cuts R v := by
  obtain ⟨hz, hc⟩ := hz
  have hlen := prefix_length_le hzv
  let iz : Fin z.1.val := ⟨z.1.val-1, by omega⟩
  let iv : Fin v.1.val := ⟨z.1.val-1, by omega⟩
  have hd : z.2.get iz = v.2.get iv := by
    simpa [List.Vector.get, List.Vector.toList] using hzv.getElem (by simpa using iz.isLt)
  have hcol : prefixColumn z iz = prefixColumn v iv := by apply Fin.ext; rfl
  have hc' : χ ≤ rightProbability cuts (prefixColumn v iv) (v.2.get iv) := by
    change χ ≤ rightProbability cuts (prefixColumn z iz) (z.2.get iz) at hc
    simpa only [hcol, hd] using hc
  have hm := mass_le_sidePrefixMass cuts hn v iv
  calc
    χ * anchoredMean cuts R v ≤ χ * (R.card * sidePrefixMass cuts v iv) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)) hχ
    _ ≤ rightMean cuts R v iv := by
      unfold rightMean
      rw [mul_comm χ]
      exact mul_le_mul_of_nonneg_left hc'
        (mul_nonneg (Nat.cast_nonneg _) (sidePrefixMass_nonneg cuts v iv))
    _ ≤ rightScale cuts R v := rightMean_le_scale cuts R v iv

/-- Source eq:ub-anchor-side-comparison, first half, with no size threshold. -/
theorem genuine_sideScale_pos {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) {χ : ℝ} {y z v : Prefix k d}
    (h : GenuineBoundaryPair cuts R χ y z v) :
    0 < χ * anchoredMean cuts R v ∧ χ * anchoredMean cuts R v ≤ sideScale cuts R v := by
  refine ⟨mul_pos h.chi_pos h.legal_join, le_min ?_ ?_⟩
  · exact left_crossing_scale cuts hn R h.chi_pos.le h.left_prefix h.left_crossing
  · exact right_crossing_scale cuts hn R h.chi_pos.le h.right_prefix h.right_crossing

end RiffleUpperV2.Anchor
