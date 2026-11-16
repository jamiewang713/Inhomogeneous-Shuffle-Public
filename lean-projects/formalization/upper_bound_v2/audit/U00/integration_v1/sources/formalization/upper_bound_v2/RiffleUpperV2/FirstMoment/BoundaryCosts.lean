import RiffleUpperV2.FirstMoment.Descriptors

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization
attribute [local instance] Classical.propDecidable

def largeDigits {k : ℕ} (p : Simplex k) (chi : ℝ) : Finset (Fin k) :=
  Finset.univ.filter fun b => chi ≤ prob p b

theorem largeDigits_nonempty {k : ℕ} (hk : 0 < k) (p : Simplex k) {chi : ℝ}
    (hchi : chi ≤ 1/(k : ℝ)) : (largeDigits p chi).Nonempty := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hsum : (∑ _ : Fin k, (1 : ℝ)/(k : ℝ)) ≤ ∑ l, prob p l := by
    simp [sum_prob, hkpos.ne']
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0,hk⟩, by simp⟩
  obtain ⟨l,hl,hp⟩ := Finset.exists_le_of_sum_le hne hsum
  exact ⟨l, Finset.mem_filter.mpr ⟨hl,hchi.trans hp⟩⟩

def leftDefault {k n d : ℕ} (hk : 0 < k) (cuts : Cuts k n d) (hn : 0 < n)
    (chi : ℝ) (hchi : chi ≤ 1/(k : ℝ)) : Fin d → Fin k :=
  fun j => (largeDigits (cuts.profile hn j) chi).min' (largeDigits_nonempty hk _ hchi)

def rightDefault {k n d : ℕ} (hk : 0 < k) (cuts : Cuts k n d) (hn : 0 < n)
    (chi : ℝ) (hchi : chi ≤ 1/(k : ℝ)) : Fin d → Fin k :=
  fun j => (largeDigits (cuts.profile hn j) chi).max' (largeDigits_nonempty hk _ hchi)

theorem leftDefault_large {k n d : ℕ} (hk : 0 < k) (cuts : Cuts k n d) (hn : 0 < n)
    (chi : ℝ) (hchi : chi ≤ 1/(k : ℝ)) (j : Fin d) :
    chi ≤ digitProbability cuts j (leftDefault hk cuts hn chi hchi j) := by
  exact (Finset.mem_filter.mp ((largeDigits (cuts.profile hn j) chi).min'_mem (largeDigits_nonempty hk _ hchi))).2

theorem rightDefault_large {k n d : ℕ} (hk : 0 < k) (cuts : Cuts k n d) (hn : 0 < n)
    (chi : ℝ) (hchi : chi ≤ 1/(k : ℝ)) (j : Fin d) :
    chi ≤ digitProbability cuts j (rightDefault hk cuts hn chi hchi j) := by
  exact (Finset.mem_filter.mp ((largeDigits (cuts.profile hn j) chi).max'_mem (largeDigits_nonempty hk _ hchi))).2

theorem below_leftDefault_rare {k n d : ℕ} (hk : 0 < k) (cuts : Cuts k n d) (hn : 0 < n)
    (chi : ℝ) (hchi : chi ≤ 1/(k : ℝ)) (j : Fin d) (b : Fin k)
    (hb : b < leftDefault hk cuts hn chi hchi j) : digitProbability cuts j b < chi := by
  by_contra h
  have hm : b ∈ largeDigits (cuts.profile hn j) chi := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt h⟩
  exact (not_lt_of_ge ((largeDigits _ _).min'_le b hm)) hb

theorem above_rightDefault_rare {k n d : ℕ} (hk : 0 < k) (cuts : Cuts k n d) (hn : 0 < n)
    (chi : ℝ) (hchi : chi ≤ 1/(k : ℝ)) (j : Fin d) (b : Fin k)
    (hb : rightDefault hk cuts hn chi hchi j < b) : digitProbability cuts j b < chi := by
  by_contra h
  have hm : b ∈ largeDigits (cuts.profile hn j) chi := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt h⟩
  exact (not_lt_of_ge ((largeDigits _ _).le_max' b hm)) hb

/-- Before its first left crossing a boundary digit cannot exceed l_j. -/
theorem leftBoundary_before_default {k n d : ℕ} (hk : 0 < k) (cuts : Cuts k n d)
    (hn : 0 < n) (chi : ℝ) (hchi : chi ≤ 1/(k : ℝ)) (R : Finset (Fin n))
    (y : Prefix k d) (hy : LeftBoundary cuts R chi y) (j : Fin d)
    (hj : j.val+1 < y.1.val) :
    completePrefix (leftDefault hk cuts hn chi hchi) y j ≤ leftDefault hk cuts hn chi hchi j := by
  let u := takePrefix y (j.val+1) (by omega)
  have hnott := hy.2.2.2 u List.nil_prefix (takePrefix_isPrefix _ _ _) hj
  by_contra h
  apply hnott
  have hjy : j.val < y.1.val := by omega
  have hgt : leftDefault hk cuts hn chi hchi j < y.2.get ⟨j.val,hjy⟩ := by
    simpa [completePrefix, hjy] using lt_of_not_ge h
  refine ⟨by dsimp [u]; omega, leftDefault hk cuts hn chi hchi j, ?_, ?_⟩
  · simpa [u, prefixColumn] using leftDefault_large hk cuts hn chi hchi j
  · simpa [u, takePrefix, RiffleShuffle.truncate, List.Vector.get,
      List.Vector.toList, Fin.cast] using hgt

/-- Before its first right crossing a boundary digit cannot precede r_j. -/
theorem rightBoundary_before_default {k n d : ℕ} (hk : 0 < k) (cuts : Cuts k n d)
    (hn : 0 < n) (chi : ℝ) (hchi : chi ≤ 1/(k : ℝ)) (R : Finset (Fin n))
    (y : Prefix k d) (hy : RightBoundary cuts R chi y) (j : Fin d)
    (hj : j.val+1 < y.1.val) :
    rightDefault hk cuts hn chi hchi j ≤ completePrefix (rightDefault hk cuts hn chi hchi) y j := by
  let u := takePrefix y (j.val+1) (by omega)
  have hnott := hy.2.2.2 u List.nil_prefix (takePrefix_isPrefix _ _ _) hj
  by_contra h
  apply hnott
  have hjy : j.val < y.1.val := by omega
  have hlt : y.2.get ⟨j.val,hjy⟩ < rightDefault hk cuts hn chi hchi j := by
    simpa [completePrefix, hjy] using lt_of_not_ge h
  refine ⟨by dsimp [u]; omega, rightDefault hk cuts hn chi hchi j, ?_, ?_⟩
  · simpa [u, prefixColumn] using rightDefault_large hk cuts hn chi hchi j
  · simpa [u, takePrefix, RiffleShuffle.truncate, List.Vector.get,
      List.Vector.toList, Fin.cast] using hlt

/-- Every encoded left boundary exception is a genuinely chi-rare selected digit. -/
theorem leftBoundary_exception_rare {k n d : ℕ} (hk : 0 < k) (cuts : Cuts k n d)
    (hn : 0 < n) (chi : ℝ) (hchi : chi ≤ 1/(k : ℝ)) (R : Finset (Fin n))
    (y : Prefix k d) (hy : LeftBoundary cuts R chi y) (j : Fin d)
    (hj : j ∈ boundaryExceptions (leftDefault hk cuts hn chi hchi) y) :
    digitProbability cuts j (completePrefix (leftDefault hk cuts hn chi hchi) y j) < chi := by
  obtain ⟨_,hjlen,hjne⟩ := Finset.mem_filter.mp hj
  exact below_leftDefault_rare hk cuts hn chi hchi j _
    (lt_of_le_of_ne (leftBoundary_before_default hk cuts hn chi hchi R y hy j hjlen) hjne)

/-- The symmetric right boundary exception estimate. -/
theorem rightBoundary_exception_rare {k n d : ℕ} (hk : 0 < k) (cuts : Cuts k n d)
    (hn : 0 < n) (chi : ℝ) (hchi : chi ≤ 1/(k : ℝ)) (R : Finset (Fin n))
    (y : Prefix k d) (hy : RightBoundary cuts R chi y) (j : Fin d)
    (hj : j ∈ boundaryExceptions (rightDefault hk cuts hn chi hchi) y) :
    digitProbability cuts j (completePrefix (rightDefault hk cuts hn chi hchi) y j) < chi := by
  obtain ⟨_,hjlen,hjne⟩ := Finset.mem_filter.mp hj
  exact above_rightDefault_rare hk cuts hn chi hchi j _
    (lt_of_le_of_ne (rightBoundary_before_default hk cuts hn chi hchi R y hy j hjlen) (Ne.symm hjne))

end RiffleUpperV2.FirstMoment
