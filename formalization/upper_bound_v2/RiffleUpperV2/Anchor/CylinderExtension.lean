import RiffleUpperV2.Anchor.Scales
import RiffleUpperV2.Localization.CylinderAdapters

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Anchor
open TimeProfile Hypergeometric RiffleUpperV2.Localization

theorem cylinderSet_update_univ {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (D : Fin d → Finset (Fin k)) (j : Fin d)
    (Dj : Finset (Fin k)) (hj : D j = Finset.univ) (ω : Sample cuts) :
    cylinderSet cuts R (Function.update D j Dj) ω =
      (cylinderSet cuts R D ω).filter (fun r => sampleEntry ω r j ∈ Dj) := by
  apply Finset.ext
  intro r
  simp only [cylinderSet, RiffleLowerV2.Thinning.intersectionWithin,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hr,hh⟩
    refine ⟨⟨hr, ?_⟩, ?_⟩
    · intro t
      by_cases ht : t = j
      · subst t
        rw [hj]
        exact Finset.mem_univ _
      · simpa only [Function.update_of_ne ht] using hh t
    · simpa only [Function.update_self, sampleEntry] using hh j
  · rintro ⟨⟨hr,hh⟩,hj'⟩
    refine ⟨hr, fun t => ?_⟩
    by_cases ht : t = j
    · subst t
      simpa only [Function.update_self, sampleEntry] using hj'
    · simpa only [Function.update_of_ne ht] using hh t

theorem cylinderMass_update_univ {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (D : Fin d → Finset (Fin k)) (j : Fin d) (Dj : Finset (Fin k))
    (hj : D j = Finset.univ) :
    cylinderMass cuts (Function.update D j Dj) =
      cylinderMass cuts D * ((allowedCount cuts j Dj : ℝ) / n) := by
  let f : Fin d → ℝ := fun t => (allowedCount cuts t (D t) : ℝ) / n
  have hf : f j = 1 := by simp only [f, hj, allowedCount_univ]; exact div_self (by positivity)
  have hfun : (fun t => (allowedCount cuts t (Function.update D j Dj t) : ℝ) / n) =
      Function.update f j ((allowedCount cuts j Dj : ℝ) / n) := by
    funext t
    by_cases ht : t = j
    · subst t
      simp only [Function.update_self]
    · simp only [Function.update_of_ne ht, f]
  unfold cylinderMass
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ j)]
  have hprod := Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j)
  rw [hf, one_mul] at hprod
  rw [Finset.sdiff_singleton_eq_erase, hprod]
  exact mul_comm _ _

/-- A prefix cylinder stopped just before j, then an arbitrary allowed set at j. -/
def prefixThenDigits {k d : ℕ} (x : Prefix k d) (j : Fin x.1.val) (D : Finset (Fin k)) :=
  Function.update (prefixDigits (takePrefix x j.val j.isLt.le)) (prefixColumn x j) D

theorem prefixBefore_univ {k d : ℕ} (x : Prefix k d) (j : Fin x.1.val) :
    prefixDigits (takePrefix x j.val j.isLt.le) (prefixColumn x j) = Finset.univ := by
  simp [prefixDigits, takePrefix, prefixColumn]

theorem prefixThenDigits_mass {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (x : Prefix k d) (j : Fin x.1.val) (D : Finset (Fin k)) :
    cylinderMass cuts (prefixThenDigits x j D) =
      sidePrefixMass cuts x j * ((allowedCount cuts (prefixColumn x j) D : ℝ) / n) := by
  rw [prefixThenDigits, cylinderMass_update_univ cuts hn _ _ _ (prefixBefore_univ x j),
    prefixDigits_mass cuts hn, ← sidePrefixMass_eq]

def singleDigits {k d : ℕ} (j : Fin d) (D : Finset (Fin k)) :=
  Function.update (fun _ : Fin d => Finset.univ) j D

theorem singleDigits_mass {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (j : Fin d) (D : Finset (Fin k)) :
    cylinderMass cuts (singleDigits j D) = (allowedCount cuts j D : ℝ) / n := by
  rw [singleDigits, cylinderMass_update_univ cuts hn _ _ _ rfl]
  have hbase : cylinderMass cuts (fun _ : Fin d => Finset.univ) = 1 := by
    unfold cylinderMass
    simp only [allowedCount_univ, div_self (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0), Finset.prod_const_one]
  rw [hbase, one_mul]

theorem singleDigits_set {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (j : Fin d) (D : Finset (Fin k)) (ω : Sample cuts) :
    cylinderSet cuts R (singleDigits j D) ω = R.filter (fun r => sampleEntry ω r j ∈ D) := by
  rw [singleDigits, cylinderSet_update_univ cuts R _ j D rfl]
  have hbase : cylinderSet cuts R (fun _ : Fin d => Finset.univ) ω = R := by
    apply Finset.ext
    intro r
    simp [cylinderSet, RiffleLowerV2.Thinning.intersectionWithin]
  rw [hbase]

end RiffleUpperV2.Anchor
