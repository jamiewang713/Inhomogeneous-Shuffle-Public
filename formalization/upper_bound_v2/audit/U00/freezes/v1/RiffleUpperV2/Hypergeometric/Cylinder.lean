import RiffleLowerV2.Thinning.ColumnSampling
import RiffleLowerV2.Thinning.Recursion
import RiffleLowerV2.Thinning.Tails

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
namespace RiffleUpperV2.Hypergeometric
open TimeProfile RiffleLowerV2 RiffleLowerV2.Thinning

/-- Number of rows whose digit lies in the prescribed set. -/
def allowedCount {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d) (D : Finset (Fin k)) : ℕ :=
  ∑ a ∈ D, cuts.count j a

@[simp] theorem allowedCount_univ {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d) :
    allowedCount cuts j Finset.univ = n := by
  simpa [allowedCount] using cuts.sum_count j

@[simp] theorem allowedCount_empty {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d) :
    allowedCount cuts j ∅ = 0 := by simp [allowedCount]

theorem allowedCount_le {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d)
    (D : Finset (Fin k)) : allowedCount cuts j D ≤ n := by
  unfold allowedCount
  calc
    _ ≤ ∑ a, cuts.count j a := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ = n := cuts.sum_count j

theorem allowed_card {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (D : Finset (Fin k)) (c : ColumnAssignments cuts j) :
    (Finset.univ.filter (fun i => c.val i ∈ D)).card = allowedCount cuts j D := by
  rw [← Finset.sum_card_fiberwise_eq_card_filter]
  exact Finset.sum_congr rfl (fun a _ => c.property a)

def allowedSubset {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (D : Finset (Fin k)) (c : ColumnAssignments cuts j) :
    Compat.Sample (Finset.univ : Finset (Fin n)) (allowedCount cuts j D) :=
  ⟨Finset.univ.filter (fun i => c.val i ∈ D),
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, allowed_card D c⟩⟩

theorem allowedSubset_relabel {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (σ : Permutation n) (D : Finset (Fin k)) (c : ColumnAssignments cuts j) :
    (allowedSubset D (columnRelabel σ c)).val =
      (allowedSubset D c).val.map σ.toEmbedding := by
  ext i
  change i ∈ (Finset.univ.filter (fun i => c.val (σ.symm i) ∈ D)) ↔
    i ∈ (Finset.univ.filter (fun i => c.val i ∈ D)).map σ.toEmbedding
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Equiv.toEmbedding_apply]
  constructor
  · intro hi
    exact ⟨σ.symm i, hi, σ.apply_symm_apply i⟩
  · rintro ⟨v, hv, rfl⟩
    simpa using hv

/-- Every allowed digit union is an actual uniform subset of the full population. -/
theorem allowed_subset_expect {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d)
    (D : Finset (Fin k))
    (f : Compat.Sample (Finset.univ : Finset (Fin n)) (allowedCount cuts j D) → ℝ) :
    expect (columnPMF cuts j) (fun c => f (allowedSubset D c)) =
      (Compat.sampleLaw (Finset.univ : Finset (Fin n)) (allowedCount cuts j D)
        (by simpa using allowedCount_le cuts j D)).expect f := by
  let c0 : ColumnAssignments cuts j := Classical.choice inferInstance
  letI : Nonempty (Compat.Sample (Finset.univ : Finset (Fin n)) (allowedCount cuts j D)) :=
    ⟨allowedSubset D c0⟩
  change expect (PMF.uniformOfFintype (ColumnAssignments cuts j))
      (fun c => f (allowedSubset D c)) = (Compat.FiniteLaw.uniform _).expect f
  have hf : ∀ b c : Compat.Sample (Finset.univ : Finset (Fin n)) (allowedCount cuts j D),
      Fintype.card {v : ColumnAssignments cuts j // allowedSubset D v = b} =
        Fintype.card {v : ColumnAssignments cuts j // allowedSubset D v = c} := by
    intro b c
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq b.val c.val
      ((Finset.mem_powersetCard.mp b.property).2.trans
        (Finset.mem_powersetCard.mp c.property).2.symm)
    apply Fintype.card_congr ((columnRelabelEquiv (cuts := cuts) (j := j) σ).subtypeEquiv
      (fun v => ?_))
    change allowedSubset D v = b ↔ allowedSubset D (columnRelabel σ v) = c
    simp only [Subtype.ext_iff]
    rw [allowedSubset_relabel, ← hσ]
    exact Finset.map_inj.symm
  have he := uniform_expect_of_equal_fibres (allowedSubset (cuts := cuts) (j := j) D) (g := f)
  rw [he (by intro b c; simpa only [Fintype.card_eq_nat_card] using hf b c), uniform_expect]
  simp only [Compat.FiniteLaw.expect, Compat.FiniteLaw.uniform, ← Finset.mul_sum]
  ring

theorem allowed_intersection_transform {k n d : ℕ} (cuts : Cuts k n d)
    (j : Fin d) (D : Finset (Fin k)) (A : Finset (Fin n)) {s : ℝ} (hs : 0 < s) :
    expect (columnPMF cuts j)
      (fun c => s ^ (A ∩ (Finset.univ.filter (fun i => c.val i ∈ D))).card) ≤
      (1 - (allowedCount cuts j D : ℝ) / n +
        (allowedCount cuts j D : ℝ) / n * s) ^ A.card := by
  have he := allowed_subset_expect cuts j D (fun S => s ^ (A ∩ S.val).card)
  change expect (columnPMF cuts j)
    (fun c => s ^ (A ∩ (Finset.univ.filter (fun i => c.val i ∈ D))).card) = _ at he
  rw [he]
  simpa using Compat.sample_expect_pow_intersection_le Finset.univ A
    (allowedCount cuts j D) (by simpa using allowedCount_le cuts j D)
    (Finset.subset_univ _) hs

/-- Arbitrary digit sets; unselected columns are assigned the full digit set. -/
def cylinderSet {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (D : Fin d → Finset (Fin k)) (ω : Sample cuts) : Finset (Fin n) :=
  intersectionWithin R (fun j c => Finset.univ.filter (fun i => c.val i ∈ D j)) ω

def cylinderCount {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (D : Fin d → Finset (Fin k)) (ω : Sample cuts) : ℕ := (cylinderSet cuts R D ω).card

def cylinderMass {k n d : ℕ} (cuts : Cuts k n d) (D : Fin d → Finset (Fin k)) : ℝ :=
  ∏ j, (allowedCount cuts j (D j) : ℝ) / n

def cylinderMean {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (D : Fin d → Finset (Fin k)) : ℝ := R.card * cylinderMass cuts D

theorem cylinderMass_bounds {k n d : ℕ} (cuts : Cuts k n d) (D : Fin d → Finset (Fin k)) :
    0 ≤ cylinderMass cuts D ∧ cylinderMass cuts D ≤ 1 := by
  have hq (j : Fin d) : 0 ≤ (allowedCount cuts j (D j) : ℝ) / n ∧
      (allowedCount cuts j (D j) : ℝ) / n ≤ 1 :=
    ⟨by positivity, div_le_one_of_le₀ (by exact_mod_cast allowedCount_le cuts j (D j))
      (by positivity)⟩
  exact ⟨Finset.prod_nonneg (fun j _ => (hq j).1),
    Finset.prod_le_one (fun j _ => (hq j).1) (fun j _ => (hq j).2)⟩

/-- The full-population fixed-column cylinder transform, with no outside reserve. -/
theorem anchorCylinderTransform {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (D : Fin d → Finset (Fin k)) (s : ℝ) (hs : 0 < s) :
    expect (fixedCountPMF cuts) (fun ω => s ^ cylinderCount cuts R D ω) ≤
      (1 - cylinderMass cuts D + cylinderMass cuts D * s) ^ R.card ∧
    (1 - cylinderMass cuts D + cylinderMass cuts D * s) ^ R.card ≤
      Real.exp (cylinderMean cuts R D * (s - 1)) := by
  have hq (j : Fin d) : 0 ≤ (allowedCount cuts j (D j) : ℝ) / n ∧
      (allowedCount cuts j (D j) : ℝ) / n ≤ 1 :=
    ⟨by positivity, div_le_one_of_le₀ (by exact_mod_cast allowedCount_le cuts j (D j))
      (by positivity)⟩
  have h := independent_intersection_transform n d (ColumnAssignments cuts)
    (fun j c => Finset.univ.filter (fun i => c.val i ∈ D j))
    (fun j => (allowedCount cuts j (D j) : ℝ) / n) hq
    (fun j A s hs => allowed_intersection_transform cuts j (D j) A hs) R s hs
  exact ⟨h, binomial_le_exp (cylinderMass_bounds cuts D).1 (cylinderMass_bounds cuts D).2 hs⟩

theorem anchorCylinderTail {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (D : Fin d → Finset (Fin k)) {t : ℝ} (ht : 0 < t) :
    probability (fixedCountPMF cuts)
      (fun ω => t ≤ |(cylinderCount cuts R D ω : ℝ) - cylinderMean cuts R D|) ≤
      2 * Real.exp (-t^2 / (4 * (cylinderMean cuts R D + t))) ∧
    probability (fixedCountPMF cuts)
      (fun ω => (cylinderCount cuts R D ω : ℝ) ≤ cylinderMean cuts R D / 2) ≤
      Real.exp (-chernoffConstant * cylinderMean cuts R D) := by
  have htr : ∀ s : ℝ, 0 < s →
      expect (fixedCountPMF cuts) (fun ω => s ^ cylinderCount cuts R D ω) ≤
        Real.exp (cylinderMean cuts R D * (s - 1)) := fun s hs =>
    (anchorCylinderTransform cuts R D s hs).1.trans (anchorCylinderTransform cuts R D s hs).2
  exact ⟨bernstein_of_transform _ _ _
    (mul_nonneg (Nat.cast_nonneg _) (cylinderMass_bounds cuts D).1) htr ht,
    half_mean_of_transform _ _ _ htr⟩

end RiffleUpperV2.Hypergeometric
