import RiffleLowerV2.Shared.Adapters
import Contracts.v1.ModelThinning
import Contracts.v1.AdditionalFinite

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
set_option maxHeartbeats 1000000

namespace RiffleLowerV2.Model
open TimeProfile

theorem expect_uniform {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    expect (PMF.uniformOfFintype α) f = (∑ a, f a) / Fintype.card α := by
  simp only [expect, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ← Finset.mul_sum]
  ring

theorem map_equiv_apply {α β : Type*} [Fintype α]
    (P : PMF α) (e : α ≃ β) (b : β) : (P.map e) b = P (e.symm b) := by
  have he (a : α) : b = e a ↔ e.symm b = a := by
    constructor
    · intro h; simpa using congrArg e.symm h
    · intro h; simpa using congrArg e h
  simp only [PMF.map_apply, he]
  simp

theorem map_uniform_equiv {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  ext b
  rw [map_equiv_apply]
  simp [PMF.uniformOfFintype_apply, Fintype.card_congr e]

theorem uniform_expect_equiv {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (e : α ≃ β) (f : β → ℝ) :
    expect (PMF.uniformOfFintype α) (fun a => f (e a)) =
      expect (PMF.uniformOfFintype β) f := by
  rw [expect_uniform, expect_uniform, e.sum_comp, Fintype.card_congr e]

theorem expect_bind {α β : Type*} [Fintype α] [Fintype β]
    (P : PMF α) (Q : α → PMF β) (f : β → ℝ) :
    expect (P.bind Q) f = expect P (fun a => expect (Q a) f) := by
  unfold expect
  simp only [PMF.bind_apply, tsum_fintype]
  simp_rw [ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top (P.apply_ne_top a)
    ((Q a).apply_ne_top _)), ENNReal.toReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

theorem expect_map {α β : Type*} [Fintype α] [Fintype β]
    (P : PMF α) (g : α → β) (f : β → ℝ) :
    expect (P.map g) f = expect P (fun a => f (g a)) := by
  rw [PMF.map, expect_bind]
  congr 1
  funext a
  simp [expect, PMF.pure_apply, apply_ite]

theorem expect_const {α : Type*} [Fintype α] (P : PMF α) (c : ℝ) :
    expect P (fun _ => c) = c := by
  have hsum : (∑ a, (P a).toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun a _ => P.apply_ne_top a)]
    have h := P.tsum_coe
    rw [tsum_fintype] at h
    rw [h]
    simp
  simp only [expect, ← Finset.sum_mul, hsum, one_mul]

theorem expect_singleton {α : Type*} [Fintype α] (P : PMF α) (a : α) :
    expect P (fun b => if b = a then 1 else 0) = (P a).toReal := by
  simp [expect, mul_ite]

theorem uniform_pi_expect_prod {T : Type*} [Fintype T] {A : T → Type*}
    [∀ t, Fintype (A t)] [∀ t, Nonempty (A t)] (f : ∀ t, A t → ℝ) :
    expect (PMF.uniformOfFintype (∀ t, A t)) (fun ω => ∏ t, f t (ω t)) =
      ∏ t, expect (PMF.uniformOfFintype (A t)) (f t) := by
  simp_rw [expect_uniform]
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]
  simp [Fintype.card_pi, Nat.cast_prod]

theorem columnIndependence : Targets.ColumnIndependence := by
  intro k N K cuts f
  rw [fixed_expect_eq_average]
  simp_rw [columnPMF, expect_uniform]
  simp only [Sample, ShuffleSample]
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]
  simp [Fintype.card_pi, Nat.cast_prod]

theorem columnMarginal {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K) :
    (fixedCountPMF cuts).map (fun ω => ω j) = columnPMF cuts j := by
  ext a
  apply (ENNReal.toReal_eq_toReal_iff'
    (((fixedCountPMF cuts).map (fun ω => ω j)).apply_ne_top a)
    ((columnPMF cuts j).apply_ne_top a)).mp
  let f : ∀ t, ColumnAssignments cuts t → ℝ :=
    Function.update (fun _ _ => 1) j (fun b => if b = a then 1 else 0)
  have hprod (ω : Sample cuts) : (∏ t, f t (ω t)) = if ω j = a then 1 else 0 := by
    rw [Finset.prod_eq_single j]
    · simp [f]
    · intro t _ ht
      simp [f, Function.update_of_ne ht]
    · simp
  have hright : (∏ t, expect (columnPMF cuts t) (f t)) =
      expect (columnPMF cuts j) (fun b => if b = a then 1 else 0) := by
    rw [Finset.prod_eq_single j]
    · simp [f]
    · intro t _ ht
      simp only [f, Function.update_of_ne ht]
      exact expect_const _ 1
    · simp
  have h := columnIndependence cuts f
  simp_rw [hprod] at h
  rw [hright] at h
  rw [← expect_singleton, expect_map]
  exact h.trans (expect_singleton _ a)

def columnRelabel {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K)
    (σ : Permutation N) (a : ColumnAssignments cuts j) : ColumnAssignments cuts j :=
  ⟨fun i => a.val (σ i), by
    intro l
    have hcard : (Finset.univ.filter fun i => a.val (σ i) = l).card =
        (Finset.univ.filter fun i => a.val i = l).card := by
      apply Finset.card_bij (fun i _ => σ i)
      · intro i hi; simpa using hi
      · intro i hi m hm him; exact σ.injective him
      · intro i hi; exact ⟨σ.symm i, by simpa using hi, by simp⟩
    exact hcard.trans (a.property l)⟩

def columnEquiv {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K)
    (σ : Permutation N) : ColumnAssignments cuts j ≃ ColumnAssignments cuts j where
  toFun := columnRelabel cuts j σ
  invFun := columnRelabel cuts j σ.symm
  left_inv a := by apply Subtype.ext; funext i; simp [columnRelabel]
  right_inv a := by apply Subtype.ext; funext i; simp [columnRelabel]

@[simp] theorem columnEquiv_apply_val {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K)
    (σ : Permutation N) (a : ColumnAssignments cuts j) (i : Fin N) :
    (columnEquiv cuts j σ a).val i = a.val (σ i) := rfl

def sampleRelabel {k N K : ℕ} (cuts : Cuts k N K) (σ : Permutation N) :
    Sample cuts ≃ Sample cuts := Equiv.piCongrRight fun j => columnEquiv cuts j σ

@[simp] theorem sampleRelabel_apply {k N K : ℕ} (cuts : Cuts k N K)
    (σ : Permutation N) (ω : Sample cuts) (j : Fin K) :
    sampleRelabel cuts σ ω j = columnEquiv cuts j σ (ω j) := rfl

@[simp] theorem sampleRow_relabel {k N K : ℕ} (cuts : Cuts k N K)
    (σ : Permutation N) (ω : Sample cuts) (i : Fin N) :
    sampleRow (sampleRelabel cuts σ ω) i = sampleRow ω (σ i) := rfl

@[simp] theorem rowWord_relabel {k N K : ℕ} (cuts : Cuts k N K)
    (σ : Permutation N) (ω : Sample cuts) (i : Fin N) :
    rowWord (sampleRelabel cuts σ ω) i = rowWord ω (σ i) := rfl

theorem sampleRelabel_uniform {k N K : ℕ} (cuts : Cuts k N K) (σ : Permutation N) :
    (fixedCountPMF cuts).map (sampleRelabel cuts σ) = fixedCountPMF cuts :=
  map_uniform_equiv (sampleRelabel cuts σ)

theorem rowRelabeling : Targets.RowRelabeling := by
  intro k N K cuts σ
  have h := congrArg (fun P : PMF (Sample cuts) => P.map sampleRow)
    (sampleRelabel_uniform cuts σ)
  rw [PMF.map_comp] at h
  exact h

def inversionEquiv (N : ℕ) : Permutation N ≃ Permutation N where
  toFun := Equiv.symm
  invFun := Equiv.symm
  left_inv := Equiv.symm_symm
  right_inv := Equiv.symm_symm

theorem inversionTV : Targets.InversionTV := by
  intro N P
  have h (π : Permutation N) : (P.map Equiv.symm) π = P π.symm :=
    map_equiv_apply P (inversionEquiv N) π
  unfold tv
  simp only [h, uniformPermutation, PMF.uniformOfFintype_apply]
  congr 1
  exact (inversionEquiv N).sum_comp
    (fun π => |(P π).toReal - ((Fintype.card (Permutation N) : ENNReal)⁻¹).toReal|)

end RiffleLowerV2.Model
