import Contracts.v1.ModelThinning
import RiffleLowerV2.Shared.Adapters
import RiffleLowerV2.Thinning.PMFTools

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RiffleLowerV2.Thinning
open TimeProfile

private abbrev unusedRows {N k K b : ℕ} (r : RowPrescription N k K b) :=
  {i : Fin N // ¬ ∃ q, r.row q = i}

private theorem unusedRows_card {N k K b : ℕ} (r : RowPrescription N k K b)
    (hr : Function.Injective r.row) : Fintype.card (unusedRows r) = N-b := by
  change Fintype.card {i : Fin N // ¬ ∃ q, r.row q = i} = N-b
  rw [Fintype.card_subtype_compl]
  have h := Fintype.card_congr
    (show Fin b ≃ {i : Fin N // ∃ q, r.row q = i} from Equiv.ofInjective r.row hr)
  simpa only [Fintype.card_fin] using congrArg (fun n => N-n) h.symm

private def unusedEnumeration {N k K b : ℕ} (r : RowPrescription N k K b)
    (hr : Function.Injective r.row) : Fin (N-b) ≃ unusedRows r :=
  (Fintype.equivFinOfCardEq (unusedRows_card r hr)).symm

private def rowSplit {N k K b : ℕ} (r : RowPrescription N k K b)
    (hr : Function.Injective r.row) (e : Fin (N-b) → Fin N)
    (he : Function.Injective e)
    (hc : ∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i) :
    Fin b ⊕ Fin (N-b) ≃ Fin N :=
  Equiv.ofBijective (Sum.elim r.row e) (by
    constructor
    · intro x y h
      cases x with
      | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (hr h)
        | inr y => exact False.elim ((hc (e y)).mp ⟨y, rfl⟩ ⟨x, h⟩)
      | inr x =>
        cases y with
        | inl y => exact False.elim ((hc (e x)).mp ⟨x, rfl⟩ ⟨y, h.symm⟩)
        | inr y => exact congrArg Sum.inr (he h)
    · intro i
      by_cases hi : ∃ q, r.row q = i
      · obtain ⟨q, hq⟩ := hi
        exact ⟨Sum.inl q, hq⟩
      · obtain ⟨q, hq⟩ := (hc i).mpr hi
        exact ⟨Sum.inr q, hq⟩)

private theorem count_split {N k K b : ℕ} (r : RowPrescription N k K b)
    (hr : Function.Injective r.row) (e : Fin (N-b) → Fin N)
    (he : Function.Injective e)
    (hc : ∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i)
    (a : Fin N → Fin k) (l : Fin k) :
    (Finset.univ.filter fun i => a i = l).card =
      (Finset.univ.filter fun q => a (r.row q) = l).card +
      (Finset.univ.filter fun q => a (e q) = l).card := by
  have h := (rowSplit r hr e he hc).sum_comp (fun i => if a i = l then (1 : ℕ) else 0)
  rw [Fintype.sum_sum_type] at h
  change (∑ q, if a (r.row q) = l then (1 : ℕ) else 0) +
    (∑ q, if a (e q) = l then (1 : ℕ) else 0) =
    (∑ i, if a i = l then (1 : ℕ) else 0) at h
  simpa only [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one] using h.symm

private theorem count_sum {n k : ℕ} (a : Fin n → Fin k) :
    ∑ l, (Finset.univ.filter fun i => a i = l).card = n := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

private theorem prescription_entry {N k K b : ℕ} {cuts : Cuts k N K}
    (r : RowPrescription N k K b) (ω : Sample cuts) (hω : prescriptionEvent r ω)
    (q : Fin b) (j : Fin K) : sampleEntry ω (r.row q) j = (r.word q).get j := by
  have h := congrArg (fun w : Word k K => w.get j) (hω q)
  simpa only [rowWord_get] using h

private theorem residual_count_eq {N k K b : ℕ} {cuts : Cuts k N K}
    (r : RowPrescription N k K b) (hr : Function.Injective r.row)
    (e : Fin (N-b) → Fin N) (he : Function.Injective e)
    (hc : ∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i)
    (ω : Sample cuts) (hω : prescriptionEvent r ω) (j : Fin K) (a : Fin k) :
    (Finset.univ.filter fun q => sampleEntry ω (e q) j = a).card =
      cuts.count j a - usedCount r j a := by
  have h := count_split r hr e he hc (fun i => sampleEntry ω i j) a
  have horig : (Finset.univ.filter fun i => sampleEntry ω i j = a).card =
      cuts.count j a := (ω j).property a
  have hused : (Finset.univ.filter fun q => sampleEntry ω (r.row q) j = a).card =
      usedCount r j a := by
    simp only [prescription_entry r ω hω, usedCount]
  rw [horig, hused] at h
  omega

private theorem prescription_exists {N k K b : ℕ} {cuts : Cuts k N K}
    (r : RowPrescription N k K b)
    (hp : 0 < probability (fixedCountPMF cuts) (prescriptionEvent r)) :
    ∃ ω : Sample cuts, prescriptionEvent r ω := by
  by_contra h
  push Not at h
  simp only [probability, expect, h, if_false, mul_zero, Finset.sum_const_zero] at hp
  exact (lt_irrefl 0) hp

private theorem residual_cuts_exists {N k K b : ℕ} (cuts : Cuts k N K)
    (r : RowPrescription N k K b) (hr : Function.Injective r.row)
    (hp : 0 < probability (fixedCountPMF cuts) (prescriptionEvent r)) :
    ∃ residual : Cuts k (N-b) K,
      ∀ j a, residual.count j a = cuts.count j a - usedCount r j a := by
  obtain ⟨ω, hω⟩ := prescription_exists r hp
  let u := unusedEnumeration r hr
  let e : Fin (N-b) → Fin N := fun q => (u q).val
  have he : Function.Injective e := Subtype.coe_injective.comp u.injective
  have hc : ∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i := by
    intro i
    constructor
    · rintro ⟨q, rfl⟩
      exact (u q).property
    · intro hi
      obtain ⟨q, hq⟩ := u.surjective ⟨i, hi⟩
      exact ⟨q, congrArg Subtype.val hq⟩
  refine ⟨⟨(fun j a => cuts.count j a - usedCount r j a), ?_⟩, fun _ _ => rfl⟩
  intro j
  simp_rw [← residual_count_eq r hr e he hc ω hω j]
  exact count_sum (fun q => sampleEntry ω (e q) j)

private theorem residual_balance {N k K b : ℕ} {cuts : Cuts k N K}
    (r : RowPrescription N k K b) (hr : Function.Injective r.row)
    (e : Fin (N-b) → Fin N) (he : Function.Injective e)
    (hc : ∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i)
    (ω : Sample cuts) (hω : prescriptionEvent r ω)
    (residual : Cuts k (N-b) K)
    (hres : ∀ j a, residual.count j a = cuts.count j a - usedCount r j a)
    (j : Fin K) (a : Fin k) :
    usedCount r j a + residual.count j a = cuts.count j a := by
  have h := count_split r hr e he hc (fun i => sampleEntry ω i j) a
  have horig : (Finset.univ.filter fun i => sampleEntry ω i j = a).card =
      cuts.count j a := (ω j).property a
  have hused : (Finset.univ.filter fun q => sampleEntry ω (r.row q) j = a).card =
      usedCount r j a := by simp only [prescription_entry r ω hω, usedCount]
  rw [horig, hused, residual_count_eq r hr e he hc ω hω, ← hres] at h
  exact h.symm

@[simp] private theorem rowSplit_symm_left {N k K b : ℕ}
    (r : RowPrescription N k K b) (hr : Function.Injective r.row)
    (e : Fin (N-b) → Fin N) (he : Function.Injective e)
    (hc : ∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i) (q : Fin b) :
    (rowSplit r hr e he hc).symm (r.row q) = Sum.inl q :=
  (rowSplit r hr e he hc).symm_apply_apply (Sum.inl q)

@[simp] private theorem rowSplit_symm_right {N k K b : ℕ}
    (r : RowPrescription N k K b) (hr : Function.Injective r.row)
    (e : Fin (N-b) → Fin N) (he : Function.Injective e)
    (hc : ∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i) (q : Fin (N-b)) :
    (rowSplit r hr e he hc).symm (e q) = Sum.inr q :=
  (rowSplit r hr e he hc).symm_apply_apply (Sum.inr q)

private def restrictSample {N k K b : ℕ} {cuts : Cuts k N K}
    (r : RowPrescription N k K b) (hr : Function.Injective r.row)
    (e : Fin (N-b) → Fin N) (he : Function.Injective e)
    (hc : ∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i)
    (residual : Cuts k (N-b) K)
    (hres : ∀ j a, residual.count j a = cuts.count j a - usedCount r j a)
    (ω : {ω : Sample cuts // prescriptionEvent r ω}) : Sample residual := fun j =>
  ⟨(fun q => sampleEntry ω.val (e q) j), by
    intro a
    rw [hres]
    exact residual_count_eq r hr e he hc ω.val ω.property j a⟩

private def rawGlue {N k K b : ℕ} (r : RowPrescription N k K b)
    (hr : Function.Injective r.row) (e : Fin (N-b) → Fin N)
    (he : Function.Injective e)
    (hc : ∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i)
    (rows : Fin (N-b) → Fin K → Fin k) (i : Fin N) (j : Fin K) : Fin k :=
  Sum.elim (fun q => (r.word q).get j) (fun q => rows q j)
    ((rowSplit r hr e he hc).symm i)

@[simp] private theorem rawGlue_left {N k K b : ℕ} (r : RowPrescription N k K b)
    (hr : Function.Injective r.row) (e : Fin (N-b) → Fin N)
    (he : Function.Injective e)
    (hc : ∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i)
    (rows : Fin (N-b) → Fin K → Fin k) (q : Fin b) (j : Fin K) :
    rawGlue r hr e he hc rows (r.row q) j = (r.word q).get j := by
  simp only [rawGlue, rowSplit_symm_left, Sum.elim_inl]

@[simp] private theorem rawGlue_right {N k K b : ℕ} (r : RowPrescription N k K b)
    (hr : Function.Injective r.row) (e : Fin (N-b) → Fin N)
    (he : Function.Injective e)
    (hc : ∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i)
    (rows : Fin (N-b) → Fin K → Fin k) (q : Fin (N-b)) (j : Fin K) :
    rawGlue r hr e he hc rows (e q) j = rows q j := by
  simp only [rawGlue, rowSplit_symm_right, Sum.elim_inr]

private def glueSample {N k K b : ℕ} {cuts : Cuts k N K}
    (r : RowPrescription N k K b) (hr : Function.Injective r.row)
    (e : Fin (N-b) → Fin N) (he : Function.Injective e)
    (hc : ∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i)
    (residual : Cuts k (N-b) K)
    (hbal : ∀ j a, usedCount r j a + residual.count j a = cuts.count j a)
    (η : Sample residual) : Sample cuts := fun j =>
  ⟨(fun i => rawGlue r hr e he hc (sampleRow η) i j), by
    intro a
    rw [count_split r hr e he hc]
    simp only [rawGlue_left, rawGlue_right]
    change usedCount r j a +
      (Finset.univ.filter fun q => (η j).val q = a).card = cuts.count j a
    rw [(η j).property a]
    exact hbal j a⟩

private def residualSampleEquiv {N k K b : ℕ} {cuts : Cuts k N K}
    (r : RowPrescription N k K b) (hr : Function.Injective r.row)
    (e : Fin (N-b) → Fin N) (he : Function.Injective e)
    (hc : ∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i)
    (residual : Cuts k (N-b) K)
    (hres : ∀ j a, residual.count j a = cuts.count j a - usedCount r j a)
    (hbal : ∀ j a, usedCount r j a + residual.count j a = cuts.count j a) :
    {ω : Sample cuts // prescriptionEvent r ω} ≃ Sample residual where
  toFun := restrictSample r hr e he hc residual hres
  invFun := fun η => ⟨glueSample r hr e he hc residual hbal η, by
    intro q
    apply List.Vector.ext
    intro j
    rw [rowWord_get]
    exact rawGlue_left r hr e he hc (sampleRow η) q j⟩
  left_inv := by
    intro ω
    apply Subtype.ext
    funext j
    apply Subtype.ext
    funext i
    by_cases hi : ∃ q, r.row q = i
    · obtain ⟨q, rfl⟩ := hi
      change rawGlue r hr e he hc _ (r.row q) j = _
      rw [rawGlue_left]
      exact (prescription_entry r ω.val ω.property q j).symm
    · obtain ⟨q, rfl⟩ := (hc i).mpr hi
      change rawGlue r hr e he hc _ (e q) j = _
      rw [rawGlue_right]
      rfl
  right_inv := by
    intro η
    funext j
    apply Subtype.ext
    funext q
    change rawGlue r hr e he hc (sampleRow η) (e q) j = (η j).val q
    rw [rawGlue_right]
    rfl

private theorem uniform_conditional_expect_equiv {Ω Γ : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype Γ] [Nonempty Γ]
    (B : Ω → Prop) (e : {ω // B ω} ≃ Γ) (f : Ω → ℝ) (g : Γ → ℝ)
    (hfg : ∀ ω : {ω // B ω}, f ω.val = g (e ω)) :
    conditionalExpect (PMF.uniformOfFintype Ω) f B =
      expect (PMF.uniformOfFintype Γ) g := by
  have hs : (∑ ω, if B ω then f ω else 0) = ∑ ω : {ω // B ω}, f ω.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) f
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hΓ : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [conditionalExpect, uniform_expect, uniform_probability, hs,
    Fintype.sum_equiv e _ _ hfg, Fintype.card_congr e, uniform_expect]
  field_simp

/-- Prescribed rows leave the exact finite residual law, for every real test of
the residual row array and every deterministic enumeration of unused labels. -/
theorem residualConditionalExpect {k N K b : ℕ} (cuts : Cuts k N K)
    (r : RowPrescription N k K b) (hr : Function.Injective r.row)
    (hp : 0 < probability (fixedCountPMF cuts) (prescriptionEvent r)) :
    ∃ residual : Cuts k (N-b) K,
      (∀ j a, residual.count j a = cuts.count j a - usedCount r j a) ∧
      ∀ e : Fin (N-b) → Fin N, Function.Injective e →
        (∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i) →
        ∀ F : (Fin (N-b) → Fin K → Fin k) → ℝ,
          conditionalExpect (fixedCountPMF cuts)
            (fun ω => F (fun q j => sampleEntry ω (e q) j)) (prescriptionEvent r) =
          expect (fixedCountPMF residual) (fun η => F (sampleRow η)) := by
  obtain ⟨residual, hres⟩ := residual_cuts_exists cuts r hr hp
  refine ⟨residual, hres, ?_⟩
  intro e he hc F
  obtain ⟨ω, hω⟩ := prescription_exists r hp
  let hbal := residual_balance r hr e he hc ω hω residual hres
  exact uniform_conditional_expect_equiv (prescriptionEvent r)
    (residualSampleEquiv r hr e he hc residual hres hbal)
    (fun ω => F (fun q j => sampleEntry ω (e q) j))
    (fun η => F (sampleRow η)) (fun _ => rfl)

private theorem conditional_probability_indicator {Ω : Type*} [Fintype Ω]
    (P : PMF Ω) (A B : Ω → Prop) :
    conditionalProbability P A B = conditionalExpect P (fun ω => if A ω then 1 else 0) B := by
  unfold conditionalProbability conditionalExpect probability expect
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  by_cases ha : A ω <;> by_cases hb : B ω <;> simp [ha, hb]

private theorem map_atom_probability {Ω Γ : Type*} [Fintype Ω]
    (P : PMF Ω) (f : Ω → Γ) (x : Γ) :
    ((P.map f) x).toReal = probability P (fun ω => f ω = x) := by
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · unfold probability expect
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : x = f ω
    · simp [h]
    · have h' : f ω ≠ x := Ne.symm h
      simp [h, h']
  · intro ω _
    split_ifs
    · exact P.apply_ne_top ω
    · exact ENNReal.zero_ne_top

/-- The conditional law also transports every event of the remaining rows. -/
theorem residualConditionalProbability {k N K b : ℕ} (cuts : Cuts k N K)
    (r : RowPrescription N k K b) (hr : Function.Injective r.row)
    (hp : 0 < probability (fixedCountPMF cuts) (prescriptionEvent r)) :
    ∃ residual : Cuts k (N-b) K,
      (∀ j a, residual.count j a = cuts.count j a - usedCount r j a) ∧
      ∀ e : Fin (N-b) → Fin N, Function.Injective e →
        (∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i) →
        ∀ A : (Fin (N-b) → Fin K → Fin k) → Prop,
          conditionalProbability (fixedCountPMF cuts)
            (fun ω => A (fun q j => sampleEntry ω (e q) j)) (prescriptionEvent r) =
          probability (fixedCountPMF residual) (fun η => A (sampleRow η)) := by
  obtain ⟨residual, hres, htransport⟩ := residualConditionalExpect cuts r hr hp
  refine ⟨residual, hres, ?_⟩
  intro e he hc A
  rw [conditional_probability_indicator]
  exact htransport e he hc (fun v => if A v then 1 else 0)

/-- Exact frozen residual law, with the original prescribed counts subtracted
and no restriction on the enumeration beyond being a complement bijection. -/
theorem residualLaw : Targets.ResidualLaw := by
  intro k N K b cuts r _hb hr hp
  obtain ⟨residual, hres, htransport⟩ := residualConditionalProbability cuts r hr hp
  refine ⟨residual, hres, ?_⟩
  intro e he hc rows
  have hpred : (fun ω : Sample cuts => ∀ q j, sampleEntry ω (e q) j = rows q j) =
      (fun ω => (fun q j => sampleEntry ω (e q) j) = rows) := by
    funext ω
    simp only [funext_iff]
  rw [hpred, map_atom_probability]
  exact htransport e he hc (fun v => v = rows)

end RiffleLowerV2.Thinning
