import RiffleLowerV2.Thinning.Residual

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RiffleLowerV2.Thinning
open TimeProfile

/-- Number of prescribed words that already match a given prefix. -/
def prescribedPrefixCount {N k K b : ℕ} (r : RowPrescription N k K b) (w : Prefix k K) : ℕ :=
  (Finset.univ.filter fun q => (r.word q).toList.take w.1.val = w.2.toList).card

/-- The count remaining after the prescribed labels have been removed. -/
def residualPrefixCount {N k K b : ℕ} {cuts : Cuts k N K}
    (r : RowPrescription N k K b) (w : Prefix k K) (ω : Sample cuts) : ℕ :=
  prefixCount w ω - prescribedPrefixCount r w

/-- The exact residual prefix mass, including every subtracted digit count. -/
def residualPrefixMass {N k K b : ℕ} (cuts : Cuts k N K)
    (r : RowPrescription N k K b) (w : Prefix k K) : ℝ :=
  ∏ j : Fin w.1.val,
    ((cuts.count ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ w.1.isLt)⟩ (w.2.get j) -
      usedCount r ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ w.1.isLt)⟩ (w.2.get j) : ℕ) : ℝ) /
      (N-b : ℕ)

/-- The population in the conditional mean is `N-b`. -/
def residualPrefixMean {N k K b : ℕ} (cuts : Cuts k N K)
    (r : RowPrescription N k K b) (w : Prefix k K) : ℝ :=
  (N-b : ℕ) * residualPrefixMass cuts r w

def rowArrayPrefixCount {n k K : ℕ} (w : Prefix k K)
    (rows : Fin n → Fin K → Fin k) : ℕ :=
  (Finset.univ.filter fun q => (List.Vector.ofFn (rows q)).toList.take w.1.val = w.2.toList).card

private theorem predicate_count_split {N k K b : ℕ} (r : RowPrescription N k K b)
    (hr : Function.Injective r.row) (e : Fin (N-b) → Fin N)
    (he : Function.Injective e)
    (hc : ∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i) (P : Fin N → Prop) :
    (Finset.univ.filter P).card =
      (Finset.univ.filter fun q => P (r.row q)).card +
      (Finset.univ.filter fun q => P (e q)).card := by
  have hbij : Function.Bijective (Sum.elim r.row e) := by
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
        exact ⟨Sum.inr q, hq⟩
  have h := hbij.sum_comp (fun i => if P i then (1 : ℕ) else 0)
  rw [Fintype.sum_sum_type] at h
  change (∑ q, if P (r.row q) then (1 : ℕ) else 0) +
    (∑ q, if P (e q) then (1 : ℕ) else 0) =
    (∑ i, if P i then (1 : ℕ) else 0) at h
  simpa only [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one] using h.symm

/-- Subtracting the prescribed prefix matches is exactly restriction to the
unused labels, on the event on which those words were prescribed. -/
theorem residualPrefixCount_eq_restriction {N k K b : ℕ} {cuts : Cuts k N K}
    (r : RowPrescription N k K b) (hr : Function.Injective r.row)
    (e : Fin (N-b) → Fin N) (he : Function.Injective e)
    (hc : ∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i)
    (w : Prefix k K) (ω : Sample cuts) (hω : prescriptionEvent r ω) :
    residualPrefixCount r w ω = rowArrayPrefixCount w (fun q j => sampleEntry ω (e q) j) := by
  have h := predicate_count_split r hr e he hc
    (fun i => (rowWord ω i).toList.take w.1.val = w.2.toList)
  change ∀ q, rowWord ω (r.row q) = r.word q at hω
  simp only [hω] at h
  have hcount : prefixCount w ω = prescribedPrefixCount r w +
      rowArrayPrefixCount w (fun q j => sampleEntry ω (e q) j) := by
    convert h using 1 <;>
      simp only [prefixCount, prescribedPrefixCount, rowArrayPrefixCount, rowWord, sampleRow] <;>
      congr
  unfold residualPrefixCount
  omega

theorem residualPrefixMass_eq {N k K b : ℕ} (cuts : Cuts k N K)
    (r : RowPrescription N k K b) (residual : Cuts k (N-b) K)
    (hres : ∀ j a, residual.count j a = cuts.count j a - usedCount r j a)
    (w : Prefix k K) : prefixMass residual w = residualPrefixMass cuts r w := by
  simp only [prefixMass, residualPrefixMass, hres]

theorem residualPrefixMean_eq {N k K b : ℕ} (cuts : Cuts k N K)
    (r : RowPrescription N k K b) (residual : Cuts k (N-b) K)
    (hres : ∀ j a, residual.count j a = cuts.count j a - usedCount r j a)
    (w : Prefix k K) : prefixMean residual w = residualPrefixMean cuts r w := by
  simp only [prefixMean, residualPrefixMean, residualPrefixMass_eq cuts r residual hres]

private theorem conditionalExpect_congr_on {Ω : Type*} [Fintype Ω]
    (P : PMF Ω) (B : Ω → Prop) (f g : Ω → ℝ) (h : ∀ ω, B ω → f ω = g ω) :
    conditionalExpect P f B = conditionalExpect P g B := by
  unfold conditionalExpect expect
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hb : B ω
  · simp [hb, h ω hb]
  · simp [hb]

private theorem conditionalProbability_congr_on {Ω : Type*} [Fintype Ω]
    (P : PMF Ω) (B A C : Ω → Prop) (h : ∀ ω, B ω → (A ω ↔ C ω)) :
    conditionalProbability P A B = conditionalProbability P C B := by
  unfold conditionalProbability
  congr 1
  congr 1
  funext ω
  apply propext
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨(h ω hb).mp ha, hb⟩
  · rintro ⟨hc, hb⟩
    exact ⟨(h ω hb).mpr hc, hb⟩

/-- Exact residual prefix expectation transport for an arbitrary complement
enumeration chosen before sampling. The test may be any real function. -/
theorem residualPrefixExpect {N k K b : ℕ} (cuts : Cuts k N K)
    (r : RowPrescription N k K b) (_hb : b < N) (hr : Function.Injective r.row)
    (hp : 0 < probability (fixedCountPMF cuts) (prescriptionEvent r)) :
    ∃ residual : Cuts k (N-b) K,
      (∀ j a, residual.count j a = cuts.count j a - usedCount r j a) ∧
      ∀ e : Fin (N-b) → Fin N, Function.Injective e →
        (∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i) →
        ∀ (w : Prefix k K) (F : ℕ → ℝ),
          conditionalExpect (fixedCountPMF cuts) (fun ω => F (residualPrefixCount r w ω))
            (prescriptionEvent r) = expect (fixedCountPMF residual) (fun η => F (prefixCount w η)) := by
  obtain ⟨residual, hres, ht⟩ := residualConditionalExpect cuts r hr hp
  refine ⟨residual, hres, ?_⟩
  intro e he hc w F
  calc
    _ = conditionalExpect (fixedCountPMF cuts)
        (fun ω => F (rowArrayPrefixCount w (fun q j => sampleEntry ω (e q) j))) (prescriptionEvent r) := by
      apply conditionalExpect_congr_on
      intro ω hω
      rw [residualPrefixCount_eq_restriction r hr e he hc w ω hω]
    _ = _ := ht e he hc (fun v => F (rowArrayPrefixCount w v))

/-- Exact residual prefix event transport, retaining the positive residual
population domain used by the subsequent concentration theorems. -/
theorem residualPrefixProbability {N k K b : ℕ} (cuts : Cuts k N K)
    (r : RowPrescription N k K b) (_hb : b < N) (hr : Function.Injective r.row)
    (hp : 0 < probability (fixedCountPMF cuts) (prescriptionEvent r)) :
    ∃ residual : Cuts k (N-b) K,
      (∀ j a, residual.count j a = cuts.count j a - usedCount r j a) ∧
      ∀ e : Fin (N-b) → Fin N, Function.Injective e →
        (∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i) →
        ∀ (w : Prefix k K) (A : ℕ → Prop),
          conditionalProbability (fixedCountPMF cuts) (fun ω => A (residualPrefixCount r w ω))
            (prescriptionEvent r) = probability (fixedCountPMF residual) (fun η => A (prefixCount w η)) := by
  obtain ⟨residual, hres, ht⟩ := residualConditionalProbability cuts r hr hp
  refine ⟨residual, hres, ?_⟩
  intro e he hc w A
  calc
    _ = conditionalProbability (fixedCountPMF cuts)
        (fun ω => A (rowArrayPrefixCount w (fun q j => sampleEntry ω (e q) j))) (prescriptionEvent r) := by
      apply conditionalProbability_congr_on
      intro ω hω
      rw [residualPrefixCount_eq_restriction r hr e he hc w ω hω]
    _ = _ := ht e he hc (fun v => A (rowArrayPrefixCount w v))

/-- A deterministic bijective enumeration of unused labels always exists. -/
theorem existsComplementEnumeration {N k K b : ℕ} (r : RowPrescription N k K b)
    (hr : Function.Injective r.row) :
    ∃ e : Fin (N-b) → Fin N, Function.Injective e ∧
      ∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i := by
  have hcard : Fintype.card {i : Fin N // ¬∃ q, r.row q = i} = N-b := by
    rw [Fintype.card_subtype_compl]
    have h := Fintype.card_congr
      (show Fin b ≃ {i : Fin N // ∃ q, r.row q = i} from Equiv.ofInjective r.row hr)
    simpa only [Fintype.card_fin] using congrArg (fun n => N-n) h.symm
  let u : Fin (N-b) ≃ {i : Fin N // ¬∃ q, r.row q = i} :=
    (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨(fun q => (u q).val), Subtype.coe_injective.comp u.injective, ?_⟩
  intro i
  constructor
  · rintro ⟨q, rfl⟩
    exact (u q).property
  · intro hi
    obtain ⟨q, hq⟩ := u.surjective ⟨i, hi⟩
    exact ⟨q, congrArg Subtype.val hq⟩

/-- Adapter from the unconditional concrete prefix theorem to the exact
conditional residual bounds. Its unconditional input is explicit. -/
theorem residualPrefixTails_of_prefixTails (hT : Targets.PrefixTails)
    {N k K b : ℕ} (cuts : Cuts k N K) (r : RowPrescription N k K b)
    (hb : b < N) (hr : Function.Injective r.row)
    (hp : 0 < probability (fixedCountPMF cuts) (prescriptionEvent r)) (w : Prefix k K) :
    (∀ t : ℝ, 0 < t →
      conditionalProbability (fixedCountPMF cuts)
        (fun ω => t ≤ |(residualPrefixCount r w ω : ℝ) - residualPrefixMean cuts r w|)
        (prescriptionEvent r) ≤
      2 * Real.exp (-t^2 / (4 * (residualPrefixMean cuts r w + t)))) ∧
    conditionalProbability (fixedCountPMF cuts)
      (fun ω => (residualPrefixCount r w ω : ℝ) ≤ residualPrefixMean cuts r w / 2)
      (prescriptionEvent r) ≤ Real.exp (-chernoffConstant * residualPrefixMean cuts r w) ∧
    conditionalProbability (fixedCountPMF cuts) (fun ω => residualPrefixCount r w ω < 2)
      (prescriptionEvent r) ≤ 2 * Real.exp (-residualPrefixMean cuts r w / 2) := by
  obtain ⟨residual, hres, ht⟩ := residualPrefixProbability cuts r hb hr hp
  obtain ⟨e, he, hc⟩ := existsComplementEnumeration r hr
  have hmean := residualPrefixMean_eq cuts r residual hres w
  have htail := hT residual (Nat.sub_pos_of_lt hb) w
  refine ⟨?_, ?_, ?_⟩
  · intro t hpos
    rw [ht e he hc w (fun n => t ≤ |(n : ℝ) - residualPrefixMean cuts r w|)]
    simpa only [hmean] using htail.1 t hpos
  · rw [ht e he hc w (fun n => (n : ℝ) ≤ residualPrefixMean cuts r w / 2)]
    simpa only [hmean] using htail.2.1
  · rw [ht e he hc w (fun n => n < 2)]
    simpa only [hmean] using htail.2.2

/-- Adapter for the full positive-parameter transform, including its binomial
and exponential comparisons with the exact residual mass and mean. -/
theorem residualPrefixTransform_of_prefixTransform
    (hT : ∀ {k N K : ℕ} (cuts : Cuts k N K), 0 < N → ∀ (w : Prefix k K) (s : ℝ), 0 < s →
      expect (fixedCountPMF cuts) (fun ω => s ^ prefixCount w ω) ≤
        (1-prefixMass cuts w+prefixMass cuts w*s)^N ∧
      (1-prefixMass cuts w+prefixMass cuts w*s)^N ≤ Real.exp (prefixMean cuts w*(s-1)))
    {N k K b : ℕ} (cuts : Cuts k N K) (r : RowPrescription N k K b)
    (hb : b < N) (hr : Function.Injective r.row)
    (hp : 0 < probability (fixedCountPMF cuts) (prescriptionEvent r))
    (w : Prefix k K) (s : ℝ) (hs : 0 < s) :
    conditionalExpect (fixedCountPMF cuts) (fun ω => s ^ residualPrefixCount r w ω)
      (prescriptionEvent r) ≤ (1-residualPrefixMass cuts r w+residualPrefixMass cuts r w*s)^(N-b) ∧
    (1-residualPrefixMass cuts r w+residualPrefixMass cuts r w*s)^(N-b) ≤
      Real.exp (residualPrefixMean cuts r w*(s-1)) := by
  obtain ⟨residual, hres, ht⟩ := residualPrefixExpect cuts r hb hr hp
  obtain ⟨e, he, hc⟩ := existsComplementEnumeration r hr
  have hmass := residualPrefixMass_eq cuts r residual hres w
  have hmean := residualPrefixMean_eq cuts r residual hres w
  have htransform := hT residual (Nat.sub_pos_of_lt hb) w s hs
  constructor
  · rw [ht e he hc w]
    simpa only [hmass] using htransform.1
  · simpa only [hmass, hmean] using htransform.2

end RiffleLowerV2.Thinning
