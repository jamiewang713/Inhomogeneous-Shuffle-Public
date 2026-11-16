import RiffleUpperV2.FirstMoment.Count
import RiffleUpperV2.Compat.EmpiricalTailLimits
import RiffleUpperV2.Compat.EmpiricalWordMass
import RiffleUpperV2.Hypergeometric.CylinderMean

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.FirstMoment
open TimeProfile RiffleLowerV2.Thinning
attribute [local instance] Classical.propDecidable

def wordRows {k n d : ℕ} {cuts : Cuts k n d} (R : Finset (Fin n))
    (w : Fin d → Fin k) (omega : Sample cuts) : Finset (Fin n) :=
  R.filter fun r => sampleRow omega r = w

def rowsInWords {k n d : ℕ} {cuts : Cuts k n d} (R : Finset (Fin n))
    (W : Finset (Fin d → Fin k)) (omega : Sample cuts) : Finset (Fin n) :=
  R.filter fun r => sampleRow omega r ∈ W

/-- Each full-word occupancy has its exact product expectation in the actual law. -/
theorem wordRows_expect {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) (w : Fin d → Fin k) :
    expect (fixedCountPMF cuts) (fun omega => ((wordRows R w omega).card : ℝ)) =
      R.card*Compat.wordWeight (fun j b => prob (cuts.profile hn j) b) w := by
  have hset (omega : Sample cuts) : wordRows R w omega =
      Hypergeometric.cylinderSet cuts R (fun j => {w j}) omega := by
    ext r
    simp only [wordRows, Finset.mem_filter, Hypergeometric.cylinderSet,
      intersectionWithin, Finset.mem_univ, Finset.mem_singleton, true_and]
    constructor
    · rintro ⟨hr,hw⟩
      exact ⟨hr, fun j => congrFun hw j⟩
    · rintro ⟨hr,hw⟩
      exact ⟨hr, funext hw⟩
  simp_rw [hset]
  change expect (fixedCountPMF cuts)
    (fun omega => (Hypergeometric.cylinderCount cuts R (fun j => {w j}) omega : ℝ)) = _
  exact (Hypergeometric.cylinderMean_eq_expect cuts R (fun j => {w j})).symm.trans (by
    simp [Hypergeometric.cylinderMean, Hypergeometric.cylinderMass,
      Hypergeometric.allowedCount, Compat.wordWeight, Cuts.profile_prob])

/-- Exact finite Fubini for any word event; no independence between rows is used. -/
theorem rowsInWords_expect {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) (W : Finset (Fin d → Fin k)) :
    expect (fixedCountPMF cuts) (fun omega => ((rowsInWords R W omega).card : ℝ)) =
      R.card*∑ w ∈ W, Compat.wordWeight (fun j b => prob (cuts.profile hn j) b) w := by
  have hf (omega : Sample cuts) : ((rowsInWords R W omega).card : ℝ) =
      ∑ w ∈ W, ((wordRows R w omega).card : ℝ) := by
    exact_mod_cast (Finset.sum_card_fiberwise_eq_card_filter R W (sampleRow omega)).symm
  calc
    _ = ∑ w ∈ W, expect (fixedCountPMF cuts)
        (fun omega => ((wordRows R w omega).card : ℝ)) := by
      simp only [RiffleLowerV2.expect]
      simp_rw [hf, Finset.mul_sum]
      exact Finset.sum_comm
    _ = _ := by simp_rw [wordRows_expect cuts hn R]; rw [Finset.mul_sum]

def rareDigits {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n) (chi : ℝ)
    (j : Fin d) : Finset (Fin k) := Finset.univ.filter fun b => prob (cuts.profile hn j) b < chi

def rareWords {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n) (chi : ℝ) (h : ℕ) :
    Finset (Fin d → Fin k) :=
  Finset.univ.filter fun w => h ≤ Compat.badCount (rareDigits cuts hn chi) w

/-- Actual row expectation bounded by the finite binomial union tail. -/
theorem rareRows_expect_le_tail {k n d N : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (hnN : n ≤ N) (R : Finset (Fin n)) {chi : ℝ} (hchi : 0 < chi) (h : ℕ) :
    expect (fixedCountPMF cuts)
      (fun omega => ((rowsInWords R (rareWords cuts hn chi h) omega).card : ℝ)) ≤
      (N : ℝ)*RiffleProfiles.tailWeight d h ((k : ℝ)*chi) := by
  rw [rowsInWords_expect cuts hn R]
  have hm : 0 ≤ Compat.badWordMass (fun j b => prob (cuts.profile hn j) b)
      (rareDigits cuts hn chi) h :=
    Finset.sum_nonneg fun w _ => Compat.wordWeight_nonneg _ (fun j b => prob_nonneg _ _) w
  have hR : (R.card : ℝ) ≤ N := by
    exact_mod_cast (Finset.card_le_univ R).trans (by simpa using hnN)
  have hb := Compat.badWordMass_smallDigits_le_tailWeight
    (fun j b => prob (cuts.profile hn j) b) (rareDigits cuts hn chi)
    (fun j b => prob_nonneg _ _) (fun j => sum_prob _) hchi
    (fun j b hb => (Finset.mem_filter.mp hb).2.le) h
  simp only [Fintype.card_fin] at hb
  exact (mul_le_mul_of_nonneg_right hR hm).trans
    (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))

/-- Counting either bad-word family costs at most the sum of their row expectations. -/
theorem rowsInWords_union_expect_le {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (W V : Finset (Fin d → Fin k)) :
    expect (fixedCountPMF cuts) (fun omega => ((rowsInWords R (W ∪ V) omega).card : ℝ)) ≤
      expect (fixedCountPMF cuts) (fun omega => ((rowsInWords R W omega).card : ℝ))+
      expect (fixedCountPMF cuts) (fun omega => ((rowsInWords R V omega).card : ℝ)) := by
  rw [← expect_add]
  apply expect_mono
  intro omega
  have hset : rowsInWords R (W ∪ V) omega = rowsInWords R W omega ∪ rowsInWords R V omega := by
    ext r
    simp [rowsInWords, and_or_left]
  rw [hset, ← Nat.cast_add]
  exact_mod_cast Finset.card_union_le _ _


theorem rareWords_mono {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    {chi chi' : ℝ} (hchi : chi ≤ chi') (h : ℕ) :
    rareWords cuts hn chi h ⊆ rareWords cuts hn chi' h := by
  intro w hw
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,(Finset.mem_filter.mp hw).2.trans ?_⟩
  apply Finset.card_le_card
  intro j hj
  simp only [Compat.badPositions, Finset.mem_filter, Finset.mem_univ, true_and,
    rareDigits] at hj ⊢
  exact hj.trans_le hchi

theorem rowsInWords_expect_mono {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) {W V : Finset (Fin d → Fin k)} (hWV : W ⊆ V) :
    expect (fixedCountPMF cuts) (fun omega => ((rowsInWords R W omega).card : ℝ)) ≤
      expect (fixedCountPMF cuts) (fun omega => ((rowsInWords R V omega).card : ℝ)) := by
  apply expect_mono
  intro omega
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro r hr
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).1,hWV (Finset.mem_filter.mp hr).2⟩

/-- A full-word rare-count majorant for all boundary/extension truncation failures.
The actual boundary and extension containment is proved separately. -/
def discardEnvelope {k n d : ℕ} (N : ℕ) (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) (C chi : ℝ) (omega : Sample cuts) : Finset (Fin n) :=
  rowsInWords R (rareWords cuts hn chi (boundaryBudget N C chi+1) ∪
    rareWords cuts hn chi (extensionBudget N chi+1)) omega

/-- The expected full-word majorant is polynomially negligible on the actual law.
C is fixed first, chi afterwards, and original N controls subdecks throughout. -/
theorem discardEnvelope_power_bound (k : ℕ) (T D C : ℝ)
    (hT : 0 ≤ T) (hD : 0 < D) (hC : D+3 ≤ C) :
    ∃ chi0 : ℝ, 0 < chi0 ∧ chi0 < 1 ∧ ∀ chi : ℝ, 0 < chi → chi < chi0 →
      ∀ N n d : ℕ, 2 ≤ N → ∀ hn : 0 < n, n ≤ N →
        (d : ℝ) ≤ T*logScale N → ∀ cuts : Cuts k n d, ∀ R : Finset (Fin n),
        expect (fixedCountPMF cuts) (fun omega => ((discardEnvelope N cuts hn R C chi omega).card : ℝ)) ≤
          (N : ℝ)^(-D) := by
  obtain ⟨cb,hcb,hcb1,hb⟩ := Compat.boundary_tailWeight_small_chi k T C 1 hT
    (by linarith) (by norm_num)
  obtain ⟨ce,hce,hce1,he⟩ := Compat.exceptional_tailWeight_small_chi k T (D+1) hT
  refine ⟨min cb ce,lt_min hcb hce,(min_le_left _ _).trans_lt hcb1,?_⟩
  intro chi hchi hchi0 N n d hN hn hnN hd cuts R
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hbr := rareRows_expect_le_tail cuts hn hnN R hchi (boundaryBudget N C chi+1)
  have hboundb : expect (fixedCountPMF cuts)
      (fun omega => ((rowsInWords R (rareWords cuts hn chi (boundaryBudget N C chi+1)) omega).card : ℝ)) ≤
      (N : ℝ)^(-D-1) := by
    apply hbr.trans
    have h := hb chi hchi (hchi0.trans_le (min_le_left _ _)) N d hN hd
    apply h.trans
    exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
  have hbounde : expect (fixedCountPMF cuts)
      (fun omega => ((rowsInWords R (rareWords cuts hn chi (extensionBudget N chi+1)) omega).card : ℝ)) ≤
      (N : ℝ)^(-D-1) := by
    apply (rowsInWords_expect_mono cuts R (rareWords_mono cuts hn
      (show chi ≤ 3*chi by linarith) (extensionBudget N chi+1))).trans
    apply (rareRows_expect_le_tail cuts hn hnN R (show 0 < 3*chi by positivity)
      (extensionBudget N chi+1)).trans
    have h := he chi hchi (hchi0.trans_le (min_le_right _ _)) N d hN hd
    convert h using 1 <;> first | rfl | congr 1; ring
  calc
    _ ≤ (N : ℝ)^(-D-1)+(N : ℝ)^(-D-1) :=
      (rowsInWords_union_expect_le cuts R _ _).trans (add_le_add hboundb hbounde)
    _ = 2*(N : ℝ)^(-D-1) := by ring
    _ ≤ (N : ℝ)*(N : ℝ)^(-D-1) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast hN) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (N : ℝ)^(-D) := by
      calc
        _ = (N : ℝ)^(1 : ℝ)*(N : ℝ)^(-D-1) := by rw [Real.rpow_one]
        _ = (N : ℝ)^(1+(-D-1)) := (Real.rpow_add hNp _ _).symm
        _ = _ := by congr 1; ring

end RiffleUpperV2.FirstMoment
