import RiffleUpperV2.Reservoir.InducedMatrix
import RiffleUpperV2.FirstMoment.Empirical
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Filter Topology
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Conditional
open TimeProfile Exploration Reservoir

/-- The induced fixed-count column records exactly the simultaneous event's
later-digit count in the actual observed cylinder. -/
theorem inducedCylinder_count {k N L : ℕ} (cuts : Cuts k N (L+1))
    (x : Prefix k (L+1)) (omega : Sample cuts) (j : Fin (L+1-x.1.val)) (a : Fin k) :
    (inducedCuts cuts (cylinderRows x omega) x omega).count j a =
      prefixLaterCount cuts x (suffixColumn x j) a omega := by
  change ((cylinderRows x omega).filter fun r=>sampleEntry omega r (suffixColumn x j)=a).card=_
  unfold cylinderRows prefixLaterCount
  apply congrArg Finset.card
  ext r
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,RiffleLowerV2.rowWord_get]

/-- A positive large mean turns the absolute two-thirds error into the precise
original-scale relative error used for every induced column. -/
theorem largeMean_error {N : ℕ} (hN : 0<N) {xi mu : ℝ}
    (hmu : (N : ℝ)^xi≤mu) :
    mu^((2 : ℝ)/3)≤mu*(N : ℝ)^(-xi/3) := by
  have hNp : (0 : ℝ)<N := by exact_mod_cast hN
  have hmup : 0<mu := (Real.rpow_pos_of_pos hNp xi).trans_le hmu
  have h := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hNp xi) hmu
    (by norm_num : (-1/3 : ℝ)≤0)
  have he : ((N : ℝ)^xi)^(-1/3 : ℝ)=(N : ℝ)^(-xi/3) := by
    rw [← Real.rpow_mul hNp.le]
    congr 1
    ring
  rw [he] at h
  calc
    _ = mu*mu^(-1/3 : ℝ) := by
      conv_rhs => lhs; rw [← Real.rpow_one mu]
      rw [← Real.rpow_add hmup]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left h hmup.le

/-- H itself supplies the actual size and all suffix coordinate estimates.
The threshold depends only on xi and precedes every model choice. -/
theorem largeCylinder_concentration (xi : ℝ) (hxi : 0<xi) :
    ∃ N0 : ℕ, 2≤N0 ∧ ∀ N : ℕ, N0≤N → ∀ k L : ℕ,
      ∀ cuts : Cuts k N (L+1), ∀ D : ℕ, ∀ g : ℝ,
      ∀ x : Prefix k (L+1), ∀ omega : Sample cuts,
      concentrationEvent cuts D g xi omega → (N : ℝ)^xi≤prefixMean cuts x →
      prefixMean cuts x/2≤((cylinderRows x omega).card : ℝ) ∧
      ((cylinderRows x omega).card : ℝ)≤2*prefixMean cuts x ∧
      2≤(cylinderRows x omega).card ∧ (cylinderRows x omega).card≤N ∧
      ∀ hm : 0<(cylinderRows x omega).card,
      ∀ j : Fin (L+1-x.1.val), ∀ a : Fin k,
        |prob ((inducedCuts cuts (cylinderRows x omega) x omega).profile hm j) a-
          (cuts.count (suffixColumn x j) a : ℝ)/N|≤2*(N : ℝ)^(-xi/3) := by
  have hpow := (tendsto_rpow_atTop hxi).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hneg := (tendsto_rpow_neg_atTop (by positivity : 0<xi/3)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N1,hN1⟩ := eventually_atTop.mp (hpow.eventually_ge_atTop 4)
  obtain ⟨N2,hN2⟩ := eventually_atTop.mp (hneg.eventually_le_const (by norm_num : (0 : ℝ)<1/2))
  refine ⟨N1+N2+2,by omega,?_⟩
  intro N hNN k L cuts D g x omega hH hlarge
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hmu : 0<prefixMean cuts x := (Real.rpow_pos_of_pos hNp xi).trans_le hlarge
  have ht : (N : ℝ)^(-xi/3)≤1/2 := by simpa only [neg_div,Function.comp_apply] using hN2 N (by omega)
  have ht0 : 0≤(N : ℝ)^(-xi/3) := Real.rpow_nonneg hNp.le _
  have hfour : 4≤prefixMean cuts x := (hN1 N (by omega)).trans hlarge
  have herr := largeMean_error (show 0<N by omega) hlarge
  have hhalf : (prefixMean cuts x)^((2 : ℝ)/3)≤prefixMean cuts x/2 := by
    have hh := mul_le_mul_of_nonneg_left ht hmu.le
    linarith
  have hsize := (hH.2.1 x hlarge).1
  change |((cylinderRows x omega).card : ℝ)-prefixMean cuts x|≤_ at hsize
  have hsizeLo := (abs_le.mp hsize).1
  have hsizeHi := (abs_le.mp hsize).2
  have hmlo : prefixMean cuts x/2≤((cylinderRows x omega).card : ℝ) := by linarith
  have hmhi : ((cylinderRows x omega).card : ℝ)≤2*prefixMean cuts x := by linarith
  have hm2 : 2≤(cylinderRows x omega).card := by
    exact_mod_cast (show (2 : ℝ)≤((cylinderRows x omega).card : ℝ) by linarith)
  refine ⟨hmlo,hmhi,hm2,by simpa using Finset.card_le_univ (cylinderRows x omega),?_⟩
  intro hm j a
  have hmp : (0 : ℝ)<(cylinderRows x omega).card := by exact_mod_cast hm
  have hc := (hH.2.1 x hlarge).2 (suffixColumn x j) a (by dsimp [suffixColumn]; omega)
  rw [← inducedCylinder_count] at hc
  change |((inducedCuts cuts (cylinderRows x omega) x omega).count j a : ℝ)-
    ((cylinderRows x omega).card : ℝ)*((cuts.count (suffixColumn x j) a : ℝ)/N)|≤_ at hc
  change |((inducedCuts cuts (cylinderRows x omega) x omega).count j a : ℝ)/
    (cylinderRows x omega).card-(cuts.count (suffixColumn x j) a : ℝ)/N|≤_
  have hdiff : ((inducedCuts cuts (cylinderRows x omega) x omega).count j a : ℝ)/
      (cylinderRows x omega).card-(cuts.count (suffixColumn x j) a : ℝ)/N =
      (((inducedCuts cuts (cylinderRows x omega) x omega).count j a : ℝ)-
        ((cylinderRows x omega).card : ℝ)*((cuts.count (suffixColumn x j) a : ℝ)/N))/
        (cylinderRows x omega).card := by field_simp
  rw [hdiff]
  rw [abs_div,abs_of_pos hmp]
  apply (div_le_iff₀ hmp).mpr
  exact hc.trans (herr.trans (by nlinarith [mul_le_mul_of_nonneg_right hmlo ht0]))

end RiffleUpperV2.Conditional
