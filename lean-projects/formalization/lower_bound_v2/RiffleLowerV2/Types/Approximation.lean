import RiffleLowerV2.Types.WordEstimates
import RiffleLowerV2.Types.ClassEntropy
import RiffleLowerV2.Types.Truncation
import RiffleLowerV2.Types.Rates

noncomputable section
open scoped BigOperators
open TimeProfile Set
namespace RiffleLowerV2.Types

/-- The fixed spatial approximation coefficient, chosen before the cutoff. -/
def typeConstant (k : ℕ) (C : ℝ) : ℝ :=
  1 + C + truncationCostConstant k C + truncationEntropyConstant k C

lemma typeConstant_pos (k : ℕ) {C : ℝ} (hC : 0 ≤ C) : 0 < typeConstant k C := by
  dsimp [typeConstant, truncationCostConstant, truncationEntropyConstant]
  positivity

/-- Every concretely verified rounded class has the claimed finite error. -/
theorem finite_type_approximation {k N K : ℕ} (hk : 2 ≤ k) (cuts : Cuts k N K)
    (hN : 0 < N) (hN2 : 2 ≤ N) (P : BorelPartition k) (I : Finset (Fin K))
    {xi C alpha : ℝ} (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ)))
    (hC : 0 ≤ C) (hreg : P.IsRegular xi C) (ha : alpha ∈ Icc (2 : ℝ) 4)
    (D : RoundedTypeData P) (hspec : TypeDataSpec cuts hN P I xi alpha D) :
    TypeApproximation cuts hN P I alpha
      ((typeConstant k C * (I.card : ℝ)*xi*Real.log (1/xi) +
        (k : ℝ)*P.cellCount*Real.log (1/xi) + 1 +
        (P.cellCount : ℝ)*(2*k+1)*(Real.log ((I.card : ℝ)+1)+2) +
        Real.log (2+(I.card : ℝ)*Real.log (1/xi))) / logScale N) D := by
  rcases hspec with ⟨htotal, hsupport, hround, hden, hraw, hsel, hbins, hcard,
    hmax, htie, hJ0, hH0, hexact, hmass, hlower⟩
  let B := Real.log (1/xi)
  let q := retainedTilt P xi alpha
  let Jbar := ∑ i, (cellPositionCount cuts hN P I i : ℝ) *
    (∑ l, q i l * digitCost (prob (P.rep i) l))
  let Hbar := ∑ i, (cellPositionCount cuts hN P I i : ℝ) * shannonEntropy (q i)
  let js := ∑ j ∈ I, tiltedCost (cuts.profile hN j) alpha
  let hs := ∑ j ∈ I, tiltedEntropy (cuts.profile hN j) alpha
  have hB : 1 ≤ B := cutoff_log_ge_one hxi (cutoff_small hk hxi hxiK).1
  have hxi1 : xi ≤ 1 := by have := (cutoff_small hk hxi hxiK).1; linarith
  have hjrep : |Jbar-js| ≤ (I.card : ℝ)*(truncationCostConstant k C*xi*B) :=
    cell_sum_error cuts hN P I _ _ _ (fun j _ =>
      retainedTilt_cost_transfer hk P hxi hxiK hC hreg ha _ (cuts.profile hN j) rfl)
  have hhrep : |Hbar-hs| ≤ (I.card : ℝ)*(truncationEntropyConstant k C*xi*B) :=
    cell_sum_error cuts hN P I _ _ _ (fun j _ =>
      retainedTilt_entropy_transfer hk P hxi hxiK hC hreg ha _ (cuts.profile hN j) rfl)
  have hjraw : ∀ x ∈ roundedClass cuts hN P I D,
      |-Real.log (massOn cuts x)-Jbar| ≤ C*xi*(I.card : ℝ)+(k : ℝ)*P.cellCount*B := by
    intro x hx
    exact raw_word_cost_error cuts hN P I D hxi hxi1 hreg q hsupport
      (fun i l h => retainedTilt_eq_zero_of_omitted P xi alpha i l h) hround x hx
  have hjemp : ∀ x ∈ roundedClass cuts hN P I D,
      |-Real.log (massOn cuts x)-js| ≤
        C*xi*(I.card : ℝ)+(k : ℝ)*P.cellCount*B+
          (I.card : ℝ)*(truncationCostConstant k C*xi*B) := by
    intro x hx
    exact (abs_sub_le _ Jbar js).trans (add_le_add (hjraw x hx) hjrep)
  have hj := selectedJ_error_of_raw_cost cuts hN hN2 P I D hsel js _ hjemp
  have hhraw : |Real.log (roundedClass cuts hN P I D).card-Hbar| ≤
      (P.cellCount : ℝ)*(2*k+1)*(Real.log ((I.card : ℝ)+1)+2) :=
    roundedClass_entropy_error cuts hN P I D q htotal
      (retainedTilt_nonneg P xi alpha) (fun i => retainedTilt_sum hk P hxi hxiK i) hround
  have hhemp : |Real.log (roundedClass cuts hN P I D).card-hs| ≤
      (P.cellCount : ℝ)*(2*k+1)*(Real.log ((I.card : ℝ)+1)+2) +
        (I.card : ℝ)*(truncationEntropyConstant k C*xi*B) :=
    (abs_sub_le _ Hbar hs).trans (add_le_add hhraw hhrep)
  have hpos : ∀ x ∈ roundedClass cuts hN P I D, 0 < massOn cuts x := fun x hx =>
    massOn_pos cuts x (fun j => hxi.trans_le (hlower x hx j))
  have hloss := selectedClass_log_loss cuts hN P I D hsel hpos hmax
    (show 0 < 2+(I.card : ℝ)*B by positivity) hbins
  have hh := selectedH_error_of_raw_entropy cuts hN hN2 P I D hs _ _ hhemp hloss
  have hc : C*xi*(I.card : ℝ) ≤ C*(I.card : ℝ)*xi*B := by
    have hh := mul_le_mul_of_nonneg_left hB (show 0 ≤ C*(I.card : ℝ)*xi by positivity)
    nlinarith
  have hnB : 0 ≤ (I.card : ℝ)*xi*B := by positivity
  change |typeJ N D-js/logScale N|+|typeH cuts hN P I D-hs/logScale N| ≤ _
  apply (add_le_add hj hh).trans
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (logScale_pos hN2).le
  dsimp [B] at *
  unfold typeConstant
  nlinarith

/-- Uniform finite-to-logarithmic-rate assembly, with explicit constants. -/
theorem type_approximation_uniform {k N K : ℕ} (hk : 2 ≤ k) (cuts : Cuts k N K)
    (hN : 0 < N) (hlarge : typeThreshold ≤ N) (P : BorelPartition k)
    (I : Finset (Fin K)) {xi C T alpha : ℝ} (hxi : 0 < xi)
    (hxiK : xi < 1/(4*(k : ℝ))) (hC : 0 ≤ C) (hT : 0 < T)
    (hreg : P.IsRegular xi C) (ha : alpha ∈ Icc (2 : ℝ) 4)
    (hsize : (I.card : ℝ) ≤ T*logScale N)
    (D : RoundedTypeData P) (hspec : TypeDataSpec cuts hN P I xi alpha D) :
    TypeApproximation cuts hN P I alpha
      (typeConstant k C*T*xi*Real.log (1/xi) +
        roundConstant k P.cellCount T (Real.log (1/xi)) *
          (Real.log (logScale N)+1)/logScale N) D := by
  have hN2 := typeThreshold_ge_two.trans hlarge
  have hL := logScale_pos hN2
  have hB : 0 ≤ Real.log (1/xi) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (cutoff_log_ge_one hxi (cutoff_small hk hxi hxiK).1)
  have hfin := finite_type_approximation hk cuts hN hN2 P I hxi hxiK hC hreg ha D hspec
  have hr := finite_remainder_bound k P.cellCount (Nat.cast_nonneg I.card)
    (logScale_ge_one hlarge) hT hB hsize
  have hc := mul_le_mul_of_nonneg_right hsize
    (show 0 ≤ typeConstant k C*xi*Real.log (1/xi) by
      exact mul_nonneg (mul_nonneg (typeConstant_pos k hC).le hxi.le) hB)
  have hsp : typeConstant k C*(I.card : ℝ)*xi*Real.log (1/xi)/logScale N ≤
      typeConstant k C*T*xi*Real.log (1/xi) := by
    apply (div_le_iff₀ hL).mpr
    nlinarith [hc]
  unfold TypeApproximation at *
  apply hfin.trans
  convert add_le_add hsp hr using 1
  ring

end RiffleLowerV2.Types
