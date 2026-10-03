import RiffleUpperV2.Localization.SideBounds

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace RiffleUpperV2.Localization
open Anchor

private theorem expect_sum {Ω I : Type*} [Fintype Ω] [Fintype I] (P : PMF Ω) (f : I → Ω → ℝ) :
    RiffleLowerV2.expect P (fun ω => ∑ i, f i ω) = ∑ i, RiffleLowerV2.expect P (f i) := by
  simp only [RiffleLowerV2.expect, Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem expect_sub {Ω : Type*} [Fintype Ω] (P : PMF Ω) (f g : Ω → ℝ) :
    RiffleLowerV2.expect P (fun ω => f ω-g ω) =
      RiffleLowerV2.expect P f-RiffleLowerV2.expect P g := by
  simp only [RiffleLowerV2.expect, mul_sub, Finset.sum_sub_distrib]

def sideDeviation {k n d : ℕ} (cuts : Cuts k n d) (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) : ℝ :=
  ∑ i : Fin x.1.val, |((sideRows cuts s R x i ω).card : ℝ)-sideMean s cuts R x i|

theorem lowerEndpoint_centered {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n) (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) :
    (lowerEndpoint c₀ R x ω : ℝ) - expect (fixedCountPMF cuts) (fun ζ => (lowerEndpoint c₀ R x ζ : ℝ)) =
      ∑ i : Fin x.1.val, (((sideRows cuts .lower R x i ω).card : ℝ)-sideMean .lower cuts R x i) := by
  have he (ζ : Sample cuts) : (lowerEndpoint c₀ R x ζ : ℝ) = (c₀ : ℝ) +
      ∑ i : Fin x.1.val, ((sideRows cuts .lower R x i ζ).card : ℝ) := by
    rw [lowerEndpoint_side_sum]
    push_cast
    rfl
  simp_rw [he]
  change _ - RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) _ = _
  rw [RiffleLowerV2.Thinning.expect_add, RiffleLowerV2.Model.expect_const, expect_sum]
  simp_rw [show ∀ i : Fin x.1.val, RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts)
    (fun ζ => ((sideRows cuts .lower R x i ζ).card : ℝ)) = sideMean .lower cuts R x i from
      fun i => sideRows_expect cuts hn .lower R x i]
  rw [Finset.sum_sub_distrib]
  ring

theorem upperEndpoint_centered {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n) (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) :
    (upperEndpoint c₀ R x ω : ℝ) - expect (fixedCountPMF cuts) (fun ζ => (upperEndpoint c₀ R x ζ : ℝ)) =
      -(∑ i : Fin x.1.val, (((sideRows cuts .upper R x i ω).card : ℝ)-sideMean .upper cuts R x i)) := by
  have he (ζ : Sample cuts) : (upperEndpoint c₀ R x ζ : ℝ) = (c₀ : ℝ) + (R.card : ℝ) -
      ∑ i : Fin x.1.val, ((sideRows cuts .upper R x i ζ).card : ℝ) := by
    rw [upperEndpoint_side_sum]
    push_cast
    rfl
  simp_rw [he]
  change _ - RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) _ = _
  rw [expect_sub, RiffleLowerV2.Model.expect_const, expect_sum]
  simp_rw [show ∀ i : Fin x.1.val, RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts)
    (fun ζ => ((sideRows cuts .upper R x i ζ).card : ℝ)) = sideMean .upper cuts R x i from
      fun i => sideRows_expect cuts hn .upper R x i]
  rw [Finset.sum_sub_distrib]
  ring

/-- Both endpoints are controlled by the same smaller-side deviations plus occupancy. -/
theorem endpoint_deviation_le {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (s : SuffixSide) (c₀ : ℤ) (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) :
    max |(lowerEndpoint c₀ R x ω : ℝ) - expect (fixedCountPMF cuts) (fun ζ => (lowerEndpoint c₀ R x ζ : ℝ))|
      |(upperEndpoint c₀ R x ω : ℝ) - expect (fixedCountPMF cuts) (fun ζ => (upperEndpoint c₀ R x ζ : ℝ))| ≤
      sideDeviation cuts s R x ω + |((Anchor.prefixRows R x ω).card : ℝ)-anchoredMean cuts R x| := by
  have hlen := expected_endpoint_length cuts hn c₀ R x
  have hexact : (upperEndpoint c₀ R x ω : ℝ) = (lowerEndpoint c₀ R x ω : ℝ) +
      ((Anchor.prefixRows R x ω).card : ℝ) := by simp [upperEndpoint]
  have habs : 0 ≤ |((Anchor.prefixRows R x ω).card : ℝ)-anchoredMean cuts R x| := abs_nonneg _
  apply max_le
  cases s with
  | lower =>
    rw [lowerEndpoint_centered cuts hn]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (le_add_of_nonneg_right habs)
  | upper =>
    have he : (lowerEndpoint c₀ R x ω : ℝ) - expect (fixedCountPMF cuts) (fun ζ => (lowerEndpoint c₀ R x ζ : ℝ)) =
        ((upperEndpoint c₀ R x ω : ℝ) - expect (fixedCountPMF cuts) (fun ζ => (upperEndpoint c₀ R x ζ : ℝ))) -
          (((Anchor.prefixRows R x ω).card : ℝ)-anchoredMean cuts R x) := by linarith
    rw [he]
    apply (abs_sub _ _).trans
    apply add_le_add_left
    rw [upperEndpoint_centered cuts hn, abs_neg]
    exact Finset.abs_sum_le_sum_abs _ _
  cases s with
  | lower =>
    have he : (upperEndpoint c₀ R x ω : ℝ) - expect (fixedCountPMF cuts) (fun ζ => (upperEndpoint c₀ R x ζ : ℝ)) =
        ((lowerEndpoint c₀ R x ω : ℝ) - expect (fixedCountPMF cuts) (fun ζ => (lowerEndpoint c₀ R x ζ : ℝ))) +
          (((Anchor.prefixRows R x ω).card : ℝ)-anchoredMean cuts R x) := by linarith
    rw [he]
    apply (abs_add_le _ _).trans
    apply add_le_add_left
    rw [lowerEndpoint_centered cuts hn]
    exact Finset.abs_sum_le_sum_abs _ _
  | upper =>
    rw [upperEndpoint_centered cuts hn, abs_neg]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (le_add_of_nonneg_right habs)

end RiffleUpperV2.Localization
