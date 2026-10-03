import RiffleUpperV2.Localization.EndpointDeviation

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Localization
open Anchor

def windowCount {k n d : ℕ} (cuts : Cuts k n d) (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (i : Option (Fin x.1.val)) (ω : Sample cuts) : ℝ :=
  match i with
  | none => (Anchor.prefixRows R x ω).card
  | some j => (sideRows cuts s R x j ω).card

def windowMean {k n d : ℕ} (cuts : Cuts k n d) (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (i : Option (Fin x.1.val)) : ℝ :=
  match i with
  | none => anchoredMean cuts R x
  | some j => sideMean s cuts R x j

theorem windowCount_tail {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (i : Option (Fin x.1.val))
    {t : ℝ} (ht : 0 < t) :
    probability (fixedCountPMF cuts)
      (fun ω => t ≤ |windowCount cuts s R x i ω-windowMean cuts s R x i|) ≤
      2*Real.exp (-t^2/(4*(windowMean cuts s R x i+t))) := by
  cases i
  · exact prefixRows_tail cuts hn R x ht
  · exact sideRows_tail cuts hn s R x _ ht

private theorem windowTail_scalar {μ B w c : ℝ} (hμ : 0 ≤ μ) (hμB : μ ≤ B)
    (hw : 0 < w) (hc : 1 ≤ c) :
    2*Real.exp (-(w/c)^2/(4*(μ+w/c))) ≤
      2*Real.exp (-w^2/(4*c^2*(B+w))) := by
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have ht : 0 < w/c := div_pos hw hcpos
  have htw : w/c ≤ w := (div_le_iff₀ hcpos).mpr (by nlinarith)
  have hB : 0 ≤ B := hμ.trans hμB
  have hden : 0 < 4*(μ+w/c) := by positivity
  have hdenB : 0 < 4*(B+w) := by positivity
  have hdiv : (w/c)^2/(4*(B+w)) ≤ (w/c)^2/(4*(μ+w/c)) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hden (by linarith)
  have he : (w/c)^2/(4*(B+w)) = w^2/(4*c^2*(B+w)) := by
    field_simp
    <;> ring
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  rw [neg_div, neg_div]
  rw [he] at hdiv
  linarith

/-- Source eq:ub-anchor-finite-window, uniformly on the actual future-column law.
The original first-column assignment is already fixed in R and c₀. -/
theorem endpointWindow {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (c₀ : ℤ) (R : Finset (Fin n)) {χ : ℝ} {y z v x : Prefix k d}
    (hpair : GenuineBoundaryPair cuts R χ y z v) (hvx : IsPrefix v x)
    {w : ℝ} (hw : 0 < w) :
    probability (fixedCountPMF cuts) (fun ω =>
      w < max |(lowerEndpoint c₀ R x ω : ℝ) - expect (fixedCountPMF cuts) (fun ζ => (lowerEndpoint c₀ R x ζ : ℝ))|
        |(upperEndpoint c₀ R x ω : ℝ) - expect (fixedCountPMF cuts) (fun ζ => (upperEndpoint c₀ R x ζ : ℝ))|) ≤
      2*(d+1)*Real.exp (-w^2/(4*(d+1)^2*(χ⁻¹*sideScale cuts R v+w))) := by
  obtain ⟨s,hs,hμ⟩ := smallerSide_mean_bound cuts hn R hpair hvx
  let c : ℝ := d+1
  let B : ℝ := χ⁻¹*sideScale cuts R v
  let t : ℝ := w/c
  have hc : 1 ≤ c := by dsimp [c]; linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have ht : 0 < t := div_pos hw hcpos
  have hbound (i : Option (Fin x.1.val)) : windowMean cuts s R x i ≤ B := by
    cases i with
    | none => exact hμ
    | some i => exact hs i
  have hnonneg (i : Option (Fin x.1.val)) : 0 ≤ windowMean cuts s R x i := by
    cases i with
    | none =>
        exact mul_nonneg (Nat.cast_nonneg _)
          (Finset.prod_nonneg fun _ _ => by positivity)
    | some i => exact sideMean_nonnegative s cuts R x i
  have hfailure : probability (fixedCountPMF cuts) (fun ω =>
      w < max |(lowerEndpoint c₀ R x ω : ℝ) - expect (fixedCountPMF cuts) (fun ζ => (lowerEndpoint c₀ R x ζ : ℝ))|
        |(upperEndpoint c₀ R x ω : ℝ) - expect (fixedCountPMF cuts) (fun ζ => (upperEndpoint c₀ R x ζ : ℝ))|) ≤
      probability (fixedCountPMF cuts) (fun ω => ∃ i : Option (Fin x.1.val),
        t ≤ |windowCount cuts s R x i ω-windowMean cuts s R x i|) := by
    apply RiffleLowerV2.Thinning.probability_mono
    intro ω hω
    by_contra hnone
    have hsmall : ∀ i : Option (Fin x.1.val),
        |windowCount cuts s R x i ω-windowMean cuts s R x i| ≤ t := by
      intro i
      exact le_of_lt (lt_of_not_ge (fun h => hnone ⟨i,h⟩))
    have hsum : sideDeviation cuts s R x ω ≤ (x.1.val : ℝ)*t := by
      calc
        _ ≤ ∑ _i : Fin x.1.val, t := Finset.sum_le_sum (fun i _ => hsmall (some i))
        _ = _ := by simp
    have hsingle := hsmall none
    change |((Anchor.prefixRows R x ω).card : ℝ)-anchoredMean cuts R x| ≤ t at hsingle
    have hdev := endpoint_deviation_le cuts hn s c₀ R x ω
    have hx : (x.1.val : ℝ)+1 ≤ c := by
      dsimp [c]
      exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt_succ x.1.isLt)
    have hct : c*t = w := by dsimp [t]; field_simp
    have htot : sideDeviation cuts s R x ω +
        |((Anchor.prefixRows R x ω).card : ℝ)-anchoredMean cuts R x| ≤ w := by
      nlinarith
    exact (not_lt_of_ge (hdev.trans htot)) hω
  have htail (i : Option (Fin x.1.val)) :
      probability (fixedCountPMF cuts) (fun ω => t ≤ |windowCount cuts s R x i ω-windowMean cuts s R x i|) ≤
        2*Real.exp (-w^2/(4*c^2*(B+w))) :=
    (windowCount_tail cuts hn s R x i ht).trans (windowTail_scalar (hnonneg i) (hbound i) hw hc)
  calc
    _ ≤ _ := hfailure
    _ ≤ ∑ i : Option (Fin x.1.val), probability (fixedCountPMF cuts)
        (fun ω => t ≤ |windowCount cuts s R x i ω-windowMean cuts s R x i|) :=
      RiffleLowerV2.Thinning.probability_iUnion_le _ _
    _ ≤ ∑ _i : Option (Fin x.1.val), 2*Real.exp (-w^2/(4*c^2*(B+w))) :=
      Finset.sum_le_sum (fun i _ => htail i)
    _ = ((x.1.val : ℝ)+1)*(2*Real.exp (-w^2/(4*c^2*(B+w)))) := by simp
    _ ≤ c*(2*Real.exp (-w^2/(4*c^2*(B+w)))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp [c]
      exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt_succ x.1.isLt)
    _ = _ := by dsimp [c,B]; ring

end RiffleUpperV2.Localization
