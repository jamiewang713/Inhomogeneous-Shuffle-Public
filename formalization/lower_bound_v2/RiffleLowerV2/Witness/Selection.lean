import RiffleLowerV2.Shared
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Set
namespace RiffleLowerV2.Witness

/-- Nonempty, bounded real variational domains justify extraction below the supremum. -/
theorem variational_pair (f : ℝ → ℝ → ℝ → ℝ) (T eta M : ℝ)
    (hT : 0 ≤ T) (heta : 0 < eta)
    (hcont : ∀ su ∈ triangle T,
      ContinuousOn (fun a => f a su.1 su.2) (Icc (3 : ℝ) 4))
    (hbound : ∀ su ∈ triangle T, f 3 su.1 su.2 ≤ M)
    (hmargin : eta ≤ sSup ((fun su : ℝ × ℝ =>
      sInf ((fun a => f a su.1 su.2) '' Icc (3 : ℝ) 4)) '' triangle T)) :
    ∃ s u : ℝ, (s,u) ∈ triangle T ∧
      ∀ a ∈ Icc (3 : ℝ) 4, 7*eta/8 ≤ f a s u := by
  let g := fun su : ℝ × ℝ => sInf ((fun a => f a su.1 su.2) '' Icc (3 : ℝ) 4)
  have htri : (triangle T).Nonempty := ⟨(0,0), by exact ⟨le_rfl, le_rfl, hT⟩⟩
  have hbelow (su : ℝ × ℝ) (hsu : su ∈ triangle T) :
      BddBelow ((fun a => f a su.1 su.2) '' Icc (3 : ℝ) 4) :=
    (isCompact_Icc.image_of_continuousOn (hcont su hsu)).bddBelow
  have habove : BddAbove (g '' triangle T) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨su, hsu, rfl⟩
    exact (csInf_le (hbelow su hsu) ⟨3, by norm_num, rfl⟩).trans (hbound su hsu)
  have hlt : 7*eta/8 < sSup (g '' triangle T) := by
    change eta ≤ sSup (g '' triangle T) at hmargin
    linarith
  obtain ⟨_, ⟨su, hsu, rfl⟩, hg⟩ := (lt_csSup_iff habove (htri.image g)).mp hlt
  refine ⟨su.1, su.2, hsu, ?_⟩
  intro a ha
  exact hg.le.trans (csInf_le (hbelow su hsu) ⟨a, ha, rfl⟩)

/-- The three tilt cases, without exchanging the two variational extrema. -/
theorem select_tilt (j : ℝ → ℝ) (c : ℝ)
    (hj : ContinuousOn j (Icc (3 : ℝ) 4)) :
    ∃ theta ∈ Icc (3 : ℝ) 4,
      (theta = 3 ∨ c ≤ j theta) ∧ (theta = 4 ∨ j theta ≤ c) := by
  by_cases h3 : j 3 ≤ c
  · exact ⟨3, by norm_num, Or.inl rfl, Or.inr h3⟩
  by_cases h4 : c ≤ j 4
  · exact ⟨4, by norm_num, Or.inr h4, Or.inl rfl⟩
  obtain ⟨theta, htheta, heq⟩ :=
    intermediate_value_Icc' (by norm_num : (3 : ℝ) ≤ 4) hj
      (show c ∈ Icc (j 4) (j 3) from ⟨(not_le.mp h4).le, (not_le.mp h3).le⟩)
  exact ⟨theta, htheta, Or.inr heq.ge, Or.inr heq.le⟩

/-- Continuous shortening with a separate, displacement-free tilt-four branch. -/
theorem shorten_selection (j f : ℝ → ℝ → ℝ) (s u b eta : ℝ)
    (heta : 0 < eta) (hsu : s ≤ u) (hb : eta / 4 ≤ b)
    (hja : ContinuousOn (fun a => j a u) (Icc (3 : ℝ) 4))
    (hjt : ∀ a ∈ Icc (3 : ℝ) 4, ContinuousOn (j a) (Icc s u))
    (hjzero : ∀ a ∈ Icc (3 : ℝ) 4, j a s = 0)
    (hf : ∀ a ∈ Icc (3 : ℝ) 4, 7 * eta / 8 ≤ f a u)
    (hloss : ∀ a ∈ Icc (3 : ℝ) 4, ∀ v ∈ Icc s u,
      -4 * (j a u - j a v) ≤ f a v - f a u)
    (hfour : ∀ v ∈ Icc s u, f 4 u ≤ f 4 v) :
    ∃ theta ∈ Icc (3 : ℝ) 4, ∃ v ∈ Icc s u,
      j theta v ≤ b / 2 - 4 * kappa eta ∧
      (theta = 3 ∨ j theta v = b / 2 - 4 * kappa eta) ∧
      7 * eta / 8 - 16 * kappa eta ≤ f theta v := by
  obtain ⟨theta, htheta, hlow, hupp⟩ := select_tilt (fun a => j a u) (b/2) hja
  have hk : 0 < kappa eta := by unfold kappa; positivity
  have hc : 0 ≤ b/2 - 4*kappa eta := by unfold kappa; linarith
  by_cases hsmall : j theta u ≤ b/2 - 4*kappa eta
  · have htheta3 : theta = 3 := by
      rcases hlow with h | h
      · exact h
      · linarith
    exact ⟨theta, htheta, u, ⟨hsu, le_rfl⟩, hsmall,
      Or.inl htheta3, by linarith [hf theta htheta]⟩
  obtain ⟨v, hv, heq⟩ := intermediate_value_Icc hsu (hjt theta htheta)
    (show b/2 - 4*kappa eta ∈ Icc (j theta s) (j theta u) from
      ⟨by rw [hjzero theta htheta]; exact hc, (not_le.mp hsmall).le⟩)
  refine ⟨theta, htheta, v, hv, heq.le, Or.inr heq, ?_⟩
  rcases hupp with htheta4 | hjupper
  · subst theta
    linarith [hfour v hv, hf 4 htheta]
  · have hmove := hloss theta htheta v hv
    linarith [hf theta htheta]

/-- The exact cold exponent identity, in the manuscript's scalar notation. -/
theorem cold_identity (b theta jp jt hp ht bp bt : ℝ)
    (hhp : hp = theta * jp - bp) (hht : ht = 2 * jt - bt) :
    2 * (2*b - 2*jp - 2*jt + hp + ht) - (b-jp+hp) =
      ((theta+3)/2*b - bp - 2*bt) + (theta-3)*(jp-b/2) := by
  rw [hhp, hht]
  ring

/-- Fixed rounding errors fit strictly inside the retained witness margins. -/
theorem rounding_margins {eta theta j0 b0 f0 j b f : ℝ}
    (heta : 0 < eta)
    (hupper : j0 ≤ b0/2 - 4*kappa eta)
    (hlower : theta = 3 ∨ j0 = b0/2 - 4*kappa eta)
    (hmargin : 7*eta/8 - 16*kappa eta ≤ f0)
    (hj : |(j-b/2) - (j0-b0/2)| ≤ kappa eta/10)
    (hf : |f-f0| ≤ kappa eta/10) :
    eta/2 ≤ f ∧ j ≤ b/2 - 3*kappa eta ∧
      (theta = 3 ∨ b/2 - 5*kappa eta ≤ j) := by
  obtain ⟨hjlo, hjhi⟩ := abs_le.mp hj
  obtain ⟨hflo, hfhi⟩ := abs_le.mp hf
  have hk : 0 < kappa eta := by unfold kappa; positivity
  refine ⟨?_, by linarith, ?_⟩
  · unfold kappa at *
    linarith
  · rcases hlower with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)

/-- Algebraic geometry and collision conclusions after rounding. -/
theorem final_margins {eta b theta jp jt hp ht bp bt : ℝ}
    (heta : 0 < eta) (htheta : theta ∈ Icc (3 : ℝ) 4)
    (hjp : 0 ≤ jp) (hhp0 : 0 ≤ hp) (hhpj : hp ≤ jp)
    (hupper : jp ≤ b/2 - 3*kappa eta)
    (hlower : theta = 3 ∨ b/2 - 5*kappa eta ≤ jp)
    (hmargin : eta/2 ≤ (theta+3)/2*b - bp - 2*bt)
    (hhp : hp = theta*jp-bp) (hht : ht = 2*jt-bt) :
    kappa eta ≤ b-jp+hp ∧ hp ≤ b-jp-kappa eta ∧
    kappa eta ≤ (2*b-2*jp-2*jt+hp+ht) - (b-jp+hp)/2 := by
  have hk : 0 < kappa eta := by unfold kappa; positivity
  have hid := cold_identity b theta jp jt hp ht bp bt hhp hht
  have hproduct : -5*kappa eta ≤ (theta-3)*(jp-b/2) := by
    rcases hlower with h | h
    · rw [h]
      norm_num
      linarith
    · have hmul := mul_nonneg (show 0 ≤ theta-3 by linarith [htheta.1])
        (show 0 ≤ jp-b/2+5*kappa eta by linarith)
      have hmul' := mul_nonneg (show 0 ≤ 4-theta by linarith [htheta.2]) hk.le
      nlinarith
  refine ⟨by linarith, by linarith, ?_⟩
  unfold kappa at *
  nlinarith

/-- The terminal beta difference protects the left endpoint before clipping. -/
theorem terminal_clearance {s S rb eta M L b betaS : ℝ}
    (heta : 0 < eta) (hM : 0 < M) (_hL : 0 < L)
    (hb : eta/4 ≤ b) (hbeta : betaS < kappa0 eta)
    (hdiff : b-betaS ≤ (S-s)*M)
    (hrb : rb*M ≤ kappa eta/100) (herror : M/L ≤ kappa eta/1000) :
    s + rb + 2/L < S := by
  have hbeta' : betaS < kappa eta/100 :=
    hbeta.trans_le (min_le_left _ _)
  have hsmall : (rb+2/L)*M ≤ kappa eta/100 + 2*(kappa eta/1000) := by
    have heq : (rb+2/L)*M = rb*M+2*(M/L) := by ring
    rw [heq]
    linarith
  have hstrict : (rb+2/L)*M < (S-s)*M := by
    unfold kappa at *
    linarith
  have := (mul_lt_mul_iff_left₀ hM).mp hstrict
  linarith

/-- Absolute endpoint errors for the two numerical quantities retained in the witness. -/
theorem endpoint_error_algebra {theta b b0 j j0 bp bp0 bt bt0 r e : ℝ}
    (htheta : theta ∈ Icc (3 : ℝ) 4) (_hr : 0 ≤ r) (he : 0 ≤ e)
    (hb : |b-b0| ≤ e) (hj : |j-j0| ≤ r+3*e)
    (hbp : |bp-bp0| ≤ 3*(r+3*e)) (hbt : |bt-bt0| ≤ r+2*e) :
    |(j-b/2)-(j0-b0/2)| ≤ r+4*e ∧
    |((theta+3)/2*b-bp-2*bt)-((theta+3)/2*b0-bp0-2*bt0)| ≤ 5*r+20*e := by
  obtain ⟨hblo, hbhi⟩ := abs_le.mp hb
  obtain ⟨hjlo, hjhi⟩ := abs_le.mp hj
  obtain ⟨hbplo, hbphi⟩ := abs_le.mp hbp
  obtain ⟨hbtlo, hbthi⟩ := abs_le.mp hbt
  have hmullo := mul_nonneg (show 0 ≤ theta+3 by linarith [htheta.1])
    (show 0 ≤ b-b0+e by linarith)
  have hmulhi := mul_nonneg (show 0 ≤ theta+3 by linarith [htheta.1])
    (show 0 ≤ e-(b-b0) by linarith)
  have heprod := mul_nonneg (show 0 ≤ 4-theta by linarith [htheta.2]) he
  constructor
  · apply abs_le.mpr
    constructor <;> linarith
  · apply abs_le.mpr
    constructor <;> nlinarith

end RiffleLowerV2.Witness
