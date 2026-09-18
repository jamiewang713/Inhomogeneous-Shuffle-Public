import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-!
The frozen scalar part of the time-inhomogeneous first-moment argument.
The model-to-scalar estimates are deliberately explicit premises. No
homogeneous cutoff identity or unproved model theorem is used here.
See `FROZEN_CONTRACT.md`, interfaces 1–10.
-/

noncomputable section

namespace InhomogeneousShuffle.FirstMoment

def thetaRange : Set ℝ := Set.Icc 3 4

def largeIntegrand (beta : ℝ) (B : ℝ → ℝ) (D theta : ℝ) : ℝ :=
  ((theta + 3) / 2) * beta - B theta - 2 * D

def smallIntegrand (beta : ℝ) (B : ℝ → ℝ) (D theta : ℝ) : ℝ :=
  ((theta - 1) / 2) * beta - B theta - 2 * D

def thetaInf (f : ℝ → ℝ) : ℝ := sInf (f '' thetaRange)

theorem le_thetaInf_add {X z : ℝ} {f : ℝ → ℝ}
    (h : ∀ theta ∈ thetaRange, X ≤ f theta + z) :
    X ≤ thetaInf f + z := by
  have hne : (f '' thetaRange).Nonempty :=
    ⟨f 3, 3, by norm_num [thetaRange], rfl⟩
  have hlower : X - z ≤ thetaInf f := by
    apply le_csInf hne
    rintro _ ⟨theta, htheta, rfl⟩
    exact sub_le_iff_le_add.mpr (h theta htheta)
  linarith

theorem variational_margin {X z eta : ℝ} {f : ℝ → ℝ}
    (h : ∀ theta ∈ thetaRange, X ≤ f theta + z)
    (hmargin : thetaInf f ≤ -eta) :
    X ≤ -eta + z := by
  have := le_thetaInf_add h
  linarith

theorem large_exponent_pointwise
    {L V F E H S Q beta D e delta theta : ℝ} {B : ℝ → ℝ}
    (he : 0 ≤ e) (hdelta : 0 ≤ delta)
    (htheta3 : 3 ≤ theta) (htheta4 : theta ≤ 4)
    (hQ : 0 ≤ Q) (hlen : L ≤ V - S - Q + e)
    (hstable : L - F ≤ delta) (hfluc : V / 2 - e ≤ F)
    (hmax : V ≤ beta + e) (hentropy : H ≤ theta * S - B theta + e)
    (htail : E ≤ -D + e) :
    4 * L - F + 2 * E + H ≤ largeIntegrand beta B D theta + 12 * e + delta := by
  have ht : 0 ≤ theta := by linarith
  have hlen' : L + S + Q ≤ V + e := by linarith
  have h1 := mul_le_mul_of_nonneg_left hlen' ht
  have h2 := mul_le_mul_of_nonneg_left hstable (show 0 ≤ 4 - theta by linarith)
  have h3 := mul_le_mul_of_nonneg_left hfluc (show 0 ≤ theta - 3 by linarith)
  have h4 := mul_le_mul_of_nonneg_left hmax (show 0 ≤ (theta + 3) / 2 by linarith)
  have h5 := mul_nonneg ht hQ
  have h6 := mul_nonneg (show 0 ≤ 4 - theta by linarith) he
  have h7 := mul_nonneg (show 0 ≤ theta - 3 by linarith) hdelta
  unfold largeIntegrand
  nlinarith

theorem small_exponent_pointwise
    {V F E H S beta D e theta : ℝ} {B : ℝ → ℝ}
    (he : 0 ≤ e) (htheta3 : 3 ≤ theta) (htheta4 : theta ≤ 4)
    (hparent : S ≤ V - F + e) (hfluc : V / 2 - e ≤ F)
    (hmax : V ≤ beta + e) (hentropy : H ≤ theta * S - B theta + e)
    (htail : E ≤ -D + e) :
    -F + 2 * E + H ≤ smallIntegrand beta B D theta + 14 * e := by
  have h1 := mul_le_mul_of_nonneg_left hparent (show 0 ≤ theta by linarith)
  have h2 := mul_le_mul_of_nonneg_left hfluc (show 0 ≤ theta + 1 by linarith)
  have h3 := mul_le_mul_of_nonneg_left hmax (show 0 ≤ (theta - 1) / 2 by linarith)
  have h4 := mul_nonneg (show 0 ≤ 4 - theta by linarith) he
  unfold smallIntegrand
  nlinarith

theorem singleton_exponent {V E beta D e : ℝ}
    (hmax : V ≤ beta + e) (htail : E ≤ -D + e) :
    V + E ≤ beta - D + 2 * e := by
  linarith

theorem large_exponent_variational
    {L V F E H S Q beta D e delta eta : ℝ} {B : ℝ → ℝ}
    (he : 0 ≤ e) (hdelta : 0 ≤ delta)
    (hQ : 0 ≤ Q) (hlen : L ≤ V - S - Q + e)
    (hstable : L - F ≤ delta) (hfluc : V / 2 - e ≤ F)
    (hmax : V ≤ beta + e)
    (hentropy : ∀ theta ∈ thetaRange, H ≤ theta * S - B theta + e)
    (htail : E ≤ -D + e)
    (hmargin : thetaInf (largeIntegrand beta B D) ≤ -eta) :
    4 * L - F + 2 * E + H ≤ -eta + 12 * e + delta := by
  have hpoint : ∀ theta ∈ thetaRange,
      4 * L - F + 2 * E + H ≤ largeIntegrand beta B D theta + (12 * e + delta) := by
    intro theta htheta
    have h := large_exponent_pointwise he hdelta htheta.1 htheta.2
      hQ hlen hstable hfluc hmax (hentropy theta htheta) htail
    linarith
  have h := variational_margin hpoint hmargin
  linarith

theorem small_exponent_variational
    {V F E H S beta D e eta : ℝ} {B : ℝ → ℝ}
    (he : 0 ≤ e) (hparent : S ≤ V - F + e) (hfluc : V / 2 - e ≤ F)
    (hmax : V ≤ beta + e)
    (hentropy : ∀ theta ∈ thetaRange, H ≤ theta * S - B theta + e)
    (htail : E ≤ -D + e)
    (hmargin : thetaInf (smallIntegrand beta B D) ≤ -eta) :
    -F + 2 * E + H ≤ -eta + 14 * e := by
  apply variational_margin (f := smallIntegrand beta B D) ?_ hmargin
  intro theta htheta
  exact small_exponent_pointwise he htheta.1 htheta.2 hparent hfluc hmax
    (hentropy theta htheta) htail

theorem large_exponent_negative
    {L V F E H S Q beta D e delta eta : ℝ} {B : ℝ → ℝ}
    (he : 0 ≤ e) (hdelta : 0 ≤ delta)
    (hQ : 0 ≤ Q) (hlen : L ≤ V - S - Q + e)
    (hstable : L - F ≤ delta) (hfluc : V / 2 - e ≤ F)
    (hmax : V ≤ beta + e)
    (hentropy : ∀ theta ∈ thetaRange, H ≤ theta * S - B theta + e)
    (htail : E ≤ -D + e)
    (hmargin : thetaInf (largeIntegrand beta B D) ≤ -eta)
    (_heta : 0 < eta) (hbudget : 12 * e + delta ≤ 3 * eta / 4) :
    4 * L - F + 2 * E + H ≤ -eta / 4 := by
  have h := large_exponent_variational he hdelta hQ hlen hstable hfluc hmax
    hentropy htail hmargin
  linarith

theorem small_exponent_negative
    {V F E H S beta D e eta : ℝ} {B : ℝ → ℝ}
    (he : 0 ≤ e) (hparent : S ≤ V - F + e) (hfluc : V / 2 - e ≤ F)
    (hmax : V ≤ beta + e)
    (hentropy : ∀ theta ∈ thetaRange, H ≤ theta * S - B theta + e)
    (htail : E ≤ -D + e)
    (hmargin : thetaInf (smallIntegrand beta B D) ≤ -eta)
    (_heta : 0 < eta) (hbudget : 14 * e ≤ 3 * eta / 4) :
    -F + 2 * E + H ≤ -eta / 4 := by
  have h := small_exponent_variational he hparent hfluc hmax hentropy htail hmargin
  linarith

theorem singleton_exponent_negative {V E beta D e eta : ℝ}
    (hmax : V ≤ beta + e) (htail : E ≤ -D + e)
    (hmargin : beta - D ≤ -eta) (_heta : 0 < eta) (hbudget : 2 * e ≤ 3 * eta / 4) :
    V + E ≤ -eta / 4 := by
  have h := singleton_exponent hmax htail
  linarith

end InhomogeneousShuffle.FirstMoment
