import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Finite numerical first-moment bounds

This module implements N01–N10 of the frozen time-profile contract.
All losses are explicit. The hypotheses are finite numerical inequalities;
this module does not infer profile convergence or properties of time integrals.
-/

namespace TimeProfile

noncomputable section

def largeObjective (beta : ℝ) (B : ℝ → ℝ) (D theta : ℝ) : ℝ :=
  ((theta + 3) / 2) * beta - B theta - 2 * D

def smallObjective (beta : ℝ) (B : ℝ → ℝ) (D theta : ℝ) : ℝ :=
  ((theta - 1) / 2) * beta - B theta - 2 * D

def largeLoss (eL eF eBeta delta eH eE : ℝ) : ℝ :=
  4 * eL + eF + (7 / 2) * eBeta + delta + eH + 2 * eE

def smallLoss (eBeta eF eS eH eE : ℝ) : ℝ :=
  (3 / 2) * eBeta + 5 * eF + 4 * eS + eH + 2 * eE

/-- N01: the large exponent bound with the frozen explicit loss. -/
theorem large_numerical_core
    {Lx Lv F E H S Q beta D theta eL eF eBeta delta eH eE : ℝ}
    {B : ℝ → ℝ}
    (htheta : theta ∈ Set.Icc (3 : ℝ) 4)
    (heL : 0 ≤ eL) (heF : 0 ≤ eF) (heBeta : 0 ≤ eBeta)
    (hdelta : 0 ≤ delta) (_heH : 0 ≤ eH) (_heE : 0 ≤ eE)
    (hmass : Lx ≤ Lv - S - Q + eL)
    (hQ : 0 ≤ Q) (hstable : Lx - F ≤ delta)
    (hfluc : Lv / 2 - eF ≤ F) (hmax : Lv ≤ beta + eBeta)
    (hentropy : H ≤ theta * S - B theta + eH)
    (htail : E ≤ -D + eE) :
    4 * Lx - F + 2 * E + H ≤
      largeObjective beta B D theta + largeLoss eL eF eBeta delta eH eE := by
  have ht0 : 0 ≤ theta := by linarith [htheta.1]
  have hm := mul_le_mul_of_nonneg_left hmass ht0
  have hq := mul_nonneg ht0 hQ
  have hs := mul_le_mul_of_nonneg_left hstable (show 0 ≤ 4 - theta by
    linarith [htheta.2])
  have hf := mul_le_mul_of_nonneg_left hfluc (show 0 ≤ theta - 3 by
    linarith [htheta.1])
  have hb := mul_le_mul_of_nonneg_left hmax (show 0 ≤ (theta + 3) / 2 by
    linarith [htheta.1])
  have hel := mul_nonneg (show 0 ≤ 4 - theta by linarith [htheta.2]) heL
  have hef := mul_nonneg (show 0 ≤ 4 - theta by linarith [htheta.2]) heF
  have heb := mul_nonneg (show 0 ≤ 4 - theta by linarith [htheta.2]) heBeta
  have hed := mul_nonneg (show 0 ≤ theta - 3 by linarith [htheta.1]) hdelta
  unfold largeObjective largeLoss
  nlinarith

/-- N02: the small nonsingleton exponent bound with the frozen explicit loss. -/
theorem small_numerical_core
    {Lv F E H S beta D theta eBeta eF eS eH eE : ℝ} {B : ℝ → ℝ}
    (htheta : theta ∈ Set.Icc (3 : ℝ) 4)
    (heBeta : 0 ≤ eBeta) (heF : 0 ≤ eF) (heS : 0 ≤ eS)
    (_heH : 0 ≤ eH) (_heE : 0 ≤ eE)
    (hparent : S ≤ Lv - F + eS)
    (hfluc : Lv / 2 - eF ≤ F) (hmax : Lv ≤ beta + eBeta)
    (hentropy : H ≤ theta * S - B theta + eH)
    (htail : E ≤ -D + eE) :
    -F + 2 * E + H ≤
      smallObjective beta B D theta + smallLoss eBeta eF eS eH eE := by
  have ht0 : 0 ≤ theta := by linarith [htheta.1]
  have hp := mul_le_mul_of_nonneg_left hparent ht0
  have hf := mul_le_mul_of_nonneg_left hfluc (show 0 ≤ theta + 1 by
    linarith [htheta.1])
  have hb := mul_le_mul_of_nonneg_left hmax (show 0 ≤ (theta - 1) / 2 by
    linarith [htheta.1])
  have heb := mul_nonneg (show 0 ≤ 4 - theta by linarith [htheta.2]) heBeta
  have hef := mul_nonneg (show 0 ≤ 4 - theta by linarith [htheta.2]) heF
  have hes := mul_nonneg (show 0 ≤ 4 - theta by linarith [htheta.2]) heS
  unfold smallObjective smallLoss
  nlinarith

/-- N03: the singleton exponent is controlled by its two errors. -/
theorem singleton_numerical_core
    {Lv E beta D eBeta eE : ℝ}
    (_heBeta : 0 ≤ eBeta) (_heE : 0 ≤ eE)
    (hmax : Lv ≤ beta + eBeta) (htail : E ≤ -D + eE) :
    Lv + E ≤ beta - D + eBeta + eE := by
  linarith

/-- N04: the pointwise estimate supplies the required lower bound for the infimum. -/
theorem numerical_le_infimum_add
    {g : ℝ → ℝ} {X e : ℝ}
    (h : ∀ theta ∈ Set.Icc (3 : ℝ) 4, X ≤ g theta + e) :
    X ≤ sInf (g '' Set.Icc (3 : ℝ) 4) + e := by
  have hne : (g '' Set.Icc (3 : ℝ) 4).Nonempty :=
    ⟨g 3, ⟨3, by norm_num, rfl⟩⟩
  have hlower : ∀ y ∈ g '' Set.Icc (3 : ℝ) 4, X - e ≤ y := by
    rintro y ⟨theta, htheta, rfl⟩
    linarith [h theta htheta]
  have hbounded : BddBelow (g '' Set.Icc (3 : ℝ) 4) :=
    ⟨X - e, hlower⟩
  have hinf : X - e ≤ sInf (g '' Set.Icc (3 : ℝ) 4) := le_csInf hne hlower
  linarith

/-- N05: a first numerical margin and its loss budget imply a negative large exponent. -/
theorem large_numerical_margin
    {Lx Lv F E H S Q beta D eL eF eBeta delta eH eE eta : ℝ}
    {B : ℝ → ℝ}
    (heL : 0 ≤ eL) (heF : 0 ≤ eF) (heBeta : 0 ≤ eBeta)
    (hdelta : 0 ≤ delta) (heH : 0 ≤ eH) (heE : 0 ≤ eE)
    (hmass : Lx ≤ Lv - S - Q + eL)
    (hQ : 0 ≤ Q) (hstable : Lx - F ≤ delta)
    (hfluc : Lv / 2 - eF ≤ F) (hmax : Lv ≤ beta + eBeta)
    (hentropy : ∀ theta ∈ Set.Icc (3 : ℝ) 4, H ≤ theta * S - B theta + eH)
    (htail : E ≤ -D + eE)
    (hmargin : sInf (largeObjective beta B D '' Set.Icc (3 : ℝ) 4) ≤ -eta)
    (_heta : 0 < eta)
    (hbudget : largeLoss eL eF eBeta delta eH eE ≤ eta / 2) :
    4 * Lx - F + 2 * E + H ≤ -eta / 2 := by
  have hp : ∀ theta ∈ Set.Icc (3 : ℝ) 4,
      4 * Lx - F + 2 * E + H ≤
        largeObjective beta B D theta + largeLoss eL eF eBeta delta eH eE := by
    intro theta htheta
    exact large_numerical_core htheta heL heF heBeta hdelta heH heE
      hmass hQ hstable hfluc hmax (hentropy theta htheta) htail
  have hi := numerical_le_infimum_add hp
  linarith

/-- N06: a second numerical margin and its loss budget imply a negative small exponent. -/
theorem small_numerical_margin
    {Lv F E H S beta D eBeta eF eS eH eE eta : ℝ} {B : ℝ → ℝ}
    (heBeta : 0 ≤ eBeta) (heF : 0 ≤ eF) (heS : 0 ≤ eS)
    (heH : 0 ≤ eH) (heE : 0 ≤ eE)
    (hparent : S ≤ Lv - F + eS)
    (hfluc : Lv / 2 - eF ≤ F) (hmax : Lv ≤ beta + eBeta)
    (hentropy : ∀ theta ∈ Set.Icc (3 : ℝ) 4, H ≤ theta * S - B theta + eH)
    (htail : E ≤ -D + eE)
    (hmargin : sInf (smallObjective beta B D '' Set.Icc (3 : ℝ) 4) ≤ -eta)
    (_heta : 0 < eta)
    (hbudget : smallLoss eBeta eF eS eH eE ≤ eta / 2) :
    -F + 2 * E + H ≤ -eta / 2 := by
  have hp : ∀ theta ∈ Set.Icc (3 : ℝ) 4,
      -F + 2 * E + H ≤
        smallObjective beta B D theta + smallLoss eBeta eF eS eH eE := by
    intro theta htheta
    exact small_numerical_core htheta heBeta heF heS heH heE
      hparent hfluc hmax (hentropy theta htheta) htail
  have hi := numerical_le_infimum_add hp
  linarith

/-- N07: the third numerical margin controls a singleton. -/
theorem singleton_numerical_margin
    {Lv E beta D eBeta eE eta : ℝ}
    (heBeta : 0 ≤ eBeta) (heE : 0 ≤ eE)
    (hmax : Lv ≤ beta + eBeta) (htail : E ≤ -D + eE)
    (hmargin : beta - D ≤ -eta) (_heta : 0 < eta)
    (hbudget : eBeta + eE ≤ eta / 2) :
    Lv + E ≤ -eta / 2 := by
  have h := singleton_numerical_core heBeta heE hmax htail
  linarith

/-- N08: a terminal mass budget excludes the nonterminal fallback condition. -/
theorem no_terminal_fallback
    {Lx F eta eT eF delta : ℝ}
    (_heT : 0 ≤ eT) (_heF : 0 ≤ eF)
    (hmass : Lx ≤ -eta + eT) (hfluc : Lx / 2 - eF ≤ F)
    (hbudget : eT + 2 * eF ≤ eta) (hdelta : 0 < delta) :
    Lx - F < delta := by
  linarith

/-- N09: the common error envelope for the large branch. -/
theorem large_loss_of_common_error
    {eL eF eBeta delta eH eE epsilon : ℝ}
    (heL : eL ∈ Set.Icc 0 epsilon) (heF : eF ∈ Set.Icc 0 epsilon)
    (heBeta : eBeta ∈ Set.Icc 0 epsilon) (hdelta : delta ∈ Set.Icc 0 epsilon)
    (heH : eH ∈ Set.Icc 0 epsilon) (heE : eE ∈ Set.Icc 0 epsilon) :
    largeLoss eL eF eBeta delta eH eE ≤ 25 * epsilon / 2 ∧
      25 * epsilon / 2 ≤ 14 * epsilon := by
  unfold largeLoss
  constructor
  · linarith [heL.2, heF.2, heBeta.2, hdelta.2, heH.2, heE.2]
  · linarith [heL.1, heL.2]

/-- N09: the common error envelope for the small branch. -/
theorem small_loss_of_common_error
    {eBeta eF eS eH eE epsilon : ℝ}
    (heBeta : eBeta ∈ Set.Icc 0 epsilon) (heF : eF ∈ Set.Icc 0 epsilon)
    (heS : eS ∈ Set.Icc 0 epsilon) (heH : eH ∈ Set.Icc 0 epsilon)
    (heE : eE ∈ Set.Icc 0 epsilon) :
    smallLoss eBeta eF eS eH eE ≤ 27 * epsilon / 2 ∧
      27 * epsilon / 2 ≤ 14 * epsilon := by
  unfold smallLoss
  constructor
  · linarith [heBeta.2, heF.2, heS.2, heH.2, heE.2]
  · linarith [heBeta.1, heBeta.2]

/-- N09: the common error envelope for a singleton. -/
theorem singleton_loss_of_common_error
    {eBeta eE epsilon : ℝ}
    (heBeta : eBeta ∈ Set.Icc 0 epsilon) (heE : eE ∈ Set.Icc 0 epsilon) :
    eBeta + eE ≤ 2 * epsilon := by
  linarith [heBeta.2, heE.2]

/-- N09: the large margin with the explicit epsilon <= eta/28 choice. -/
theorem large_numerical_margin_of_common_error
    {Lx Lv F E H S Q beta D eL eF eBeta delta eH eE eta epsilon : ℝ}
    {B : ℝ → ℝ}
    (heL : eL ∈ Set.Icc 0 epsilon) (heF : eF ∈ Set.Icc 0 epsilon)
    (heBeta : eBeta ∈ Set.Icc 0 epsilon) (hdelta : delta ∈ Set.Icc 0 epsilon)
    (heH : eH ∈ Set.Icc 0 epsilon) (heE : eE ∈ Set.Icc 0 epsilon)
    (hmass : Lx ≤ Lv - S - Q + eL)
    (hQ : 0 ≤ Q) (hstable : Lx - F ≤ delta)
    (hfluc : Lv / 2 - eF ≤ F) (hmax : Lv ≤ beta + eBeta)
    (hentropy : ∀ theta ∈ Set.Icc (3 : ℝ) 4, H ≤ theta * S - B theta + eH)
    (htail : E ≤ -D + eE)
    (hmargin : sInf (largeObjective beta B D '' Set.Icc (3 : ℝ) 4) ≤ -eta)
    (heta : 0 < eta) (hchoice : epsilon ≤ eta / 28) :
    4 * Lx - F + 2 * E + H ≤ -eta / 2 := by
  have hloss := large_loss_of_common_error heL heF heBeta hdelta heH heE
  apply large_numerical_margin heL.1 heF.1 heBeta.1 hdelta.1 heH.1 heE.1
    hmass hQ hstable hfluc hmax hentropy htail hmargin heta
  linarith [hloss.1, hloss.2]

/-- N09: the small margin with the explicit epsilon <= eta/28 choice. -/
theorem small_numerical_margin_of_common_error
    {Lv F E H S beta D eBeta eF eS eH eE eta epsilon : ℝ} {B : ℝ → ℝ}
    (heBeta : eBeta ∈ Set.Icc 0 epsilon) (heF : eF ∈ Set.Icc 0 epsilon)
    (heS : eS ∈ Set.Icc 0 epsilon) (heH : eH ∈ Set.Icc 0 epsilon)
    (heE : eE ∈ Set.Icc 0 epsilon)
    (hparent : S ≤ Lv - F + eS)
    (hfluc : Lv / 2 - eF ≤ F) (hmax : Lv ≤ beta + eBeta)
    (hentropy : ∀ theta ∈ Set.Icc (3 : ℝ) 4, H ≤ theta * S - B theta + eH)
    (htail : E ≤ -D + eE)
    (hmargin : sInf (smallObjective beta B D '' Set.Icc (3 : ℝ) 4) ≤ -eta)
    (heta : 0 < eta) (hchoice : epsilon ≤ eta / 28) :
    -F + 2 * E + H ≤ -eta / 2 := by
  have hloss := small_loss_of_common_error heBeta heF heS heH heE
  apply small_numerical_margin heBeta.1 heF.1 heS.1 heH.1 heE.1
    hparent hfluc hmax hentropy htail hmargin heta
  linarith [hloss.1, hloss.2]

/-- N09: the singleton margin under the same explicit error choice. -/
theorem singleton_numerical_margin_of_common_error
    {Lv E beta D eBeta eE eta epsilon : ℝ}
    (heBeta : eBeta ∈ Set.Icc 0 epsilon) (heE : eE ∈ Set.Icc 0 epsilon)
    (hmax : Lv ≤ beta + eBeta) (htail : E ≤ -D + eE)
    (hmargin : beta - D ≤ -eta) (heta : 0 < eta)
    (hchoice : epsilon ≤ eta / 28) :
    Lv + E ≤ -eta / 2 := by
  have hloss := singleton_loss_of_common_error heBeta heE
  apply singleton_numerical_margin heBeta.1 heE.1 hmax htail hmargin heta
  linarith

/-- N10: uniform large-branch hypotheses retain their exact threshold N0. -/
theorem large_numerical_margin_uniform
    {ι : ℕ → Type*} {allowed : (N : ℕ) → Set (ι N)}
    {Lx Lv F E H S Q beta D eL eF eBeta delta eH eE : (N : ℕ) → ι N → ℝ}
    {B : (N : ℕ) → ι N → ℝ → ℝ} {eta : ℝ} {N0 : ℕ}
    (heta : 0 < eta)
    (h : ∀ N, N0 ≤ N → ∀ x ∈ allowed N,
      0 ≤ eL N x ∧ 0 ≤ eF N x ∧ 0 ≤ eBeta N x ∧
      0 ≤ delta N x ∧ 0 ≤ eH N x ∧ 0 ≤ eE N x ∧
      Lx N x ≤ Lv N x - S N x - Q N x + eL N x ∧
      0 ≤ Q N x ∧ Lx N x - F N x ≤ delta N x ∧
      Lv N x / 2 - eF N x ≤ F N x ∧ Lv N x ≤ beta N x + eBeta N x ∧
      (∀ theta ∈ Set.Icc (3 : ℝ) 4,
        H N x ≤ theta * S N x - B N x theta + eH N x) ∧
      E N x ≤ -D N x + eE N x ∧
      sInf (largeObjective (beta N x) (B N x) (D N x) '' Set.Icc (3 : ℝ) 4) ≤
        -eta ∧
      largeLoss (eL N x) (eF N x) (eBeta N x) (delta N x) (eH N x) (eE N x) ≤
        eta / 2) :
    ∀ N, N0 ≤ N → ∀ x ∈ allowed N,
      4 * Lx N x - F N x + 2 * E N x + H N x ≤ -eta / 2 := by
  intro N hN x hx
  obtain ⟨heL, heF, heBeta, hdelta, heH, heE, hmass, hQ, hstable, hfluc,
    hmax, hentropy, htail, hmargin, hbudget⟩ := h N hN x hx
  exact large_numerical_margin heL heF heBeta hdelta heH heE
    hmass hQ hstable hfluc hmax hentropy htail hmargin heta hbudget

/-- N10: uniform small-branch hypotheses retain their exact threshold N0. -/
theorem small_numerical_margin_uniform
    {ι : ℕ → Type*} {allowed : (N : ℕ) → Set (ι N)}
    {Lv F E H S beta D eBeta eF eS eH eE : (N : ℕ) → ι N → ℝ}
    {B : (N : ℕ) → ι N → ℝ → ℝ} {eta : ℝ} {N0 : ℕ}
    (heta : 0 < eta)
    (h : ∀ N, N0 ≤ N → ∀ x ∈ allowed N,
      0 ≤ eBeta N x ∧ 0 ≤ eF N x ∧ 0 ≤ eS N x ∧ 0 ≤ eH N x ∧ 0 ≤ eE N x ∧
      S N x ≤ Lv N x - F N x + eS N x ∧
      Lv N x / 2 - eF N x ≤ F N x ∧ Lv N x ≤ beta N x + eBeta N x ∧
      (∀ theta ∈ Set.Icc (3 : ℝ) 4,
        H N x ≤ theta * S N x - B N x theta + eH N x) ∧
      E N x ≤ -D N x + eE N x ∧
      sInf (smallObjective (beta N x) (B N x) (D N x) '' Set.Icc (3 : ℝ) 4) ≤
        -eta ∧
      smallLoss (eBeta N x) (eF N x) (eS N x) (eH N x) (eE N x) ≤ eta / 2) :
    ∀ N, N0 ≤ N → ∀ x ∈ allowed N,
      -F N x + 2 * E N x + H N x ≤ -eta / 2 := by
  intro N hN x hx
  obtain ⟨heBeta, heF, heS, heH, heE, hparent, hfluc, hmax, hentropy, htail,
    hmargin, hbudget⟩ := h N hN x hx
  exact small_numerical_margin heBeta heF heS heH heE
    hparent hfluc hmax hentropy htail hmargin heta hbudget

/-- N10: uniform singleton hypotheses retain their exact threshold N0. -/
theorem singleton_numerical_margin_uniform
    {ι : ℕ → Type*} {allowed : (N : ℕ) → Set (ι N)}
    {Lv E beta D eBeta eE : (N : ℕ) → ι N → ℝ} {eta : ℝ} {N0 : ℕ}
    (heta : 0 < eta)
    (h : ∀ N, N0 ≤ N → ∀ x ∈ allowed N,
      0 ≤ eBeta N x ∧ 0 ≤ eE N x ∧
      Lv N x ≤ beta N x + eBeta N x ∧ E N x ≤ -D N x + eE N x ∧
      beta N x - D N x ≤ -eta ∧ eBeta N x + eE N x ≤ eta / 2) :
    ∀ N, N0 ≤ N → ∀ x ∈ allowed N, Lv N x + E N x ≤ -eta / 2 := by
  intro N hN x hx
  obtain ⟨heBeta, heE, hmax, htail, hmargin, hbudget⟩ := h N hN x hx
  exact singleton_numerical_margin heBeta heE hmax htail hmargin heta hbudget

end

end TimeProfile
