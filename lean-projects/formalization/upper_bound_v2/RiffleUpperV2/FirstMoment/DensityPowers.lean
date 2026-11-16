import RiffleUpperV2.FirstMoment.TailCosts
import RiffleUpperV2.Localization.Eventual

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization

/-- Exact power representation of a finite class's mass/collision contribution. -/
theorem card_mean_tail_rpow {A : Type*} {k n d N : ℕ} (hN : 2 ≤ N)
    (cuts : Cuts k n d) (hn : 0 < n) (R : Finset (Fin n)) (x : Prefix k d)
    (hx : Legal cuts R x) (W : Finset A) (hW : W.Nonempty) (a : ℕ) :
    (W.card : ℝ)*anchoredMean cuts R x^4*tailSquareMass cuts x^2 =
      (N : ℝ)^(Real.log (W.card : ℝ)/logScale N+4*meanExponent N cuts R x-
        2*empiricalB N a cuts hn 2 (a+x.1.val) (a+d)) := by
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hc : 0<(W.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hW
  have hcard := rpow_normalizedExponent hN (W.card : ℝ) hc
  change (N : ℝ)^(Real.log (W.card : ℝ)/logScale N) = _ at hcard
  conv_lhs => rw [← hcard]
  rw [anchoredMean_rpow hN cuts R x hx,tailSquareMass_rpow hN cuts hn a x]
  rw [← Real.rpow_mul_natCast hNp.le,← Real.rpow_mul_natCast hNp.le,
    ← Real.rpow_add hNp,← Real.rpow_add hNp]
  congr 1
  push_cast
  ring

/-- The small-block density estimate in its exact original-scale exponent form. -/
theorem smallDensity_power {A : Type*} {k n d N : ℕ} (hN : 2 ≤ N)
    (cuts : Cuts k n d) (hn : 0 < n) (c₀ : ℤ) (R : Finset (Fin n))
    (x : Prefix k d) (hx : Legal cuts R x) (slots : Finset ℤ)
    (W : Finset A) (hW : W.Nonempty) (a : ℕ) {E : ℝ}
    (hE : Real.log (W.card : ℝ)/logScale N+4*meanExponent N cuts R x-
      2*empiricalB N a cuts hn 2 (a+x.1.val) (a+d) ≤ E) :
    (W.card : ℝ)*anchoredDensity cuts c₀ R x slots ≤ (N : ℝ)^E := by
  have h := smallDensity cuts c₀ R x slots
  have hmu : 0 ≤ anchoredMean cuts R x^4*tailSquareMass cuts x^2 := by positivity
  have hsmall : anchoredDensity cuts c₀ R x slots ≤ anchoredMean cuts R x^4*tailSquareMass cuts x^2 := by
    linarith
  calc
    _ ≤ (W.card : ℝ)*(anchoredMean cuts R x^4*tailSquareMass cuts x^2) :=
      mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg _)
    _ = _ := by rw [← mul_assoc,card_mean_tail_rpow hN cuts hn R x hx W hW a]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega)) hE

/-- The square-root smoothing factor is one inverse fluctuation power. -/
theorem smoothingFactor_power {k n d N : ℕ} (hN : 2 ≤ N) (cuts : Cuts k n d)
    (hn : 0 < n) (R : Finset (Fin n)) {g chi : ℝ} (hg : 0 < g)
    {y z v : Prefix k d} (hp : GenuineBoundaryPair cuts R chi y z v) :
    Real.sqrt (varianceDenominator chi v/(g*sideScale cuts R v)) =
      Real.sqrt (varianceDenominator chi v/g) /
        (N : ℝ)^(boundaryFluctuation N cuts R v) := by
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  rw [sideScale_eq_rpow N (by omega) cuts hn R hp]
  have hc := hp.chi_pos
  rw [← div_div,Real.sqrt_div (by unfold varianceDenominator; positivity)]
  congr 1
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul hNp.le]
  congr 1
  ring

/-- The actual large-block density, with the finite smoothing failure displayed
separately from the proved class exponent. -/
theorem largeDensity_power {A : Type*} {k n d N : ℕ} (hN : 2 ≤ N)
    (cuts : Cuts k n d) (hn : 2 ≤ n) (hd : 1 ≤ d) (c₀ : ℤ) (R : Finset (Fin n))
    {g chi : ℝ} (hg : Reserve R g) {y z v x : Prefix k d}
    (hp : GenuineBoundaryPair cuts R chi y z v) (hvx : IsPrefix v x) (hx : Legal cuts R x)
    (slots : Finset ℤ) (W : Finset A) (hW : W.Nonempty) (a : ℕ) {E : ℝ}
    (hE : Real.log (W.card : ℝ)/logScale N+4*meanExponent N cuts R x-
      boundaryFluctuation N cuts R v-2*empiricalB N a cuts (by omega) 2 (a+x.1.val) (a+d) ≤ E) :
    (W.card : ℝ)*anchoredDensity cuts c₀ R x slots ≤
      4*Real.sqrt (varianceDenominator chi v/g)*(N : ℝ)^E +
        (W.card : ℝ)*(6*(slots.card : ℝ)*
          Real.exp (-RiffleLowerV2.chernoffConstant*g*sideScale cuts R v)) := by
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have h := mul_le_mul_of_nonneg_left (largeDensity cuts hn hd c₀ R hg hp hvx slots)
    (Nat.cast_nonneg W.card : (0 : ℝ)≤W.card)
  rw [smoothingFactor_power hN cuts (by omega) R hg.1 hp] at h
  have heq : (W.card : ℝ)*(4*(Real.sqrt (varianceDenominator chi v/g)/
      (N : ℝ)^(boundaryFluctuation N cuts R v))*anchoredMean cuts R x^4*tailSquareMass cuts x^2) =
      4*Real.sqrt (varianceDenominator chi v/g)*
      (N : ℝ)^(Real.log (W.card : ℝ)/logScale N+4*meanExponent N cuts R x-
        boundaryFluctuation N cuts R v-2*empiricalB N a cuts (by omega) 2 (a+x.1.val) (a+d)) := by
    calc
      _ = 4*Real.sqrt (varianceDenominator chi v/g)*
        (((W.card : ℝ)*anchoredMean cuts R x^4*tailSquareMass cuts x^2)/
          (N : ℝ)^(boundaryFluctuation N cuts R v)) := by ring
      _ = _ := by
        rw [card_mean_tail_rpow hN cuts (by omega) R x hx W hW a,← Real.rpow_sub hNp]
        congr 2
        ring
  rw [mul_add,heq] at h
  have hm := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ)≤(N : ℝ) from by exact_mod_cast (show 1≤N by omega)) hE)
    (show 0≤4*Real.sqrt (varianceDenominator chi v/g) by positivity)
  exact h.trans (add_le_add hm le_rfl)

end RiffleUpperV2.FirstMoment
