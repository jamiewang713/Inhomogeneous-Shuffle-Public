import RiffleUpperV2.FirstMoment.GraphAssembly
import RiffleUpperV2.FirstMoment.CandidateCount
import RiffleUpperV2.FirstMoment.ActiveCount
import RiffleUpperV2.Shared.CountedRates

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization

/-- The actual number of omitted retained blocks is absorbed uniformly. -/
theorem retainedOmitted_eventually (k : ℕ) (hk : 0<k) (T delta epsilon M : ℝ)
    (hT : 0≤T) (hdelta : 0<delta) :
    ∃ N0 : ℕ, 2≤N0 ∧ ∀ N n d : ℕ, N0≤N → ∀ hN : 2≤N,
      ∀ (cuts : Cuts k n d) (hn : 0<n) (R : Fin k → Finset (Fin n))
        (C chi width : ℝ) (hchi : 0<chi) (hchi1 : chi≤1)
        (hchiK : chi≤1/(k : ℝ)) (hwidth : 0<width) (hd : (d : ℝ)≤T*logScale N),
      ((retainedClasses hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd).card : ℝ)≤
        (N : ℝ)^epsilon →
      (Fintype.card (RetainedAtPile hk N cuts hn R C chi delta hchiK) : ℝ)*
        Real.exp (-(N : ℝ)^(delta/16))≤(N : ℝ)^(-M) := by
  obtain ⟨N0,hN0,h⟩ := countedWindowError_power_rate k hk T delta epsilon M hT hdelta
  refine ⟨N0,hN0,?_⟩
  intro N n d hNN hN cuts hn R C chi width hchi hchi1 hchiK hwidth hd hc
  have hcard : (Fintype.card (RetainedAtPile hk N cuts hn R C chi delta hchiK) : ℝ)≤
      ((retainedClasses hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd).card : ℝ)*
        (((d : ℝ)+1)*(k : ℝ)^d) := by
    exact_mod_cast retainedCandidate_count hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd
  calc
    _ ≤ ((N : ℝ)^epsilon*(((d : ℝ)+1)*(k : ℝ)^d))*Real.exp (-(N : ℝ)^(delta/16)) :=
      mul_le_mul_of_nonneg_right (hcard.trans (mul_le_mul_of_nonneg_right hc (by positivity)))
        (Real.exp_pos _).le
    _ ≤ _ := h N d hNN hd

/-- The two concrete graph-error terms fit inside one inverse power. -/
theorem graphError_power_bound {N n k : ℕ} (hN : 2≤N) (hnN : n≤N)
    (eta z : ℝ) (heta : 0<eta) (hz : 0≤z) (hzbound : z≤(N : ℝ)^(-(eta+4)))
    (hkN : 4*((k : ℝ)^2+1)≤N) :
    4*(k : ℝ)^2*(N : ℝ)^(-(eta+4))+4*(n-1 : ℕ)*z^2≤(N : ℝ)^(-eta) := by
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hNone : (1 : ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hr0 := Real.rpow_nonneg hNp.le (-(eta+4))
  have hr1 : (N : ℝ)^(-(eta+4))≤1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hNone (by linarith : -(eta+4)≤0)
  have hzs : z^2≤(N : ℝ)^(-(eta+4)) := by
    have hz1 := hzbound.trans hr1
    nlinarith
  have hn : ((n-1 : ℕ) : ℝ)≤N := by exact_mod_cast (show n-1≤N by omega)
  have hcoeff : 4*((k : ℝ)^2+(N : ℝ))≤(N : ℝ)^2 := by
    have h := mul_le_mul_of_nonneg_right hkN hNp.le
    nlinarith [sq_nonneg (k : ℝ)]
  calc
    _ ≤ 4*(k : ℝ)^2*(N : ℝ)^(-(eta+4))+4*(N : ℝ)*(N : ℝ)^(-(eta+4)) := by
      apply add_le_add le_rfl
      exact mul_le_mul (mul_le_mul_of_nonneg_left hn (by norm_num)) hzs
        (sq_nonneg z) (by positivity)
    _ = (4*((k : ℝ)^2+(N : ℝ)))*(N : ℝ)^(-(eta+4)) := by ring
    _ ≤ (N : ℝ)^2*(N : ℝ)^(-(eta+4)) := mul_le_mul_of_nonneg_right hcoeff hr0
    _ = (N : ℝ)^(-eta-2) := by
      rw [← Real.rpow_natCast,← Real.rpow_add hNp]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNone (by linarith)

end RiffleUpperV2.FirstMoment
