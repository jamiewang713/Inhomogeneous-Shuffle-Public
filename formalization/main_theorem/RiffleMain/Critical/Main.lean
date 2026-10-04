import RiffleMain.Critical.Nondegenerate

set_option autoImplicit false

/-! The complete scalar critical-time bridge, with the infinite case retained. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RiffleMain.Critical
open TimeProfile RiffleUpperV2

theorem cutoff_times {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    (hI : LocallyScalarIntegrable μ) (hfinite : criticalTime μ ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    0 < (1-ε) * (criticalTime μ).toReal ∧
    ENNReal.ofReal ((1-ε) * (criticalTime μ).toReal) < criticalTime μ ∧
    criticalTime μ < ENNReal.ofReal ((1+ε) * (criticalTime μ).toReal) := by
  have hreal : ENNReal.ofReal (criticalTime μ).toReal = criticalTime μ :=
    ENNReal.ofReal_toReal hfinite
  have hC : 0 < (criticalTime μ).toReal :=
    ENNReal.ofReal_pos.mp (by simpa only [hreal] using criticalTime_pos hk hI)
  have hεC := mul_pos hε hC
  have hl : (1-ε) * (criticalTime μ).toReal < (criticalTime μ).toReal := by nlinarith
  have hu : (criticalTime μ).toReal < (1+ε) * (criticalTime μ).toReal := by nlinarith
  refine ⟨mul_pos (sub_pos.mpr hε1) hC, ?_, ?_⟩
  · calc
      _ < ENNReal.ofReal (criticalTime μ).toReal := ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hl, hC⟩
      _ = criticalTime μ := hreal
  · calc
      criticalTime μ = ENNReal.ofReal (criticalTime μ).toReal := hreal.symm
      _ < _ := ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hu, hC.trans hu⟩

end RiffleMain.Critical
