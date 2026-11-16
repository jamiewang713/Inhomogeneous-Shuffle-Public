import RiffleMain.Profile.Integrability

set_option autoImplicit false

noncomputable section
open Set MeasureTheory
namespace RiffleMain.Profile
open TimeProfile

/-- The domain on which the manuscript specifies the time profile. -/
abbrev NonnegativeTimeLaw (k : ℕ) := Ici (0 : ℝ) → ProbabilityMeasure (Simplex k)

/-- Exactly the manuscript's Borel evaluation measurability on `t ≥ 0`. -/
def NonnegativeMeasurableProfile {k : ℕ} (μ : NonnegativeTimeLaw k) : Prop :=
  ∀ s : Set (Simplex k), MeasurableSet s →
    Measurable (fun t : Ici (0 : ℝ) => (μ t : Measure (Simplex k)) s)

/-- Extend by the time-zero law on negative times so that existing interval
integral APIs can keep their domain `ℝ`. -/
def extendNonnegativeProfile {k : ℕ} (μ : NonnegativeTimeLaw k) : TimeLaw k :=
  fun t => μ ⟨max t 0, mem_Ici.mpr (le_max_right t 0)⟩

@[simp] theorem extendNonnegativeProfile_at {k : ℕ} (μ : NonnegativeTimeLaw k)
    (t : Ici (0 : ℝ)) : extendNonnegativeProfile μ t = μ t := by
  unfold extendNonnegativeProfile
  congr 1
  apply Subtype.ext
  exact max_eq_left (mem_Ici.mp t.property)

theorem extendNonnegativeProfile_measurable {k : ℕ} {μ : NonnegativeTimeLaw k}
    (hμ : NonnegativeMeasurableProfile μ) : MeasurableProfile (extendNonnegativeProfile μ) := by
  intro s hs
  have hm : Measurable (fun t : ℝ =>
      (⟨max t 0, mem_Ici.mpr (le_max_right t 0)⟩ : Ici (0 : ℝ))) :=
    (measurable_id.max measurable_const).subtype_mk
  exact (hμ s hs).comp hm

/-- Restricting a globally represented family recovers the exact domain used
by the manuscript. -/
def restrictNonnegativeProfile {k : ℕ} (μ : TimeLaw k) : NonnegativeTimeLaw k :=
  fun t => μ t

theorem restrictNonnegativeProfile_measurable {k : ℕ} {μ : TimeLaw k}
    (hμ : MeasurableProfile μ) : NonnegativeMeasurableProfile (restrictNonnegativeProfile μ) := by
  intro s hs
  exact (hμ s hs).comp measurable_subtype_coe

@[simp] theorem restrict_extendNonnegativeProfile {k : ℕ} (μ : NonnegativeTimeLaw k) :
    restrictNonnegativeProfile (extendNonnegativeProfile μ) = μ := by
  funext t
  exact extendNonnegativeProfile_at μ t

end RiffleMain.Profile
