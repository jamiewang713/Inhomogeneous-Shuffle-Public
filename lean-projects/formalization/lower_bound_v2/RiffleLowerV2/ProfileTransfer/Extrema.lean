import Contracts.v1.Endpoints

noncomputable section
open Set
namespace RiffleLowerV2.ProfileTransfer

/-- The alpha-domain in the frozen lower margin is nonempty. -/
theorem alphaDomain_nonempty : (Icc (3 : ℝ) 4).Nonempty := ⟨3, by norm_num⟩

/-- Uniform bounds make each real infimum meaningful without temporal continuity. -/
theorem alphaInf_bounds (f : ℝ → ℝ) (C : ℝ)
    (hf : ∀ a ∈ Icc (3 : ℝ) 4, |f a| ≤ C) :
    -C ≤ sInf (f '' Icc (3 : ℝ) 4) ∧ sInf (f '' Icc (3 : ℝ) 4) ≤ C := by
  have hb : BddBelow (f '' Icc (3 : ℝ) 4) := by
    refine ⟨-C, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact (abs_le.mp (hf a ha)).1
  constructor
  · apply le_csInf (alphaDomain_nonempty.image f)
    rintro _ ⟨a, ha, rfl⟩
    exact (abs_le.mp (hf a ha)).1
  · exact (csInf_le hb ⟨3, by norm_num, rfl⟩).trans (abs_le.mp (hf 3 (by norm_num))).2

/-- Taking an infimum preserves a pointwise additive upper comparison. -/
theorem alphaInf_le_add (f g : ℝ → ℝ) (C d : ℝ)
    (hf : ∀ a ∈ Icc (3 : ℝ) 4, |f a| ≤ C)
    (hfg : ∀ a ∈ Icc (3 : ℝ) 4, f a ≤ g a + d) :
    sInf (f '' Icc (3 : ℝ) 4) ≤ sInf (g '' Icc (3 : ℝ) 4) + d := by
  have hb : BddBelow (f '' Icc (3 : ℝ) 4) := by
    refine ⟨-C, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact (abs_le.mp (hf a ha)).1
  have h : sInf (f '' Icc (3 : ℝ) 4) - d ≤ sInf (g '' Icc (3 : ℝ) 4) := by
    apply le_csInf (alphaDomain_nonempty.image g)
    rintro _ ⟨a, ha, rfl⟩
    have hi := csInf_le hb (show f a ∈ f '' Icc (3 : ℝ) 4 from ⟨a, ha, rfl⟩)
    have hc := hfg a ha
    linarith
  linarith

/-- A map between nonempty time domains transfers their bounded variational values. -/
theorem variational_le_of_lift
    (f g : ℝ → ℝ → ℝ → ℝ) (D E : Set (ℝ × ℝ)) (C d : ℝ)
    (hD : D.Nonempty) (hf : ∀ su ∈ D, ∀ a ∈ Icc (3 : ℝ) 4, |f a su.1 su.2| ≤ C)
    (hg : ∀ su ∈ E, ∀ a ∈ Icc (3 : ℝ) 4, |g a su.1 su.2| ≤ C)
    (hlift : ∀ su ∈ D, ∃ tv ∈ E, ∀ a ∈ Icc (3 : ℝ) 4,
      f a su.1 su.2 ≤ g a tv.1 tv.2 + d) :
    sSup ((fun su : ℝ × ℝ => sInf ((fun a => f a su.1 su.2) '' Icc (3 : ℝ) 4)) '' D) ≤
      sSup ((fun su : ℝ × ℝ => sInf ((fun a => g a su.1 su.2) '' Icc (3 : ℝ) 4)) '' E) + d := by
  let fi := fun su : ℝ × ℝ => sInf ((fun a => f a su.1 su.2) '' Icc (3 : ℝ) 4)
  let gi := fun su : ℝ × ℝ => sInf ((fun a => g a su.1 su.2) '' Icc (3 : ℝ) 4)
  have hbg : BddAbove (gi '' E) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨su, hsu, rfl⟩
    exact (alphaInf_bounds _ C (hg su hsu)).2
  apply csSup_le (hD.image fi)
  rintro _ ⟨su, hsu, rfl⟩
  obtain ⟨tv, htv, hfg⟩ := hlift su hsu
  have h1 := alphaInf_le_add (fun a => f a su.1 su.2)
    (fun a => g a tv.1 tv.2) C d (hf su hsu) hfg
  have h2 := le_csSup hbg (show gi tv ∈ gi '' E from ⟨tv, htv, rfl⟩)
  dsimp only [gi] at h2
  linarith

end RiffleLowerV2.ProfileTransfer
