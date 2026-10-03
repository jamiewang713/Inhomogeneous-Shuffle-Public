import RiffleUpperV2.Hypergeometric.Cylinder

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Hypergeometric
open TimeProfile RiffleLowerV2 RiffleLowerV2.Thinning

theorem allowed_intersection_mean {k n d : ℕ} (cuts : Cuts k n d)
    (j : Fin d) (D : Finset (Fin k)) (A : Finset (Fin n)) :
    expect (columnPMF cuts j)
      (fun c => ((A ∩ (Finset.univ.filter (fun i => c.val i ∈ D))).card : ℝ)) =
      A.card * ((allowedCount cuts j D : ℝ) / n) := by
  have he := allowed_subset_expect cuts j D (fun S => ((A ∩ S.val).card : ℝ))
  change expect (columnPMF cuts j)
    (fun c => ((A ∩ (Finset.univ.filter (fun i => c.val i ∈ D))).card : ℝ)) = _ at he
  rw [he, Compat.sample_expect_intersection_eq_hypergeom Finset.univ A
    (allowedCount cuts j D) (by simpa using allowedCount_le cuts j D)
    (Finset.subset_univ _) (fun q => (q : ℝ))]
  rw [Compat.HypergeomParams.expect_val]
  simp [Compat.samplingParams, Compat.HypergeomParams.mean, mul_div_assoc]

/-- Exact integration over the independent columns; no positivity is required. -/
theorem independent_intersection_mean (n d : ℕ) :
    ∀ (Ω : Fin d → Type*) [∀ j, Fintype (Ω j)] [∀ j, Nonempty (Ω j)]
      (S : ∀ j, Ω j → Finset (Fin n)) (q : Fin d → ℝ),
      (∀ j (A : Finset (Fin n)),
        expect (PMF.uniformOfFintype (Ω j)) (fun ω => ((A ∩ S j ω).card : ℝ)) =
          A.card * q j) →
      ∀ A : Finset (Fin n),
        expect (PMF.uniformOfFintype (∀ j, Ω j))
          (fun ω => ((intersectionWithin A S ω).card : ℝ)) = A.card * ∏ j, q j := by
  induction d with
  | zero =>
      intro Ω _ _ S q hstep A
      simp [intersectionWithin, uniform_expect_const]
  | succ d ih =>
      intro Ω _ _ S q hstep A
      have hsplit (a : Ω 0) (ω : ∀ j : Fin d, Ω j.succ) :
          intersectionWithin A S (Fin.cons a ω) =
            intersectionWithin (A ∩ S 0 a) (fun j => S j.succ) ω := by
        ext i
        simp [intersectionWithin, Fin.forall_fin_succ, and_assoc]
      calc
        _ = expect (PMF.uniformOfFintype (Ω 0)) (fun a =>
            expect (PMF.uniformOfFintype (∀ j : Fin d, Ω j.succ))
              (fun ω => ((intersectionWithin (A ∩ S 0 a) (fun j => S j.succ) ω).card : ℝ))) := by
          rw [← uniform_expect_equiv (Fin.consEquiv Ω), uniform_product_expect]
          congr 1
          funext a
          congr 1
          funext ω
          exact congrArg (fun B : Finset (Fin n) => (B.card : ℝ)) (hsplit a ω)
        _ = expect (PMF.uniformOfFintype (Ω 0))
            (fun a => ((A ∩ S 0 a).card : ℝ) * ∏ j : Fin d, q j.succ) := by
          congr 1
          funext a
          exact ih (fun j => Ω j.succ) (fun j => S j.succ) (fun j => q j.succ)
            (fun j => hstep j.succ) (A ∩ S 0 a)
        _ = (∏ j : Fin d, q j.succ) *
            expect (PMF.uniformOfFintype (Ω 0)) (fun a => ((A ∩ S 0 a).card : ℝ)) := by
          simp_rw [mul_comm _ (∏ j : Fin d, q j.succ)]
          rw [expect_const_mul]
        _ = _ := by rw [hstep, Fin.prod_univ_succ]; ring

/-- The cylinder parameter used in transform/tail bounds is its actual expectation. -/
theorem cylinderMean_eq_expect {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (D : Fin d → Finset (Fin k)) :
    cylinderMean cuts R D =
      expect (fixedCountPMF cuts) (fun ω => (cylinderCount cuts R D ω : ℝ)) := by
  symm
  exact independent_intersection_mean n d (ColumnAssignments cuts)
    (fun j c => Finset.univ.filter (fun i => c.val i ∈ D j))
    (fun j => (allowedCount cuts j (D j) : ℝ) / n)
    (fun j A => allowed_intersection_mean cuts j (D j) A) R

/-- Literal mean-over-anchor-size normalization in the manuscript display. -/
theorem anchorCylinderTransform_mean {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (hR : 0 < R.card) (D : Fin d → Finset (Fin k))
    (s : ℝ) (hs : 0 < s) :
    expect (fixedCountPMF cuts) (fun ω => s ^ cylinderCount cuts R D ω) ≤
      (1 - cylinderMean cuts R D / R.card + cylinderMean cuts R D / R.card * s) ^ R.card ∧
    (1 - cylinderMean cuts R D / R.card + cylinderMean cuts R D / R.card * s) ^ R.card ≤
      Real.exp (cylinderMean cuts R D * (s - 1)) := by
  have he : cylinderMean cuts R D / R.card = cylinderMass cuts D := by
    unfold cylinderMean
    have hR0 : (R.card : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
    field_simp
  rw [he]
  exact anchorCylinderTransform cuts R D s hs

end RiffleUpperV2.Hypergeometric
