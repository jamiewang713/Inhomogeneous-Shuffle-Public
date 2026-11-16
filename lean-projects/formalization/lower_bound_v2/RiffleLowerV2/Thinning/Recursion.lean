import RiffleLowerV2.Thinning.PMFTools

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Thinning

/-- The labels surviving a specified sequence of column subsets. -/
def intersectionWithin {M d : ℕ} {Ω : Fin d → Type*} (A : Finset (Fin M))
    (S : ∀ j, Ω j → Finset (Fin M)) (ω : ∀ j, Ω j) : Finset (Fin M) :=
  A.filter fun i => ∀ j, i ∈ S j (ω j)

theorem affine_pos {q s : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hs : 0 < s) :
    0 < 1-q+q*s := by
  by_cases hq : q = 1
  · simpa [hq] using hs
  · have hlt : q < 1 := lt_of_le_of_ne hq1 hq
    have := mul_nonneg hq0 hs.le
    linarith

/-- Finite coordinate integration is the exact conditional step. Eliminating
columns recursively composes positive affine bases, including at q=0 and q=1. -/
theorem independent_intersection_transform (M d : ℕ) :
    ∀ (Ω : Fin d → Type*) [∀ j, Fintype (Ω j)] [∀ j, Nonempty (Ω j)]
      (S : ∀ j, Ω j → Finset (Fin M)) (q : Fin d → ℝ),
      (∀ j, 0 ≤ q j ∧ q j ≤ 1) →
      (∀ j (A : Finset (Fin M)) (s : ℝ), 0 < s →
        expect (PMF.uniformOfFintype (Ω j)) (fun ω => s^(A ∩ S j ω).card) ≤
          (1-q j+q j*s)^A.card) →
      ∀ (A : Finset (Fin M)) (s : ℝ), 0 < s →
      expect (PMF.uniformOfFintype (∀ j, Ω j))
        (fun ω => s^(intersectionWithin A S ω).card) ≤
        (1-(∏ j, q j)+(∏ j, q j)*s)^A.card := by
  induction d with
  | zero =>
      intro Ω _ _ S q hq hstep A s hs
      simp [intersectionWithin, uniform_expect_const]
  | succ d ih =>
      intro Ω _ _ S q hq hstep A s hs
      let Q := ∏ j : Fin d, q j.succ
      let z := 1-Q+Q*s
      have hQ0 : 0 ≤ Q := Finset.prod_nonneg fun j _ => (hq j.succ).1
      have hQ1 : Q ≤ 1 := Finset.prod_le_one (fun j _ => (hq j.succ).1) (fun j _ => (hq j.succ).2)
      have hz : 0 < z := affine_pos hQ0 hQ1 hs
      have hsplit (a : Ω 0) (ω : ∀ j : Fin d, Ω j.succ) :
          intersectionWithin A S (Fin.cons a ω) =
            intersectionWithin (A ∩ S 0 a) (fun j => S j.succ) ω := by
        ext i
        simp [intersectionWithin, Fin.forall_fin_succ, and_assoc]
      calc
        _ = expect (PMF.uniformOfFintype (Ω 0)) (fun a =>
            expect (PMF.uniformOfFintype (∀ j : Fin d, Ω j.succ))
              (fun ω => s^(intersectionWithin (A ∩ S 0 a) (fun j => S j.succ) ω).card)) := by
          rw [← uniform_expect_equiv (Fin.consEquiv Ω), uniform_product_expect]
          congr 1
          funext a
          congr 1
          funext ω
          exact congrArg (fun B : Finset (Fin M) => s^B.card) (hsplit a ω)
        _ ≤ expect (PMF.uniformOfFintype (Ω 0)) (fun a => z^(A ∩ S 0 a).card) := by
          apply expect_mono
          intro a
          exact ih (fun j => Ω j.succ) (fun j => S j.succ) (fun j => q j.succ)
            (fun j => hq j.succ) (fun j => hstep j.succ) (A ∩ S 0 a) s hs
        _ ≤ (1-q 0+q 0*z)^A.card := hstep 0 A z hz
        _ = _ := by
          rw [Fin.prod_univ_succ]
          congr 1
          dsimp [z, Q]
          ring

theorem binomial_le_exp {M : ℕ} {Q s : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (hs : 0 < s) :
    (1-Q+Q*s)^M ≤ Real.exp ((M : ℝ)*Q*(s-1)) := by
  calc
    _ ≤ (Real.exp (Q*(s-1)))^M := by
      apply pow_le_pow_left₀ (affine_pos hQ0 hQ1 hs).le
      linarith [Real.add_one_le_exp (Q*(s-1))]
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

end RiffleLowerV2.Thinning
