import FirstMoment.Entropy
import RiffleUpperV2.Shared.Empirical

/-! Actual probability-cost bins, with an exact exceptional-digit record.
A fixed complement represents the selected prefix and a harmless fixed completion;
only digits in I are allowed to vary. No simplex partition occurs. -/
noncomputable section
open scoped BigOperators
open Set
namespace RiffleUpperV2.FirstMoment
open TimeProfile

/-- Common lower masses suffice; equal word masses are not required. -/
theorem card_mul_lower_mass_le_one {J D : Type*} [Fintype J] [Fintype D]
    (p : J → D → ℝ) (hp : ∀ j l, 0 ≤ p j l)
    (hnorm : ∀ j, ∑ l, p j l = 1) (W : Finset (J → D))
    (m : ℝ) (hmass : ∀ w ∈ W, m ≤ ∏ j, p j (w j)) :
    (W.card : ℝ)*m ≤ 1 := by
  classical
  calc
    _ = ∑ _w ∈ W, m := by simp
    _ ≤ ∑ w ∈ W, ∏ j, p j (w j) := Finset.sum_le_sum hmass
    _ ≤ ∑ w : J → D, ∏ j, p j (w j) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ W)
        (fun w _ _ => Finset.prod_nonneg (fun j _ => hp j (w j)))
    _ = 1 := InhomogeneousShuffle.FirstMoment.word_mass_sum p hp hnorm

theorem log_card_le_of_lower_mass {J D : Type*} [Fintype J] [Fintype D]
    (p : J → D → ℝ) (hp : ∀ j l, 0 ≤ p j l)
    (hnorm : ∀ j, ∑ l, p j l = 1) (W : Finset (J → D))
    (hW : W.Nonempty) (H : ℝ)
    (hmass : ∀ w ∈ W, Real.exp (-H) ≤ ∏ j, p j (w j)) :
    Real.log (W.card : ℝ) ≤ H := by
  have h := card_mul_lower_mass_le_one p hp hnorm W (Real.exp (-H)) hmass
  have hc : 0 < (W.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hW
  have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos H).le
  have he : (W.card : ℝ) ≤ Real.exp H := by
    simpa [mul_assoc, ← Real.exp_add] using hh
  have hl := Real.log_le_log hc he
  simpa using hl

def exceptionalPositions {J : Type*} [Fintype J] [DecidableEq J] {k : ℕ}
    (p : J → Simplex k) (I : Finset J) (chi : ℝ) (w : J → Fin k) : Finset J := by
  classical
  exact I.filter (fun j => prob (p j) (w j) < chi)

def goodPositions {J : Type*} [Fintype J] [DecidableEq J] {k : ℕ}
    (p : J → Simplex k) (I : Finset J) (chi : ℝ) (w : J → Fin k) : Finset J :=
  I \ exceptionalPositions p I chi w

def selectedCost {J : Type*} [Fintype J] [DecidableEq J] {k : ℕ}
    (N : ℕ) (p : J → Simplex k) (I : Finset J) (w : J → Fin k) : ℝ :=
  (∑ j ∈ I, digitCost (prob (p j) (w j))) / logScale N

def goodCost {J : Type*} [Fintype J] [DecidableEq J] {k : ℕ}
    (N : ℕ) (p : J → Simplex k) (I : Finset J) (chi : ℝ) (w : J → Fin k) : ℝ :=
  selectedCost N p (goodPositions p I chi w) w

def exceptionalCost {J : Type*} [Fintype J] [DecidableEq J] {k : ℕ}
    (N : ℕ) (p : J → Simplex k) (I : Finset J) (chi : ℝ) (w : J → Fin k) : ℝ :=
  selectedCost N p (exceptionalPositions p I chi w) w

/-- The genuine cost split, before converting products into mean exponents. -/
theorem selectedCost_split {J : Type*} [Fintype J] [DecidableEq J] {k : ℕ}
    (N : ℕ) (p : J → Simplex k) (I : Finset J) (chi : ℝ) (w : J → Fin k) :
    selectedCost N p I w = goodCost N p I chi w+exceptionalCost N p I chi w := by
  classical
  unfold goodCost exceptionalCost goodPositions selectedCost
  rw [← add_div]
  congr 1
  exact (Finset.sum_sdiff (show exceptionalPositions p I chi w ⊆ I from
    Finset.filter_subset _ _)).symm

theorem selectedCost_nonneg {J : Type*} [Fintype J] [DecidableEq J] {k N : ℕ}
    (hN : 2 ≤ N) (p : J → Simplex k) (I : Finset J) (w : J → Fin k)
    (hlegal : ∀ j ∈ I, 0 < prob (p j) (w j)) : 0 ≤ selectedCost N p I w := by
  apply div_nonneg _ (logScale_pos hN).le
  apply Finset.sum_nonneg
  intro j hj
  exact Real.log_nonneg ((one_le_div (hlegal j hj)).mpr (prob_le_one _ _))

/-- This records the actual bin and actual exceptional positions and digits.
It fixes all remaining outside digits, including the chosen boundary prefix. -/
def costClass {J : Type*} [Fintype J] [DecidableEq J] {k : ℕ}
    (N : ℕ) (p : J → Simplex k) (I : Finset J) (chi width : ℝ)
    (w0 : J → Fin k) : Finset (J → Fin k) := by
  classical
  exact Finset.univ.filter fun w =>
    (∀ j ∉ I, w j = w0 j) ∧
    (∀ j ∈ I, 0 < prob (p j) (w j)) ∧
    exceptionalPositions p I chi w = exceptionalPositions p I chi w0 ∧
    (∀ j ∈ exceptionalPositions p I chi w0, w j = w0 j) ∧
    ⌊goodCost N p I chi w / width⌋ = ⌊goodCost N p I chi w0 / width⌋

theorem self_mem_costClass {J : Type*} [Fintype J] [DecidableEq J] {k : ℕ}
    (N : ℕ) (p : J → Simplex k) (I : Finset J) (chi width : ℝ)
    (w0 : J → Fin k) (hlegal : ∀ j ∈ I, 0 < prob (p j) (w0 j)) :
    w0 ∈ costClass N p I chi width w0 := by
  classical
  simpa [costClass] using hlegal

private theorem costClass_data {J : Type*} [Fintype J] [DecidableEq J] {k : ℕ}
    (N : ℕ) (p : J → Simplex k) (I : Finset J) (chi width : ℝ)
    (w0 w : J → Fin k) (hw : w ∈ costClass N p I chi width w0) :
    (∀ j ∉ goodPositions p I chi w0, w j = w0 j) ∧
    goodPositions p I chi w = goodPositions p I chi w0 ∧
    (∀ j ∈ I, 0 < prob (p j) (w j)) ∧
    ⌊goodCost N p I chi w / width⌋ = ⌊goodCost N p I chi w0 / width⌋ := by
  classical
  simp only [costClass, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  refine ⟨?_, by simp [goodPositions, hw.2.2.1], hw.2.1, hw.2.2.2.2⟩
  intro j hj
  by_cases hi : j ∈ I
  · apply hw.2.2.2.1
    simpa [goodPositions, hi] using hj
  · exact hw.1 j hi

/-- The fixed-width bin contributes at most one width above any representative. -/
theorem costClass_goodCost_le {J : Type*} [Fintype J] [DecidableEq J] {k : ℕ}
    (N : ℕ) (p : J → Simplex k) (I : Finset J) (chi width : ℝ)
    (hwidth : 0 < width) (w0 w : J → Fin k)
    (hw : w ∈ costClass N p I chi width w0) :
    goodCost N p I chi w ≤ goodCost N p I chi w0+width := by
  have hbin := (costClass_data N p I chi width w0 w hw).2.2.2
  have hl := Int.floor_le (goodCost N p I chi w0/width)
  have hu := Int.lt_floor_add_one (goodCost N p I chi w/width)
  rw [hbin] at hu
  have hd : goodCost N p I chi w/width ≤ goodCost N p I chi w0/width+1 := by linarith
  have hm := mul_le_mul_of_nonneg_right hd hwidth.le
  field_simp at hm
  nlinarith

/-- Independent tilted digits on good positions, deterministic digits elsewhere. -/
def classTilt {J : Type*} [Fintype J] [DecidableEq J] {k : ℕ}
    (p : J → Simplex k) (G : Finset J) (theta : ℝ) (w0 : J → Fin k) : J → Fin k → ℝ :=
  fun j d => if j ∈ G then tiltedWeight (p j) theta d else if d = w0 j then 1 else 0

theorem classTilt_nonneg {J : Type*} [Fintype J] [DecidableEq J] {k : ℕ}
    (p : J → Simplex k) (G : Finset J) (theta : ℝ) (w0 : J → Fin k) :
    ∀ j d, 0 ≤ classTilt p G theta w0 j d := by
  intro j d
  unfold classTilt
  split_ifs
  · exact div_nonneg (Real.rpow_nonneg (prob_nonneg _ _) _)
      (Finset.sum_nonneg (fun l _ => Real.rpow_nonneg (prob_nonneg _ _) _))
  · norm_num
  · norm_num

theorem classTilt_sum {J : Type*} [Fintype J] [DecidableEq J] {k : ℕ}
    (p : J → Simplex k) (G : Finset J) (theta : ℝ) (htheta : 1 ≤ theta)
    (w0 : J → Fin k) : ∀ j, ∑ d, classTilt p G theta w0 j d = 1 := by
  classical
  intro j
  by_cases hj : j ∈ G
  · simp only [classTilt, hj, if_true, tiltedWeight, ← Finset.sum_div]
    exact div_self (powerSum_pos (p j) htheta).ne'
  · simp [classTilt, hj]

/-- Exact log probability of every realized class word under its tilted law. -/
theorem costClass_tilt_log {J : Type*} [Fintype J] [DecidableEq J] {k N : ℕ}
    (hN : 2 ≤ N) (p : J → Simplex k) (I : Finset J) (chi width theta : ℝ)
    (htheta : 1 ≤ theta) (w0 w : J → Fin k)
    (hw : w ∈ costClass N p I chi width w0) :
    Real.log (∏ j, classTilt p (goodPositions p I chi w0) theta w0 j (w j)) =
      -theta*goodCost N p I chi w*logScale N+
        ∑ j ∈ goodPositions p I chi w0, psi (p j) theta := by
  classical
  let G := goodPositions p I chi w0
  obtain ⟨hout,hG,hlegal,hbin⟩ := costClass_data N p I chi width w0 w hw
  have hp : ∀ j, 0 < classTilt p G theta w0 j (w j) := by
    intro j
    by_cases hj : j ∈ G
    · simp only [classTilt, hj, if_true, tiltedWeight]
      exact div_pos (Real.rpow_pos_of_pos (hlegal j ((Finset.mem_sdiff.mp hj).1)) theta)
        (powerSum_pos (p j) htheta)
    · simp [classTilt, hj, hout j hj]
  rw [Real.log_prod (fun j _ => (hp j).ne')]
  have hlog : (∑ j, Real.log (classTilt p G theta w0 j (w j))) =
      ∑ j ∈ G, (-theta*digitCost (prob (p j) (w j))+psi (p j) theta) := by
    calc
      _ = ∑ j ∈ G, Real.log (classTilt p G theta w0 j (w j)) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        simp [classTilt, hj, hout j hj]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjp := hlegal j (Finset.mem_sdiff.mp hj).1
        simp only [classTilt, hj, if_true, tiltedWeight]
        rw [Real.log_div (Real.rpow_pos_of_pos hjp theta).ne'
          (powerSum_pos (p j) htheta).ne', Real.log_rpow hjp]
        simp [digitCost, psi, Real.log_inv, sub_eq_add_neg]
  rw [hlog, Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold goodCost selectedCost
  rw [hG]
  have hL := (logScale_pos hN).ne'
  dsimp [G]
  field_simp


/-- The class probability is positive even when unused digits have zero mass. -/
theorem costClass_tilt_pos {J : Type*} [Fintype J] [DecidableEq J] {k : ℕ}
    (N : ℕ) (p : J → Simplex k) (I : Finset J) (chi width theta : ℝ)
    (htheta : 1 ≤ theta) (w0 w : J → Fin k)
    (hw : w ∈ costClass N p I chi width w0) :
    0 < ∏ j, classTilt p (goodPositions p I chi w0) theta w0 j (w j) := by
  classical
  obtain ⟨hout,hG,hlegal,hbin⟩ := costClass_data N p I chi width w0 w hw
  apply Finset.prod_pos
  intro j _
  by_cases hj : j ∈ goodPositions p I chi w0
  · simp only [classTilt, hj, if_true, tiltedWeight]
    exact div_pos (Real.rpow_pos_of_pos (hlegal j (Finset.mem_sdiff.mp hj).1) theta)
      (powerSum_pos (p j) htheta)
  · simp [classTilt, hj, hout j hj]

/-- Entropy on the good positions with the exact cost-bin error theta*width. -/
theorem classEntropy_goodPositions {J : Type*} [Fintype J] [DecidableEq J] {k N : ℕ}
    (hN : 2 ≤ N) (p : J → Simplex k) (I : Finset J) (chi width theta : ℝ)
    (hwidth : 0 < width) (htheta : 1 ≤ theta) (w0 : J → Fin k)
    (hlegal : ∀ j ∈ I, 0 < prob (p j) (w0 j)) :
    Real.log ((costClass N p I chi width w0).card : ℝ)/logScale N ≤
      theta*goodCost N p I chi w0-
        (∑ j ∈ goodPositions p I chi w0, psi (p j) theta)/logScale N+theta*width := by
  let G := goodPositions p I chi w0
  let H := theta*(goodCost N p I chi w0+width)*logScale N-
    ∑ j ∈ G, psi (p j) theta
  have hm : ∀ w ∈ costClass N p I chi width w0,
      Real.exp (-H) ≤ ∏ j, classTilt p G theta w0 j (w j) := by
    intro w hw
    rw [← Real.exp_log (costClass_tilt_pos N p I chi width theta htheta w0 w hw)]
    apply Real.exp_le_exp.mpr
    rw [costClass_tilt_log hN p I chi width theta htheta w0 w hw]
    have hs := costClass_goodCost_le N p I chi width hwidth w0 w hw
    have hmul := mul_le_mul_of_nonneg_left hs
      (mul_nonneg (by linarith : 0 ≤ theta) (logScale_pos hN).le)
    dsimp [H,G]
    nlinarith
  have hh := log_card_le_of_lower_mass (classTilt p G theta w0)
    (classTilt_nonneg p G theta w0) (classTilt_sum p G theta htheta w0)
    (costClass N p I chi width w0)
    ⟨w0,self_mem_costClass N p I chi width w0 hlegal⟩ H hm
  apply (div_le_iff₀ (logScale_pos hN)).mpr
  dsimp [H,G] at hh
  have hL := (logScale_pos hN).ne'
  field_simp
  nlinarith

/-- Source entropy inequality for actual bins, with the explicit number of removed
columns. It needs no approximation or common-mass assumption. -/
theorem classEntropy {J : Type*} [Fintype J] [DecidableEq J] {k N : ℕ}
    (hk : 2 ≤ k) (hN : 2 ≤ N) (p : J → Simplex k) (I : Finset J)
    (chi width theta : ℝ) (hwidth : 0 < width)
    (htheta : theta ∈ Icc (3 : ℝ) 4) (w0 : J → Fin k)
    (hlegal : ∀ j ∈ I, 0 < prob (p j) (w0 j)) :
    Real.log ((costClass N p I chi width w0).card : ℝ)/logScale N ≤
      theta*goodCost N p I chi w0-(∑ j ∈ I, psi (p j) theta)/logScale N+
        4*width+4*Real.log (k : ℝ)*(exceptionalPositions p I chi w0).card/logScale N := by
  have hgood := classEntropy_goodPositions hN p I chi width theta hwidth
    (by linarith [htheta.1]) w0 hlegal
  have htheta' : theta ∈ Icc (2 : ℝ) 4 := ⟨by linarith [htheta.1],htheta.2⟩
  have hsum : (∑ j ∈ exceptionalPositions p I chi w0, psi (p j) theta) ≤
      4*Real.log (k : ℝ)*(exceptionalPositions p I chi w0).card := by
    calc
      _ ≤ ∑ _j ∈ exceptionalPositions p I chi w0, 4*Real.log (k : ℝ) :=
        Finset.sum_le_sum fun j _ => (psi_bounds hk (p j) htheta').2
      _ = _ := by simp [mul_comm]
  have hsplit : (∑ j ∈ goodPositions p I chi w0, psi (p j) theta)+
      (∑ j ∈ exceptionalPositions p I chi w0, psi (p j) theta) =
      ∑ j ∈ I, psi (p j) theta :=
    Finset.sum_sdiff (Finset.filter_subset _ _)
  have hd := div_le_div_of_nonneg_right hsum (logScale_pos hN).le
  have ht := mul_le_mul_of_nonneg_right htheta.2 hwidth.le
  have heq := congrArg (fun z : ℝ => z/logScale N) hsplit
  rw [add_div] at heq
  linarith

/-- The manuscript's retained exceptional budget gives exactly its stated e_H. -/
theorem classEntropy_of_exceptionalBudget {J : Type*} [Fintype J] [DecidableEq J]
    {k N : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N) (p : J → Simplex k) (I : Finset J)
    (chi width theta alpha : ℝ) (hwidth : 0 < width)
    (htheta : theta ∈ Icc (3 : ℝ) 4) (w0 : J → Fin k)
    (hlegal : ∀ j ∈ I, 0 < prob (p j) (w0 j))
    (hbudget : ((exceptionalPositions p I chi w0).card : ℝ) ≤ alpha*logScale N) :
    Real.log ((costClass N p I chi width w0).card : ℝ)/logScale N ≤
      theta*goodCost N p I chi w0-(∑ j ∈ I, psi (p j) theta)/logScale N+
        (4*width+4*Real.log (k : ℝ)*alpha) := by
  have h := classEntropy hk hN p I chi width theta hwidth htheta w0 hlegal
  have hc : 0 ≤ 4*Real.log (k : ℝ) := by
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k)))
  have hd := (div_le_iff₀ (logScale_pos hN)).mpr hbudget
  have hm := mul_le_mul_of_nonneg_left hd hc
  rw [← mul_div_assoc] at hm
  linarith

/-- Actual absolute-column interval; the ambient population N is never substituted. -/
def empiricalPositions (L a s u : ℕ) : Finset (Fin L) :=
  Finset.univ.filter fun j => s-a ≤ j.val ∧ j.val < u-a

theorem empiricalClassEntropy {k n L N : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    (a s u : ℕ) (cuts : Cuts k n L) (hn : 0 < n)
    (chi width theta alpha : ℝ) (hwidth : 0 < width)
    (htheta : theta ∈ Icc (3 : ℝ) 4) (w0 : Fin L → Fin k)
    (hlegal : ∀ j ∈ empiricalPositions L a s u, 0 < prob (cuts.profile hn j) (w0 j))
    (hbudget : ((exceptionalPositions (cuts.profile hn) (empiricalPositions L a s u)
      chi w0).card : ℝ) ≤ alpha*logScale N) :
    Real.log ((costClass N (cuts.profile hn) (empiricalPositions L a s u)
      chi width w0).card : ℝ)/logScale N ≤
      theta*goodCost N (cuts.profile hn) (empiricalPositions L a s u) chi w0-
        empiricalB N a cuts hn theta s u+(4*width+4*Real.log (k : ℝ)*alpha) := by
  exact classEntropy_of_exceptionalBudget hk hN (cuts.profile hn)
    (empiricalPositions L a s u) chi width theta alpha hwidth htheta w0 hlegal hbudget

end RiffleUpperV2.FirstMoment
