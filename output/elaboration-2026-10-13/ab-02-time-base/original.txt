import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Set.Union
import Mathlib.Tactic

/-!
Finite foundations and literal source definitions for the frozen time-profile contract.
Lean column `j` denotes paper column `j.val + 1`.
-/

noncomputable section

open scoped BigOperators NNReal
open MeasureTheory Set

namespace TimeProfile

abbrev Simplex (k : ℕ) := ↥(stdSimplex ℝ (Fin k))

def prob {k : ℕ} (p : Simplex k) (l : Fin k) : ℝ := p.val l

theorem prob_nonneg {k : ℕ} (p : Simplex k) (l : Fin k) : 0 ≤ prob p l :=
  p.property.1 l

theorem prob_le_one {k : ℕ} (p : Simplex k) (l : Fin k) : prob p l ≤ 1 :=
  (mem_Icc_of_mem_stdSimplex p.property l).2

theorem sum_prob {k : ℕ} (p : Simplex k) : ∑ l, prob p l = 1 :=
  p.property.2

def pileMax {k : ℕ} (p : Simplex k) : ℝ :=
  ((Finset.univ.sup (fun l : Fin k => (⟨prob p l, prob_nonneg p l⟩ : ℝ≥0)) : ℝ≥0) : ℝ)

theorem exists_prob_pos {k : ℕ} (p : Simplex k) : ∃ l, 0 < prob p l := by
  by_contra! h
  have hs : ∑ l, prob p l ≤ 0 := Finset.sum_nonpos fun l _ => h l
  rw [sum_prob] at hs
  linarith

theorem prob_le_pileMax {k : ℕ} (p : Simplex k) (l : Fin k) :
    prob p l ≤ pileMax p := by
  unfold pileMax
  exact_mod_cast (Finset.le_sup (s := Finset.univ)
    (f := fun i : Fin k => (⟨prob p i, prob_nonneg p i⟩ : ℝ≥0)) (Finset.mem_univ l))

theorem pileMax_nonneg {k : ℕ} (p : Simplex k) : 0 ≤ pileMax p := by
  unfold pileMax
  exact NNReal.coe_nonneg _

theorem pileMax_pos {k : ℕ} (p : Simplex k) : 0 < pileMax p := by
  obtain ⟨l, hl⟩ := exists_prob_pos p
  exact hl.trans_le (prob_le_pileMax p l)

theorem pileMax_le_one {k : ℕ} (p : Simplex k) : pileMax p ≤ 1 := by
  unfold pileMax
  exact_mod_cast (Finset.sup_le fun l (_ : l ∈ (Finset.univ : Finset (Fin k))) =>
    (show (⟨prob p l, prob_nonneg p l⟩ : ℝ≥0) ≤ 1 from prob_le_one p l))

theorem inv_card_le_pileMax {k : ℕ} (hk : 0 < k) (p : Simplex k) :
    1 / (k : ℝ) ≤ pileMax p := by
  apply (div_le_iff₀ (show 0 < (k : ℝ) by exact_mod_cast hk)).2
  calc
    1 = ∑ l, prob p l := (sum_prob p).symm
    _ ≤ ∑ _l : Fin k, pileMax p := Finset.sum_le_sum fun l _ => prob_le_pileMax p l
    _ = pileMax p * (k : ℝ) := by simp [mul_comm]

def digitCost (z : ℝ) : ℝ := Real.log (1 / z)

def maxCost {k : ℕ} (p : Simplex k) : ℝ := digitCost (pileMax p)

def powerSum {k : ℕ} (p : Simplex k) (theta : ℝ) : ℝ :=
  ∑ l, (prob p l) ^ theta

def psi {k : ℕ} (p : Simplex k) (theta : ℝ) : ℝ :=
  -Real.log (powerSum p theta)

def tiltedWeight {k : ℕ} (p : Simplex k) (theta : ℝ) (l : Fin k) : ℝ :=
  (prob p l) ^ theta / powerSum p theta

def tiltedCost {k : ℕ} (p : Simplex k) (theta : ℝ) : ℝ :=
  ∑ l, if prob p l = 0 then 0 else tiltedWeight p theta l * digitCost (prob p l)

def shannonEntropy {k : ℕ} (q : Fin k → ℝ) : ℝ :=
  -∑ l, if q l = 0 then 0 else q l * Real.log (q l)

def tiltedEntropy {k : ℕ} (p : Simplex k) (theta : ℝ) : ℝ :=
  shannonEntropy (tiltedWeight p theta)

structure Cuts (k N K : ℕ) where
  count : Fin K → Fin k → ℕ
  sum_count : ∀ j, ∑ l, count j l = N

def Cuts.profile {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N) (j : Fin K) :
    Simplex k := by
  refine ⟨fun l => (cuts.count j l : ℝ) / (N : ℝ), ?_, ?_⟩
  · intro l
    positivity
  · have hs : ∑ l, (cuts.count j l : ℝ) = (N : ℝ) := by
      exact_mod_cast cuts.sum_count j
    rw [← Finset.sum_div, hs, div_self]
    exact_mod_cast hN.ne'

theorem Cuts.profile_prob {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (j : Fin K) (l : Fin k) :
    prob (cuts.profile hN j) l = (cuts.count j l : ℝ) / (N : ℝ) := rfl

theorem Cuts.profile_pos_iff {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (j : Fin K) (l : Fin k) :
    0 < prob (cuts.profile hN j) l ↔ 0 < cuts.count j l := by
  rw [Cuts.profile_prob, div_pos_iff_of_pos_right (show 0 < (N : ℝ) by exact_mod_cast hN)]
  exact Nat.cast_pos

def logScale (N : ℕ) : ℝ := Real.log (N : ℝ)

def columnTime {K : ℕ} (N : ℕ) (j : Fin K) : ℝ :=
  ((j.val : ℝ) + 1) / logScale N

def horizonDepth (N : ℕ) (T : ℝ) : ℕ := ⌊T * logScale N⌋₊

theorem logScale_pos {N : ℕ} (hN : 2 ≤ N) : 0 < logScale N := by
  apply Real.log_pos
  exact_mod_cast (show 1 < N by omega)

theorem horizonDepth_error {N : ℕ} (hN : 2 ≤ N) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ T - (horizonDepth N T : ℝ) / logScale N ∧
      T - (horizonDepth N T : ℝ) / logScale N < 1 / logScale N := by
  have hL := logScale_pos hN
  have hlo : (horizonDepth N T : ℝ) ≤ T * logScale N :=
    Nat.floor_le (mul_nonneg hT hL.le)
  have hhi : T * logScale N < (horizonDepth N T : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  constructor
  · exact sub_nonneg.mpr ((div_le_iff₀ hL).2 hlo)
  · apply (lt_div_iff₀ hL).2
    rw [sub_mul, div_mul_cancel₀ _ hL.ne']
    linarith

theorem horizonDepth_zero (N : ℕ) : horizonDepth N 0 = 0 := by
  simp [horizonDepth]

structure BorelPartition (k : ℕ) where
  cellCount : ℕ
  classify : Simplex k → Fin cellCount
  measurable_classify : Measurable classify
  rep : Fin cellCount → Simplex k
  classify_rep : ∀ i, classify (rep i) = i

def BorelPartition.cell {k : ℕ} (P : BorelPartition k) (i : Fin P.cellCount) :
    Set (Simplex k) := {p | P.classify p = i}

structure BorelPartition.IsRegular {k : ℕ} (P : BorelPartition k) (chi C : ℝ) : Prop where
  psi_oscillation : ∀ (i : Fin P.cellCount) (p p' : Simplex k),
    P.classify p = i → P.classify p' = i → ∀ theta ∈ Icc (2 : ℝ) 4,
    |psi p theta - psi p' theta| ≤ C * chi
  maxCost_oscillation : ∀ (i : Fin P.cellCount) (p p' : Simplex k),
    P.classify p = i → P.classify p' = i → |maxCost p - maxCost p'| ≤ C * chi
  good_digit : ∀ (i : Fin P.cellCount) (p : Simplex k) (l : Fin k),
    P.classify p = i → 2 * chi < prob (P.rep i) l →
    chi < prob p l ∧ |digitCost (prob p l) - digitCost (prob (P.rep i) l)| ≤ C * chi
  exceptional_digit : ∀ (i : Fin P.cellCount) (p : Simplex k) (l : Fin k),
    P.classify p = i → prob (P.rep i) l ≤ 2 * chi → prob p l ≤ 3 * chi

def BorelPartition.IsGoodDigit {k : ℕ} (P : BorelPartition k) (chi : ℝ)
    (p : Simplex k) (l : Fin k) : Prop :=
  2 * chi < prob (P.rep (P.classify p)) l

theorem BorelPartition.IsRegular.good_prob_pos {k : ℕ} {P : BorelPartition k}
    {chi C : ℝ} (_hreg : P.IsRegular chi C) (hchi : 0 < chi) {p : Simplex k}
    {l : Fin k} (hgood : P.IsGoodDigit chi p l) :
    0 < prob (P.rep (P.classify p)) l := by
  dsimp [IsGoodDigit] at hgood
  linarith

theorem BorelPartition.IsRegular.good_actual_gt {k : ℕ} {P : BorelPartition k}
    {chi C : ℝ} (hreg : P.IsRegular chi C) (_hchi : 0 < chi) {p : Simplex k}
    {l : Fin k} (hgood : P.IsGoodDigit chi p l) : chi < prob p l :=
  (hreg.good_digit (P.classify p) p l rfl hgood).1

theorem BorelPartition.IsRegular.good_digitCost_error {k : ℕ} {P : BorelPartition k}
    {chi C : ℝ} (hreg : P.IsRegular chi C) (_hchi : 0 < chi) {p : Simplex k}
    {l : Fin k} (hgood : P.IsGoodDigit chi p l) :
    |digitCost (prob p l) - digitCost (prob (P.rep (P.classify p)) l)| ≤ C * chi :=
  (hreg.good_digit (P.classify p) p l rfl hgood).2

theorem BorelPartition.IsRegular.exceptional_actual_le {k : ℕ} {P : BorelPartition k}
    {chi C : ℝ} (hreg : P.IsRegular chi C) {p : Simplex k} {l : Fin k}
    (hbad : ¬P.IsGoodDigit chi p l) : prob p l ≤ 3 * chi :=
  hreg.exceptional_digit (P.classify p) p l rfl (le_of_not_gt hbad)

theorem BorelPartition.IsRegular.maxCost_rep_error {k : ℕ} {P : BorelPartition k}
    {chi C : ℝ} (hreg : P.IsRegular chi C) (p : Simplex k) :
    |maxCost p - maxCost (P.rep (P.classify p))| ≤ C * chi :=
  hreg.maxCost_oscillation (P.classify p) p _ rfl (P.classify_rep _)

theorem BorelPartition.IsRegular.psi_rep_error {k : ℕ} {P : BorelPartition k}
    {chi C : ℝ} (hreg : P.IsRegular chi C) (p : Simplex k) {theta : ℝ}
    (htheta : theta ∈ Icc (2 : ℝ) 4) :
    |psi p theta - psi (P.rep (P.classify p)) theta| ≤ C * chi :=
  hreg.psi_oscillation (P.classify p) p _ rfl (P.classify_rep _) theta htheta

structure TimeMesh (T : ℝ) where
  cellCount : ℕ
  cellCount_pos : 0 < cellCount
  boundary : Fin (cellCount + 1) → ℝ
  strictMono_boundary : StrictMono boundary
  boundary_zero : boundary 0 = 0
  boundary_last : boundary (Fin.last cellCount) = T

def TimeMesh.cell {T : ℝ} (mesh : TimeMesh T) (q : Fin mesh.cellCount) : Set ℝ :=
  if q.val + 1 = mesh.cellCount then
    Icc (mesh.boundary q.castSucc) (mesh.boundary q.succ)
  else Ico (mesh.boundary q.castSucc) (mesh.boundary q.succ)

def TimeMesh.MeshLE {T : ℝ} (mesh : TimeMesh T) (Delta : ℝ) : Prop :=
  ∀ q : Fin mesh.cellCount, mesh.boundary q.succ - mesh.boundary q.castSucc ≤ Delta

theorem TimeMesh.cells_disjoint {T : ℝ} (mesh : TimeMesh T)
    (q q' : Fin mesh.cellCount) (hqq' : q ≠ q') :
    Disjoint (mesh.cell q) (mesh.cell q') := by
  have hordered : ∀ a b : Fin mesh.cellCount, a < b →
      Disjoint (mesh.cell a) (mesh.cell b) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro t hta htb
    have habval : a.val < b.val := hab
    have hnotlast : a.val + 1 ≠ mesh.cellCount := by omega
    have haupper : t < mesh.boundary a.succ := by
      exact (show t ∈ Ico (mesh.boundary a.castSucc) (mesh.boundary a.succ) from
        by simpa only [TimeMesh.cell, if_neg hnotlast] using hta).2
    have hblower : mesh.boundary b.castSucc ≤ t := by
      dsimp [TimeMesh.cell] at htb
      split_ifs at htb <;> exact htb.1
    have hindex : a.succ ≤ b.castSucc := by
      change a.val + 1 ≤ b.val
      omega
    have hboundary := mesh.strictMono_boundary.monotone hindex
    linarith
  rcases lt_or_gt_of_ne hqq' with hlt | hgt
  · exact hordered q q' hlt
  · exact (hordered q' q hgt).symm

theorem TimeMesh.existsUnique_mem_cell {T : ℝ} (mesh : TimeMesh T) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) T) : ∃! q : Fin mesh.cellCount, t ∈ mesh.cell q := by
  classical
  let lower : Finset (Fin mesh.cellCount) :=
    Finset.univ.filter fun q => mesh.boundary q.castSucc ≤ t
  let first : Fin mesh.cellCount := ⟨0, mesh.cellCount_pos⟩
  have hfirst : first ∈ lower := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hcast : first.castSucc = 0 := Fin.ext rfl
    rw [hcast, mesh.boundary_zero]
    exact ht.1
  have hnonempty : lower.Nonempty := ⟨first, hfirst⟩
  let q := lower.max' hnonempty
  have hq : q ∈ lower := Finset.max'_mem lower hnonempty
  have hqlo : mesh.boundary q.castSucc ≤ t := (Finset.mem_filter.mp hq).2
  have hqmem : t ∈ mesh.cell q := by
    by_cases hlast : q.val + 1 = mesh.cellCount
    · rw [TimeMesh.cell, if_pos hlast]
      refine ⟨hqlo, ?_⟩
      have hsucc : q.succ = Fin.last mesh.cellCount := Fin.ext hlast
      rw [hsucc, mesh.boundary_last]
      exact ht.2
    · rw [TimeMesh.cell, if_neg hlast]
      refine ⟨hqlo, ?_⟩
      apply lt_of_not_ge
      intro htupper
      have hnextlt : q.val + 1 < mesh.cellCount := by
        have hqbound := q.isLt
        omega
      let next : Fin mesh.cellCount := ⟨q.val + 1, hnextlt⟩
      have hnextmem : next ∈ lower := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        have hcast : next.castSucc = q.succ := Fin.ext rfl
        rw [hcast]
        exact htupper
      have hnextle : next ≤ q := Finset.le_max' lower next hnextmem
      have hvalues : q.val + 1 ≤ q.val := hnextle
      omega
  refine ⟨q, hqmem, ?_⟩
  intro q' hq'mem
  by_contra hneq
  exact Set.disjoint_left.mp (mesh.cells_disjoint q' q hneq) hq'mem hqmem

def TimeMesh.cellIndex {T : ℝ} (mesh : TimeMesh T) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) T) : Fin mesh.cellCount :=
  Classical.choose (mesh.existsUnique_mem_cell t ht).exists

theorem TimeMesh.cellIndex_mem {T : ℝ} (mesh : TimeMesh T) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) T) : t ∈ mesh.cell (mesh.cellIndex t ht) :=
  Classical.choose_spec (mesh.existsUnique_mem_cell t ht).exists

theorem TimeMesh.column_cellIndex_mem {N K : ℕ} {T : ℝ} (mesh : TimeMesh T)
    (j : Fin K) (hj : 0 < columnTime N j ∧ columnTime N j ≤ T) :
    columnTime N j ∈ mesh.cell (mesh.cellIndex (columnTime N j) ⟨hj.1.le, hj.2⟩) :=
  mesh.cellIndex_mem _ _

abbrev TimeLaw (k : ℕ) := ℝ → MeasureTheory.ProbabilityMeasure (Simplex k)

def profileMaxCost {k : ℕ} (mu : TimeLaw k) (t : ℝ) : ℝ :=
  ∫ p, maxCost p ∂(mu t : Measure (Simplex k))

def profilePsi {k : ℕ} (mu : TimeLaw k) (t theta : ℝ) : ℝ :=
  ∫ p, psi p theta ∂(mu t : Measure (Simplex k))

def profileTiltedCost {k : ℕ} (mu : TimeLaw k) (t theta : ℝ) : ℝ :=
  ∫ p, tiltedCost p theta ∂(mu t : Measure (Simplex k))

def profileTiltedEntropy {k : ℕ} (mu : TimeLaw k) (t theta : ℝ) : ℝ :=
  ∫ p, tiltedEntropy p theta ∂(mu t : Measure (Simplex k))

def integratedMaxCost {k : ℕ} (mu : TimeLaw k) (r s : ℝ) : ℝ :=
  ∫ t in r..s, profileMaxCost mu t

def integratedPsi {k : ℕ} (mu : TimeLaw k) (theta r s : ℝ) : ℝ :=
  ∫ t in r..s, profilePsi mu t theta

def integratedTiltedCost {k : ℕ} (mu : TimeLaw k) (theta r s : ℝ) : ℝ :=
  ∫ t in r..s, profileTiltedCost mu t theta

def cellMass {k : ℕ} (mu : TimeLaw k) (P : BorelPartition k)
    (i : Fin P.cellCount) (t : ℝ) : ℝ :=
  ((mu t : Measure (Simplex k)) (P.cell i)).toReal

def intervalCount {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (a b : ℝ) (i : Fin P.cellCount) : ℕ := by
  classical
  exact (Finset.univ.filter fun j : Fin K =>
    a ≤ columnTime N j ∧ columnTime N j ≤ b ∧ P.classify (cuts.profile hN j) = i).card

def AlmostLike {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (mu : TimeLaw k) (P : BorelPartition k) (T rho phi : ℝ) : Prop :=
  ∀ a : ℝ, (∃ z : ℤ, a = rho * z) → 0 ≤ a → a < min (a + rho) T →
    ∀ i : Fin P.cellCount,
      |(intervalCount cuts hN P a (min (a + rho) T) i : ℝ) / logScale N -
        ∫ t in a..min (a + rho) T, cellMass mu P i t| ≤
      phi * (min (a + rho) T - a) + 1 / logScale N

def GoodColumn {k : ℕ} (p : Simplex k) (chi : ℝ) : Prop :=
  ∃ l m : Fin k, l ≠ m ∧ chi ≤ prob p l ∧ chi ≤ prob p m

def LocalGood {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (chi gamma rho r T : ℝ) : Prop := by
  classical
  exact ∀ a : ℝ, r ≤ a → a + rho ≤ T →
    gamma * rho * logScale N ≤
      ((Finset.univ.filter fun j : Fin K =>
        a ≤ columnTime N j ∧ columnTime N j ≤ a + rho ∧
          GoodColumn (cuts.profile hN j) chi).card : ℝ)

end TimeProfile
