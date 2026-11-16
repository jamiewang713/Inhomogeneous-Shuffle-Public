import RiffleLowerV2.Model.Main
import RiffleLowerV2.Thinning.Main
import RiffleLowerV2.Ascent.Mixture

/-! Source `prop:largest-prefix`: the exact finite contiguous-run test.
The natural permutation-counting argument is adapted from the historical
`lean-lower-bound/RiffleLower/UniformPermutation.lean` (U01--U06).
All probability laws and sorting maps below are the canonical shared objects.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace RiffleLowerV2.EmpiricalLower
open TimeProfile

private def increasingAlong {N m : ℕ} (e : Fin m ↪ Fin N)
    (π : Permutation N) : Prop := StrictMono (fun i => π (e i))

private def increasingAlongEvent {N m : ℕ} (e : Fin m ↪ Fin N) :
    Finset (Permutation N) := Finset.univ.filter (increasingAlong e)

private theorem unique_increasing_reordering {N m : ℕ} (f : Fin m → Fin N)
    (hf : Function.Injective f) :
    ∃! τ : Permutation m, StrictMono (f ∘ τ) := by
  refine ⟨Tuple.sort f, ?_, ?_⟩
  · exact (Tuple.monotone_sort f).strictMono_of_injective
      (hf.comp (Tuple.sort f).injective)
  · intro τ hτ
    apply Equiv.ext
    intro i
    apply hf
    exact congrFun (Tuple.unique_monotone hτ.monotone (Tuple.monotone_sort f)) i

private theorem increasing_reordering_card {N m : ℕ} (e : Fin m ↪ Fin N)
    (τ : Permutation m) :
    (Finset.univ.filter (fun π : Permutation N =>
      StrictMono (fun i => π (e (τ i))))).card =
      (increasingAlongEvent e).card := by
  let er : Fin m ≃ Set.range e := Equiv.ofInjective e e.injective
  let p : Permutation N := τ.extendDomain er
  have hp (i : Fin m) : p (e i) = e (τ i) :=
    τ.extendDomain_apply_image er i
  let b : Permutation N ≃ Permutation N :=
    { toFun := fun π => p.trans π
      invFun := fun π => p.symm.trans π
      left_inv := by intro π; ext i; simp
      right_inv := by intro π; ext i; simp }
  have hb (π : Permutation N) :
      StrictMono (fun i => π (e (τ i))) ↔ increasingAlong e (b π) := by
    simp only [increasingAlong, b, Equiv.coe_fn_mk, Equiv.trans_apply, hp]
  simpa only [increasingAlongEvent, Fintype.card_subtype] using
    Fintype.card_congr (b.subtypeEquiv hb)

private theorem increasingAlong_card_mul_factorial {N m : ℕ} (e : Fin m ↪ Fin N) :
    (increasingAlongEvent e).card * m.factorial = N.factorial := by
  let q : Permutation N → Permutation m → ℕ :=
    fun π τ => if StrictMono (fun i => π (e (τ i))) then 1 else 0
  have hrow (π : Permutation N) : ∑ τ, q π τ = 1 := by
    obtain ⟨τ, hτ, huniq⟩ :=
      unique_increasing_reordering (fun i => π (e i)) (π.injective.comp e.injective)
    rw [Finset.sum_eq_single τ]
    · simp only [q, Function.comp_def] at hτ ⊢
      simp [hτ]
    · intro b _ hb
      simp only [q, ite_eq_right_iff, one_ne_zero, imp_false]
      intro h
      exact hb (huniq b h)
    · simp
  have hcol (τ : Permutation m) :
      ∑ π, q π τ = (increasingAlongEvent e).card := by
    simpa only [q, Finset.card_eq_sum_ones, Finset.sum_filter] using
      increasing_reordering_card e τ
  calc
    (increasingAlongEvent e).card * m.factorial =
        ∑ τ : Permutation m, (increasingAlongEvent e).card := by
          simp [Permutation, Fintype.card_perm, Nat.mul_comm]
    _ = ∑ τ : Permutation m, ∑ π : Permutation N, q π τ := by
          simp_rw [hcol]
    _ = ∑ π : Permutation N, ∑ τ : Permutation m, q π τ := Finset.sum_comm
    _ = N.factorial := by simp_rw [hrow]; simp [Permutation, Fintype.card_perm]

private theorem probability_increasingAlong {N m : ℕ} (e : Fin m ↪ Fin N) :
    probability (uniformPermutation N) (increasingAlong e) =
      1 / (m.factorial : ℝ) := by
  rw [uniformPermutation, Ascent.uniform_probability]
  simp only [Permutation, Fintype.card_perm, Fintype.card_fin, Fintype.card_subtype]
  have hc := congrArg (fun n : ℕ => (n : ℝ)) (increasingAlong_card_mul_factorial e)
  simp only [Nat.cast_mul] at hc
  apply (div_eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))).mpr
  simpa only [one_mul, increasingAlongEvent] using hc

private def windowEmbedding (N m a : ℕ) (h : a + m ≤ N) : Fin m ↪ Fin N where
  toFun i := ⟨a + i.val, lt_of_lt_of_le (Nat.add_lt_add_left i.isLt a) h⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val hij)

private theorem increasing_window_iff {N m a : ℕ} (h : a + m ≤ N)
    (π : Permutation N) :
    increasingAlong (windowEmbedding N m a h) π ↔
      ∀ i j : Fin N, a ≤ i.val → j.val < a + m → i < j → π i < π j := by
  constructor
  · intro hs i j hi hj hij
    let ii : Fin m := ⟨i.val - a, by have := i.isLt; have := j.isLt; omega⟩
    let jj : Fin m := ⟨j.val - a, by have := i.isLt; have := j.isLt; omega⟩
    have he_i : windowEmbedding N m a h ii = i := by
      apply Fin.ext
      change a + (i.val - a) = i.val
      omega
    have he_j : windowEmbedding N m a h jj = j := by
      apply Fin.ext
      change a + (j.val - a) = j.val
      omega
    rw [← he_i, ← he_j]
    apply hs
    change i.val - a < j.val - a
    omega
  · intro hs i j hij
    apply hs
    · change a ≤ a + i.val
      omega
    · change a + j.val < a + m
      exact Nat.add_lt_add_left j.isLt a
    · change a + i.val < a + j.val
      exact Nat.add_lt_add_left hij a

private theorem run_iff_exists_window {N m : ℕ} (hm : m ≤ N) (π : Permutation N) :
    HasIncreasingRun π m ↔ ∃ a : Fin (N-m+1),
      increasingAlong (windowEmbedding N m a.val (by have := a.isLt; omega)) π := by
  constructor
  · rintro ⟨a, ha, hs⟩
    refine ⟨⟨a, by omega⟩, ?_⟩
    exact (increasing_window_iff ha π).mpr hs
  · rintro ⟨a, ha⟩
    have hav : a.val + m ≤ N := by have := a.isLt; omega
    exact ⟨a.val, hav, (increasing_window_iff hav π).mp ha⟩

/-- The exact number N-m+1 of possible contiguous starts enters the null bound. -/
theorem probability_increasingRun_le {N m : ℕ} (hm : m ≤ N) :
    probability (uniformPermutation N) (fun π => HasIncreasingRun π m) ≤
      ((N-m+1 : ℕ) : ℝ)/(m.factorial : ℝ) := by
  simp_rw [run_iff_exists_window hm]
  calc
    _ ≤ ∑ a : Fin (N-m+1), probability (uniformPermutation N)
        (increasingAlong (windowEmbedding N m a.val (by have := a.isLt; omega))) :=
      Ascent.probability_iUnion_le _ _
    _ = ∑ _a : Fin (N-m+1), 1/(m.factorial : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      exact probability_increasingAlong _
    _ = _ := by simp [div_eq_mul_inv]

private theorem sortedWord_full_rank_iff {k N K : ℕ} {cuts : Cuts k N K}
    (ω : Sample cuts) (w : Word k K) (i : Fin N) :
    sortedWord ω i = w ↔
      lowerRank (fullPrefix w) ω ≤ i.val ∧ i.val < upperRank (fullPrefix w) ω := by
  have h := (Model.prefixRanks cuts ω (fullPrefix w)).1 i
  have ht : (sortedWord ω i).toList.take K = (sortedWord ω i).toList := by
    simpa only [List.Vector.toList_length] using
      (List.take_length (l := (sortedWord ω i).toList))
  simp only [fullPrefix, Fin.val_last, ht] at h
  constructor
  · intro he
    exact h.mp (congrArg List.Vector.toList he)
  · intro hi
    exact Subtype.ext (h.mpr hi)

/-- Canonical full-word counts force an observable run under the canonical stable sort. -/
theorem fullWord_forces_increasingRun {k N K : ℕ} {cuts : Cuts k N K}
    (ω : Sample cuts) (w : Word k K) (m : ℕ) (hm : 1 ≤ m)
    (hc : m ≤ wordCount w ω) : HasIncreasingRun (stableSort ω) m := by
  have hbound : upperRank (fullPrefix w) ω ≤ N :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin N)
  have hcount := (Model.prefixRanks cuts ω (fullPrefix w)).2
  change upperRank (fullPrefix w) ω - lowerRank (fullPrefix w) ω = wordCount w ω at hcount
  refine ⟨lowerRank (fullPrefix w) ω, by omega, ?_⟩
  intro i j hi hj hij
  have hiw := (sortedWord_full_rank_iff ω w i).mpr ⟨hi, by
    have hij' : i.val < j.val := hij
    omega⟩
  have hjw := (sortedWord_full_rank_iff ω w j).mpr ⟨by
    have hij' : i.val < j.val := hij
    omega, by omega⟩
  exact Model.stableTie cuts ω i j hij (hiw.trans hjw.symm)

/-- The frozen finite largest-word TV inequality for the physical chronological inverse law. -/
theorem finiteLargestWordTV : Targets.FiniteLargestWordTV := by
  intro k N K cuts hN m hm hmN hmean
  obtain ⟨w, _hw, _hwmean, htail⟩ := Thinning.maximalWordTail cuts hN
  let A := fun π : Permutation N => HasIncreasingRun π m
  have hsuccess : 1 - Real.exp (-chernoffConstant * maximalMean cuts hN) ≤
      probability (matrixLaw cuts) A := by
    have hgood : 1 - Real.exp (-chernoffConstant * maximalMean cuts hN) ≤
        probability (fixedCountPMF cuts) (fun ω => m ≤ wordCount w ω) := by
      have hc := Ascent.probability_not (fixedCountPMF cuts)
        (fun ω => wordCount w ω < m)
      simp only [not_lt] at hc
      rw [hc]
      exact sub_le_sub_left (htail m hmean) 1
    have hmap : probability (matrixLaw cuts) A =
        probability (fixedCountPMF cuts) (fun ω => A (stableSort ω)) := by
      unfold matrixLaw probability
      exact Model.expect_map _ _ _
    rw [hmap]
    apply hgood.trans
    apply Ascent.probability_mono
    intro ω hω
    exact fullWord_forces_increasingRun ω w m (by omega) hω
  have hnull := probability_increasingRun_le hmN
  have htv := Ascent.probability_sub_le_tv (matrixLaw cuts) (uniformPermutation N) A
  rw [Model.physicalMatrixBridge]
  dsimp [A] at hsuccess htv
  linarith

end RiffleLowerV2.EmpiricalLower
