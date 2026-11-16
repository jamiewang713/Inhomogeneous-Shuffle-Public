import RiffleUpperV2.Exploration.Guards
import RiffleLowerV2.Thinning.MaximalWord

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Exploration
open TimeProfile

private theorem ordered_three {α : Type*} [LinearOrder α] (P : α → Prop)
    {a b c : α} (ha : P a) (hb : P b) (hc : P c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ x y z, P x ∧ P y ∧ P z ∧ x < y ∧ y < z := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · rcases lt_or_gt_of_ne hbc with hbc | hcb
    · exact ⟨a,b,c,ha,hb,hc,hab,hbc⟩
    · rcases lt_or_gt_of_ne hac with hac | hca
      · exact ⟨a,c,b,ha,hc,hb,hac,hcb⟩
      · exact ⟨c,a,b,hc,ha,hb,hca,hab⟩
  · rcases lt_or_gt_of_ne hac with hac | hca
    · exact ⟨b,a,c,hb,ha,hc,hba,hac⟩
    · rcases lt_or_gt_of_ne hbc with hbc | hcb
      · exact ⟨b,c,a,hb,hc,ha,hbc,hca⟩
      · exact ⟨c,b,a,hc,hb,ha,hcb,hba⟩

/-- The two good coordinates contribute g twice; every other coordinate contributes 1/k. -/
theorem reserve_product_lower {d k D : ℕ} (hk : 1 ≤ k) (hdD : d ≤ D)
    {g : ℝ} (hg : 0 ≤ g) (a b : Fin d) (hab : a ≠ b) (f : Fin d → ℝ)
    (hgood : g ≤ f a ∧ g ≤ f b)
    (hrest : ∀ r, r ≠ a → r ≠ b → 1/(k : ℝ) ≤ f r) :
    reserveMass k D g ≤ ∏ r, f r := by
  let q : ℝ := 1/(k : ℝ)
  have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := (div_le_one hkpos).mpr (by exact_mod_cast hk)
  have hprod : (∏ r : Fin d, q*(if r=a ∨ r=b then g else 1)) ≤ ∏ r, f r := by
    apply Finset.prod_le_prod
    · intro r _
      split_ifs <;> positivity
    · intro r _
      by_cases hra : r=a
      · subst r
        simp only [true_or, if_true]
        exact (mul_le_of_le_one_left hg hq1).trans hgood.1
      · by_cases hrb : r=b
        · subst r
          simp only [or_true, if_true]
          exact (mul_le_of_le_one_left hg hq1).trans hgood.2
        · simpa [hra, hrb, q] using hrest r hra hrb
  have hs : (∏ r : Fin d, if r=a ∨ r=b then g else 1) = g^2 := by
    calc
      _ = ∏ r ∈ ({a,b} : Finset (Fin d)), if r=a ∨ r=b then g else 1 := by
        symm
        apply Finset.prod_subset (Finset.subset_univ _)
        intro r _ hr
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
        simp [hr.1,hr.2]
      _ = _ := by simp [hab, hab.symm]; ring
  rw [Finset.prod_mul_distrib, hs] at hprod
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  have hpow : (k : ℝ)^(-(D : ℝ)) ≤ q^d := by
    calc
      _ = q^D := by simp [q, Real.rpow_neg, Real.rpow_natCast, one_div, inv_pow]
      _ ≤ q^d := pow_le_pow_of_le_one hq0 hq1 hdD
  unfold reserveMass
  exact (mul_le_mul_of_nonneg_left hpow (sq_nonneg g)).trans (by nlinarith [hprod])

/-- At every column, a deterministic maximal-count digit has fraction at least 1/k. -/
theorem exists_large_digits {k n K : ℕ} (cuts : Cuts k n K) (hn : 0 < n) :
    ∃ f : Fin K → Fin k, ∀ j, 1/(k : ℝ) ≤ (cuts.count j (f j) : ℝ)/n := by
  obtain ⟨w, hw⟩ := RiffleLowerV2.Thinning.exists_canonicalMaxWord cuts hn
  refine ⟨fun j => w.get j, ?_⟩
  intro j
  have hsum : n ≤ k*cuts.count j (w.get j) := by
    calc
      n = ∑ a, cuts.count j a := (cuts.sum_count j).symm
      _ ≤ ∑ _a : Fin k, cuts.count j (w.get j) := Finset.sum_le_sum (fun a _ => (hw j).1 a)
      _ = _ := by simp
  have hkpos : (0:ℝ)<k := by
    have hp : 0 < k := by nlinarith
    exact_mod_cast hp
  have hnpos : (0:ℝ)<n := by exact_mod_cast hn
  apply (div_le_div_iff₀ hkpos hnpos).mpr
  have hh : (n : ℝ) ≤ (k : ℝ)*(cuts.count j (w.get j) : ℝ) := by exact_mod_cast hsum
  nlinarith

def modifiedTail {k d : ℕ} (base : Fin d → Fin k) (a b : Fin d) (u v : Fin k) : Word k d :=
  List.Vector.ofFn (fun r => if r=a then u else if r=b then v else base r)

/-- Actual reserve existence from the two later good columns in the retained cluster. -/
theorem reserveCandidates_nonempty {k n L : ℕ} (cuts : Cuts k n (L+1)) (hn : 0 < n)
    (hk : 1 ≤ k) (D : ℕ) {g : ℝ} (hg : 0 ≤ g)
    (hc : retainedGoodCluster cuts hn D g) : (reserveCandidates cuts D g).Nonempty := by
  obtain ⟨_,j₁,j₂,hj₁,hj₁₂,hj₂,hgood₁,hgood₂⟩ := hc
  let a : Fin (min D L) := ⟨j₁.val-1, by have := j₁.isLt; have := j₂.isLt; omega⟩
  let b : Fin (min D L) := ⟨j₂.val-1, by have := j₂.isLt; omega⟩
  have hab : a ≠ b := by intro he; have hh := congrArg Fin.val he; dsimp [a,b] at hh; exact (ne_of_lt hj₁₂) (Fin.ext (by omega))
  obtain ⟨u₁,v₁,huv₁,hu₁,hv₁⟩ := hgood₁
  obtain ⟨u₂,v₂,huv₂,hu₂,hv₂⟩ := hgood₂
  obtain ⟨base,hbase⟩ := exists_large_digits cuts hn
  let base' : Fin (min D L) → Fin k := fun r => base ⟨r.val+1, by have := r.isLt; omega⟩
  have ha : (⟨a.val+1, by have := a.isLt; omega⟩ : Fin (L+1)) = j₁ := by apply Fin.ext; dsimp [a]; omega
  have hb : (⟨b.val+1, by have := b.isLt; omega⟩ : Fin (L+1)) = j₂ := by apply Fin.ext; dsimp [b]; omega
  have hmass (u v : Fin k) (hu : g ≤ (cuts.count j₁ u : ℝ)/n) (hv : g ≤ (cuts.count j₂ v : ℝ)/n) :
      reserveMass k D g ≤ tailMass cuts D (modifiedTail base' a b u v) := by
    apply reserve_product_lower hk (min_le_left D L) hg a b hab
    · constructor
      · simpa [tailMass, modifiedTail, ha] using hu
      · simpa [tailMass, modifiedTail, hab.symm, hb] using hv
    · intro r hra hrb
      simpa [modifiedTail, hra, hrb, base'] using hbase ⟨r.val+1, by have := r.isLt; omega⟩
  let x := modifiedTail base' a b u₁ u₂
  let y := modifiedTail base' a b u₁ v₂
  let z := modifiedTail base' a b v₁ u₂
  have hx : reserveMass k D g ≤ tailMass cuts D x := hmass u₁ u₂ hu₁ hu₂
  have hy : reserveMass k D g ≤ tailMass cuts D y := hmass u₁ v₂ hu₁ hv₂
  have hz : reserveMass k D g ≤ tailMass cuts D z := hmass v₁ u₂ hv₁ hu₂
  have hxy : x ≠ y := by
    intro hh
    have hh' := congrArg (fun w => List.Vector.get w b) hh
    simp only [x,y,modifiedTail,List.Vector.get_ofFn,if_neg hab.symm,if_pos rfl] at hh'
    exact huv₂ hh'
  have hxz : x ≠ z := by
    intro hh
    have hh' := congrArg (fun w => List.Vector.get w a) hh
    simp only [x,z,modifiedTail,List.Vector.get_ofFn,if_pos rfl] at hh'
    exact huv₁ hh'
  have hyz : y ≠ z := by
    intro hh
    have hh' := congrArg (fun w => List.Vector.get w a) hh
    simp only [y,z,modifiedTail,List.Vector.get_ofFn,if_pos rfl] at hh'
    exact huv₁ hh'
  obtain ⟨x',y',z',hx',hy',hz',hxy',hyz'⟩ := ordered_three
    (fun w => reserveMass k D g ≤ tailMass cuts D w) hx hy hz hxy hxz hyz
  refine ⟨toLex (x',toLex (y',z')), ?_⟩
  simp only [reserveCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hxy',hyz',hx',hy',hz'⟩

theorem chosenReserves_of_retainedGoodCluster {k n L : ℕ} (cuts : Cuts k n (L+1)) (hn : 0 < n)
    (hk : 1 ≤ k) (D : ℕ) {g : ℝ} (hg : 0 ≤ g)
    (hc : retainedGoodCluster cuts hn D g) : ∃ v, chosenReserves cuts D g = some v :=
  (chosenReserves_exists_iff cuts D g).2 (reserveCandidates_nonempty cuts hn hk D hg hc)

end RiffleUpperV2.Exploration
