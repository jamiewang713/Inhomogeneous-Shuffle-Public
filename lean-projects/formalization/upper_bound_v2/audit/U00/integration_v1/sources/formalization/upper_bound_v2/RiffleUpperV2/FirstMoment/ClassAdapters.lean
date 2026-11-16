import RiffleUpperV2.FirstMoment.WordCosts
import RiffleUpperV2.FirstMoment.BoundaryCosts

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization

/-- Canonical completions introduce no multiplicity when the recorded length agrees. -/
theorem completePrefix_injective_of_length {k d : ℕ} (default : Fin d → Fin k)
    {x y : Prefix k d} (hlen : x.1 = y.1)
    (hcomplete : completePrefix default x = completePrefix default y) : x = y := by
  rcases x with ⟨m,x⟩
  rcases y with ⟨m',y⟩
  dsimp at hlen
  subst m'
  apply Sigma.ext (by rfl)
  apply heq_of_eq
  apply List.Vector.ext
  intro i
  let j : Fin d := ⟨i.val, by have := m.isLt; omega⟩
  have h := congrFun hcomplete j
  simpa [completePrefix, j, i.isLt] using h

/-- Fixed-prefix words of equal length have identical canonical digits outside
 their extension interval. This is the map needed by the actual entropy classes. -/
theorem completePrefix_agree_outside_extension {k d : ℕ} (default : Fin d → Fin k)
    {v x y : Prefix k d} (hvx : IsPrefix v x) (hvy : IsPrefix v y)
    (hlen : x.1.val = y.1.val) (j : Fin d)
    (hj : j ∉ empiricalPositions d 0 v.1.val x.1.val) :
    completePrefix default x j = completePrefix default y j := by
  have hvlen := prefix_length_le hvx
  have hj' : ¬ (v.1.val ≤ j.val ∧ j.val < x.1.val) := by
    simpa [empiricalPositions] using hj
  by_cases hix : j.val < x.1.val
  · have hiv : j.val < v.1.val := by omega
    have hiy : j.val < y.1.val := by omega
    have hxget : v.2.get ⟨j.val,hiv⟩ = x.2.get ⟨j.val,hix⟩ := by
      simpa [List.Vector.get, List.Vector.toList] using hvx.getElem (by simpa using hiv)
    have hyget : v.2.get ⟨j.val,hiv⟩ = y.2.get ⟨j.val,hiy⟩ := by
      simpa [List.Vector.get, List.Vector.toList] using hvy.getElem (by simpa using hiv)
    simpa [completePrefix,hix,hiy] using hxget.symm.trans hyget
  · have hiy : ¬ j.val < y.1.val := by omega
    simp [completePrefix,hix,hiy]

/-- Natural and integer bins agree for the nonnegative actual selected costs. -/
theorem goodCost_natBin_eq_intBin {J : Type*} [Fintype J] [DecidableEq J] {k N : ℕ}
    (hN : 2 ≤ N) (p : J → Simplex k) (I : Finset J) (chi width : ℝ)
    (hwidth : 0 < width) (w : J → Fin k)
    (hlegal : ∀ j ∈ I, 0 < prob (p j) (w j)) :
    (⌊goodCost N p I chi w/width⌋₊ : ℤ) = ⌊goodCost N p I chi w/width⌋ := by
  apply Int.natCast_floor_eq_floor
  apply div_nonneg _ hwidth.le
  exact selectedCost_nonneg hN p _ w (fun j hj => hlegal j (Finset.mem_sdiff.mp hj).1)

/-- The actual finite descriptor's natural bin implies the entropy class's integer bin. -/
theorem mem_costClass_of_natBin {J : Type*} [Fintype J] [DecidableEq J] {k N : ℕ}
    (hN : 2 ≤ N) (p : J → Simplex k) (I : Finset J) (chi width : ℝ)
    (hwidth : 0 < width) (w0 w : J → Fin k)
    (hlegal0 : ∀ j ∈ I, 0 < prob (p j) (w0 j))
    (hlegal : ∀ j ∈ I, 0 < prob (p j) (w j))
    (hout : ∀ j ∉ I, w j = w0 j)
    (hQ : exceptionalPositions p I chi w = exceptionalPositions p I chi w0)
    (hvalues : ∀ j ∈ exceptionalPositions p I chi w0, w j = w0 j)
    (hbin : ⌊goodCost N p I chi w/width⌋₊ = ⌊goodCost N p I chi w0/width⌋₊) :
    w ∈ costClass N p I chi width w0 := by
  classical
  have heq : ⌊goodCost N p I chi w/width⌋ = ⌊goodCost N p I chi w0/width⌋ := by
    rw [← goodCost_natBin_eq_intBin hN p I chi width hwidth w hlegal,
      ← goodCost_natBin_eq_intBin hN p I chi width hwidth w0 hlegal0, hbin]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hout,hlegal,hQ,hvalues,heq⟩

/-- Each good selected digit costs at most log(1/chi), without a lower bound
 on exceptional digit probabilities. -/
theorem goodCost_le_horizon {k n d N : ℕ} (hN : 2 ≤ N)
    (cuts : Cuts k n d) (hn : 0 < n) (I : Finset (Fin d))
    (chi : ℝ) (hchi : 0 < chi) (hchi1 : chi ≤ 1) (w : Fin d → Fin k)
    {T : ℝ} (hd : (d : ℝ) ≤ T*logScale N) :
    goodCost N (cuts.profile hn) I chi w ≤ T*Real.log (1/chi) := by
  classical
  let G := goodPositions (cuts.profile hn) I chi w
  have hlog : 0 ≤ Real.log (1/chi) := Real.log_nonneg ((one_le_div hchi).mpr hchi1)
  have hc : (G.card : ℝ) ≤ d := by exact_mod_cast (show G.card ≤ d by simpa using Finset.card_le_univ G)
  have hs : (∑ j ∈ G, digitCost (prob (cuts.profile hn j) (w j))) ≤
      (G.card : ℝ)*Real.log (1/chi) := by
    calc
      _ ≤ ∑ _j ∈ G, Real.log (1/chi) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjI := (Finset.mem_sdiff.mp hj).1
        have hrare := (Finset.mem_sdiff.mp hj).2
        have hp : chi ≤ prob (cuts.profile hn j) (w j) := by
          simpa [exceptionalPositions,hjI] using hrare
        exact Real.log_le_log (one_div_pos.mpr (hchi.trans_le hp))
          (one_div_le_one_div_of_le hchi hp)
      _ = _ := by simp
  have hmul := mul_le_mul_of_nonneg_right (hc.trans hd) hlog
  apply (div_le_iff₀ (logScale_pos hN)).mpr
  dsimp [goodCost,selectedCost,G] at hs ⊢
  nlinarith

/-- The fixed number of cost bins is uniform over the arrays. -/
theorem goodCost_bin_bound {k n d N : ℕ} (hN : 2 ≤ N)
    (cuts : Cuts k n d) (hn : 0 < n) (I : Finset (Fin d))
    (chi width : ℝ) (hchi : 0 < chi) (hchi1 : chi ≤ 1) (hwidth : 0 < width)
    (w : Fin d → Fin k) {T : ℝ} (hd : (d : ℝ) ≤ T*logScale N) :
    ⌊goodCost N (cuts.profile hn) I chi w/width⌋₊ <
      1+⌊T*Real.log (1/chi)/width⌋₊ := by
  have h := Nat.floor_mono (div_le_div_of_nonneg_right
    (goodCost_le_horizon hN cuts hn I chi hchi hchi1 w hd) hwidth.le)
  omega

/-- The terminal occupancy formula is the existing literal prefix mean. -/
theorem fullWordMean_eq_prefixMean {k n L : ℕ} (cuts : Cuts k n L) (hn : 0 < n)
    (w : Fin L → Fin k) :
    fullWordMean cuts hn w =
      prefixMean cuts (RiffleLowerV2.fullPrefix (List.Vector.ofFn w)) := by
  unfold fullWordMean RiffleUpperV2.prefixMean RiffleLowerV2.prefixMean
    RiffleLowerV2.prefixMass RiffleLowerV2.fullPrefix
  simp [Cuts.profile_prob]

/-- An actual finite prefix family with fixed descriptor data injects into the
cost class. Additional boundary/routing restrictions may shrink W arbitrarily. -/
theorem prefixFamilyEntropy {k n d N : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    (cuts : Cuts k n d) (hn : 0 < n) (default : Fin d → Fin k)
    (v w0 : Prefix k d) (W : Finset (Prefix k d)) (hw0 : w0 ∈ W)
    (I : Finset (Fin d)) (hI : I = empiricalPositions d 0 v.1.val w0.1.val)
    (chi width theta alpha : ℝ) (hwidth : 0 < width)
    (htheta : theta ∈ Set.Icc (3 : ℝ) 4)
    (hlen : ∀ x ∈ W, x.1.val = w0.1.val)
    (hprefix : ∀ x ∈ W, IsPrefix v x)
    (hlegal : ∀ x ∈ W, ∀ j ∈ I, 0 < prob (cuts.profile hn j) (completePrefix default x j))
    (hQ : ∀ x ∈ W, exceptionalPositions (cuts.profile hn) I chi (completePrefix default x) =
      exceptionalPositions (cuts.profile hn) I chi (completePrefix default w0))
    (hvalues : ∀ x ∈ W, ∀ j ∈ exceptionalPositions (cuts.profile hn) I chi (completePrefix default w0),
      completePrefix default x j = completePrefix default w0 j)
    (hbin : ∀ x ∈ W, ⌊goodCost N (cuts.profile hn) I chi (completePrefix default x)/width⌋₊ =
      ⌊goodCost N (cuts.profile hn) I chi (completePrefix default w0)/width⌋₊)
    (hbudget : ((exceptionalPositions (cuts.profile hn) I chi (completePrefix default w0)).card : ℝ) ≤
      alpha*logScale N) :
    Real.log (W.card : ℝ)/logScale N ≤
      theta*goodCost N (cuts.profile hn) I chi (completePrefix default w0)-
        (∑ j ∈ I, psi (cuts.profile hn j) theta)/logScale N+
        (4*width+4*Real.log (k : ℝ)*alpha) := by
  classical
  let words := W.image (completePrefix default)
  have hc : words.card = W.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    apply completePrefix_injective_of_length default _ hxy
    apply Fin.ext
    exact (hlen x hx).trans (hlen y hy).symm
  have hwords : words.Nonempty := ⟨completePrefix default w0,Finset.mem_image.mpr ⟨w0,hw0,rfl⟩⟩
  have hsub : words ⊆ costClass N (cuts.profile hn) I chi width (completePrefix default w0) := by
    intro w hw
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hw
    apply mem_costClass_of_natBin hN (cuts.profile hn) I chi width hwidth
      (completePrefix default w0) (completePrefix default x) (hlegal w0 hw0) (hlegal x hx)
      ?_ (hQ x hx) (hvalues x hx) (hbin x hx)
    intro j hj
    apply completePrefix_agree_outside_extension default (hprefix x hx) (hprefix w0 hw0)
      (hlen x hx) j
    simpa [hI,hlen x hx] using hj
  have h := refinedClassEntropy hk hN (cuts.profile hn) I chi width theta alpha hwidth
    htheta (completePrefix default w0) (hlegal w0 hw0) hbudget words hwords hsub
  simpa only [hc] using h

end RiffleUpperV2.FirstMoment
