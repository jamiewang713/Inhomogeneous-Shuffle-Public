import RiffleUpperV2.Conditional.PrefixAdapters
import RiffleUpperV2.Conditional.RegimePowers
import RiffleUpperV2.Reservoir.BackwardCounts

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Conditional
open TimeProfile Exploration Reservoir
attribute [local instance 2000] Reservoir.wordDecEq

/-- Actual tiny-cylinder count in either natural spatial direction. Constants
are selected before the population, array, history, prefix and regime exponent. -/
theorem tinyCylinder_count (k D : ℕ) (hk : 0<k) (hD : 1≤D)
    (g tau T : ℝ) (hg : 0<g) (hg1 : g<1) (htau : 0<tau) (htaug : tau<g) (hT : 0<T)
    (halpha : Real.log (1/g)/Real.log (1/tau)<1/2) :
    ∃ C1 : ℝ, 0<C1 ∧ ∃ N0 : ℕ, 2≤N0 ∧ ∀ n : ℕ, N0≤n → ∀ L : ℕ,
      ((L+1 : ℕ) : ℝ)≤T*Real.log (n : ℝ) → ∀ cuts : Cuts k n (L+1), ∀ hn : 0<n,
      GoodColumn (cuts.profile hn 0) g → ∀ xi epsilon : ℝ, 0≤epsilon → ∀ p : Fin k,
      ∀ d : Direction, ∀ omega : Sample cuts, ∀ j : Fin (pileSize cuts p),
      positiveHistory cuts p d (j.val+1) omega →
      historyGood cuts D g xi epsilon p d (j.val+1) omega →
      hasDirection cuts D g d (sortedWord omega (pilePosition cuts p d j)) →
      ∀ x : Prefix k (L+1), 0<x.1.val →
      (∀ w : Word k (L+1), inCylinder x w → w.get 0=p) →
      (∀ w : Word k (L+1), inCylinder x w → match d with
        | .forward => sortedWord omega (pilePosition cuts p d j)<w
        | .backward => w<sortedWord omega (pilePosition cuts p d j)) →
      prefixMean cuts x≤(n : ℝ)^(-xi) →
      conditionalExpect (fixedCountPMF cuts) (fun z => (RiffleUpperV2.prefixCount x z : ℝ))
        (historyFiber cuts p d (j.val+1) omega) ≤
        C1*(n : ℝ)^(-xi+(Real.log (1/g)/Real.log (1/tau))*(1+xi))+(n : ℝ)*epsilon := by
  obtain ⟨Cf,hCf,Nf,hNf,hf⟩ := Reservoir.prefixCount k D hk hD g tau T hg hg1 htau htaug hT halpha
  obtain ⟨Cb,hCb,Nb,hNb,hb⟩ := Reservoir.Backward.prefixCount k D hk hD g tau T hg hg1 htau htaug hT halpha
  let C1 := max Cf Cb
  have hC1 : 0<C1 := hCf.trans_le (le_max_left _ _)
  refine ⟨C1,hC1,Nf+Nb+2,by omega,?_⟩
  intro n hnn L hL cuts hn hgood xi epsilon hepsilon p d omega j hpos hhist hdir x hx hp hfuture htiny
  obtain ⟨E,v,hxv⟩ := tailBinPrefix_of_cylinder p x hx hp
  have hv (w : Word k (L+1)) (hwp : w.get 0=p) (hwt : tailPrefix E w=v) : inCylinder x w := by
    rw [← hxv]
    exact (inCylinder_tailBinPrefix E p v w).mpr ⟨hwp,hwt⟩
  have hmass : 0≤RiffleUpperV2.prefixMass cuts x := by
    unfold RiffleUpperV2.prefixMass RiffleLowerV2.prefixMass
    positivity
  have hraw : conditionalExpect (fixedCountPMF cuts) (fun z => (RiffleUpperV2.prefixCount x z : ℝ))
      (historyFiber cuts p d (j.val+1) omega) ≤
      C1*n*(RiffleUpperV2.prefixMass cuts x)^(1-Real.log (1/g)/Real.log (1/tau))+n*epsilon := by
    cases d with
    | forward =>
      have h := hf n (by omega) L hL cuts hn hgood xi epsilon hepsilon p omega j hpos hhist hdir E v
        (fun w hwp hwt => hfuture w (hv w hwp hwt))
      rw [hxv] at h
      apply h.trans
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left Cf Cb)
        (Nat.cast_nonneg n)) (Real.rpow_nonneg hmass _)
    | backward =>
      have h := hb n (by omega) L hL cuts hn hgood xi epsilon hepsilon p omega j hpos hhist hdir E v
        (fun w hwp hwt => hfuture w (hv w hwp hwt))
      rw [hxv] at h
      apply h.trans
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right Cf Cb)
        (Nat.cast_nonneg n)) (Real.rpow_nonneg hmass _)
  have hpower := tinyCount_power (N := (n : ℝ)) (ξ := xi)
    (α := Real.log (1/g)/Real.log (1/tau)) (by exact_mod_cast hn) hmass (by linarith) htiny
  apply hraw.trans
  apply add_le_add _ le_rfl
  calc
    _ = C1*((n : ℝ)*(RiffleUpperV2.prefixMass cuts x)^(1-Real.log (1/g)/Real.log (1/tau))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpower hC1.le

/-- Actual collision count in the intermediate mean regime, in either natural
spatial direction. The original terminal margin is an explicit scalar input. -/
theorem intermediateCylinder_collisions (k D : ℕ) (hk : 0<k) (hD : 1≤D)
    (g tau T : ℝ) (hg : 0<g) (hg1 : g<1) (htau : 0<tau) (htaug : tau<g) (hT : 0<T)
    (halpha : Real.log (1/g)/Real.log (1/tau)<1/2) :
    ∃ C2 : ℝ, 0<C2 ∧ ∃ N0 : ℕ, 2≤N0 ∧ ∀ n : ℕ, N0≤n → ∀ L : ℕ,
      ((L+1 : ℕ) : ℝ)≤T*Real.log (n : ℝ) → ∀ cuts : Cuts k n (L+1), ∀ hn : 0<n,
      GoodColumn (cuts.profile hn 0) g → ∀ xi eta epsilon : ℝ, 0≤epsilon → ∀ p : Fin k,
      ∀ d : Direction, ∀ omega : Sample cuts, ∀ j : Fin (pileSize cuts p),
      positiveHistory cuts p d (j.val+1) omega →
      historyGood cuts D g xi epsilon p d (j.val+1) omega →
      hasDirection cuts D g d (sortedWord omega (pilePosition cuts p d j)) →
      ∀ x : Prefix k (L+1), 0<x.1.val →
      (∀ w : Word k (L+1), inCylinder x w → w.get 0=p) →
      (∀ w : Word k (L+1), inCylinder x w → match d with
        | .forward => sortedWord omega (pilePosition cuts p d j)<w
        | .backward => w<sortedWord omega (pilePosition cuts p d j)) →
      (n : ℝ)^(-xi)≤prefixMean cuts x → prefixMean cuts x≤(n : ℝ)^xi →
      empiricalBeta n 0 cuts hn (L+1)≤-eta →
      conditionalExpect (fixedCountPMF cuts) (fun z => ∑ w : Word k (L+1),
        if inCylinder x w then ((wordCount z w).choose 2 : ℝ) else 0)
        (historyFiber cuts p d (j.val+1) omega) ≤
        C2*(n : ℝ)^(-eta+3*xi+2*(Real.log (1/g)/Real.log (1/tau))*(1+eta-2*xi))+(n : ℝ)^2*epsilon := by
  obtain ⟨Cf,hCf,Nf,hNf,hf⟩ := Reservoir.tailCollisions k D hk hD g tau T hg hg1 htau htaug hT halpha
  obtain ⟨Cb,hCb,Nb,hNb,hb⟩ := Reservoir.Backward.tailCollisions k D hk hD g tau T hg hg1 htau htaug hT halpha
  let C2 := max Cf Cb
  have hC2 : 0<C2 := hCf.trans_le (le_max_left _ _)
  refine ⟨C2,hC2,Nf+Nb+2,by omega,?_⟩
  intro n hnn L hL cuts hn hgood xi eta epsilon hepsilon p d omega j hpos hhist hdir x hx hp hfuture hlow hupp hterminal
  obtain ⟨E,v,hxv⟩ := tailBinPrefix_of_cylinder p x hx hp
  have hv (w : Word k (L+1)) (hwp : w.get 0=p) (hwt : tailPrefix E w=v) : inCylinder x w := by
    rw [← hxv]
    exact (inCylinder_tailBinPrefix E p v w).mpr ⟨hwp,hwt⟩
  have hmass : 0≤RiffleUpperV2.prefixMass cuts x := by
    unfold RiffleUpperV2.prefixMass RiffleLowerV2.prefixMass
    positivity
  have htail : 0≤tailPowerMass cuts x (2*(1-Real.log (1/g)/Real.log (1/tau))) := by
    unfold tailPowerMass
    apply Finset.prod_nonneg
    intro _ _
    split_ifs
    · norm_num
    · exact Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (by positivity) _)
  have hraw : conditionalExpect (fixedCountPMF cuts) (fun z => ∑ w : Word k (L+1),
        if inCylinder x w then ((wordCount z w).choose 2 : ℝ) else 0)
      (historyFiber cuts p d (j.val+1) omega) ≤
      C2*(n : ℝ)^2*(RiffleUpperV2.prefixMass cuts x)^(2*(1-Real.log (1/g)/Real.log (1/tau)))*
        tailPowerMass cuts x (2*(1-Real.log (1/g)/Real.log (1/tau)))+(n : ℝ)^2*epsilon := by
    cases d with
    | forward =>
      have h := hf n (by omega) L hL cuts hn hgood xi epsilon hepsilon p omega j hpos hhist hdir E v
        (fun w hwp hwt => hfuture w (hv w hwp hwt))
      rw [hxv] at h
      simp_rw [← inCylinder_iff_take] at h
      apply h.trans
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left Cf Cb) (sq_nonneg (n : ℝ)))
        (Real.rpow_nonneg hmass _)) htail
    | backward =>
      have h := hb n (by omega) L hL cuts hn hgood xi epsilon hepsilon p omega j hpos hhist hdir E v
        (fun w hwp hwt => hfuture w (hv w hwp hwt))
      rw [hxv] at h
      simp_rw [← inCylinder_iff_take] at h
      apply h.trans
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right Cf Cb) (sq_nonneg (n : ℝ)))
        (Real.rpow_nonneg hmass _)) htail
  have hmax := intermediate_maximalTail_le (show 2≤n by omega) cuts hn x hlow hterminal
  have htailmax := tailPowerMass_le_maximalTail cuts hn x
    (by linarith : 1<2*(1-Real.log (1/g)/Real.log (1/tau)))
  have hpower := intermediateCollision_power (by exact_mod_cast hn) hmass
    (maximalTailMass_pos cuts hn x).le halpha.le hupp hmax
    (by convert htailmax using 1 <;> congr 1 <;> ring)
  apply hraw.trans
  apply add_le_add _ le_rfl
  calc
    _ = C2*((n : ℝ)^2*(RiffleUpperV2.prefixMass cuts x)^(2*(1-Real.log (1/g)/Real.log (1/tau)))*
        tailPowerMass cuts x (2*(1-Real.log (1/g)/Real.log (1/tau)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpower hC2.le

end RiffleUpperV2.Conditional
