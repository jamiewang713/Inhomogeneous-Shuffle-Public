import RiffleUpperV2.EmpiricalUpper.Deletion
import RiffleUpperV2.Exploration.WindowClusters

noncomputable section
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.EmpiricalUpper
open TimeProfile RiffleLowerV2 Filter

/-- Reset the absolute column origin while retaining the original logarithmic scale. -/
theorem rebaseMargin {k N n L a : ℕ} (cuts : Cuts k n L) (hn : 0 < n)
    {η : ℝ} (h : EmpiricalNegativeMargin N a cuts hn η) :
    EmpiricalNegativeMargin N 0 cuts hn η := by
  constructor
  · simpa [empiricalBeta, empiricalA] using h.1
  · intro s u hs hsu hu
    have hh := h.2 (a+s) (a+u) (by omega) (by omega) (by omega)
    simpa [empiricalInf, empiricalExpression, empiricalBeta, empiricalA, empiricalB] using hh

theorem fullCost_le {k N K : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    (cuts : Cuts k N K) :
    empiricalA N 0 cuts (by omega) 0 K ≤
      (K : ℝ)*Real.log (k : ℝ)/logScale N := by
  simp only [empiricalA, gridSum, Nat.sub_zero, Nat.zero_le, true_and]
  have hs : (∑ j : Fin K, maxCost (cuts.profile (by omega) j)) ≤
      (K : ℝ)*Real.log (k : ℝ) := by
    calc
      _ ≤ ∑ _j : Fin K, Real.log (k : ℝ) :=
        Finset.sum_le_sum fun j _ => (maxCost_bounds hk _).2
      _ = _ := by simp
  simpa only [Finset.filter_true_of_mem (fun (j : Fin K) _ => j.isLt)] using
    div_le_div_of_nonneg_right hs (logScale_pos hN).le

/-- The terminal negative margin forces enough chronological columns before
any good-window or exploratory construction is selected. -/
theorem terminal_horizon {k N K : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    (cuts : Cuts k N K) {η0 : ℝ}
    (h : EmpiricalNegativeMargin N 0 cuts (by omega) η0) :
    (1+η0)*logScale N ≤ (K : ℝ)*Real.log (k : ℝ) := by
  have hz : Real.log (N : ℝ) ≠ 0 := (logScale_pos hN).ne'
  have hm := h.1
  simp only [empiricalBeta, Nat.zero_add, div_self hz] at hm
  have hc := fullCost_le hk hN cuts
  have hh : 1+η0 ≤ (K : ℝ)*Real.log (k : ℝ)/logScale N := by linarith
  exact (le_div_iff₀ (logScale_pos hN)).mp hh

/-- A finite, array-independent threshold suffices to fit the initial window. -/
theorem initialWindow_fits {k N K : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    (cuts : Cuts k N K) {η0 ρ : ℝ} (hη0 : 0 ≤ η0) (hρ : 0 ≤ ρ)
    (hbudget : ρ*Real.log (k : ℝ) ≤ 1/4)
    (hlarge : 4*Real.log (k : ℝ) ≤ logScale N)
    (hmargin : EmpiricalNegativeMargin N 0 cuts (by omega) η0) :
    Exploration.windowLength N ρ ≤ K := by
  have hklog : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast hk)
  have hz := logScale_pos hN
  have hc : (Exploration.windowLength N ρ : ℝ) < ρ*logScale N+2 := by
    have hh := Nat.ceil_lt_add_one (mul_nonneg hρ hz.le)
    simpa only [Exploration.windowLength, logScale, Nat.cast_add, Nat.cast_one] using
      (by linarith : (⌈ρ*logScale N⌉₊ : ℝ)+1 < ρ*logScale N+2)
  have hh := terminal_horizon hk hN cuts hmargin
  have hmul := mul_lt_mul_of_pos_right hc hklog
  have hb := mul_le_mul_of_nonneg_right hbudget hz.le
  have he := mul_nonneg hη0 hz.le
  have hfit : (Exploration.windowLength N ρ : ℝ)*Real.log (k : ℝ) <
      (K : ℝ)*Real.log (k : ℝ) := by nlinarith
  have hreal := (mul_lt_mul_iff_left₀ hklog).mp hfit
  exact le_of_lt (by exact_mod_cast hreal)

def restartIndex {K : ℕ} (r : Fin (K+1)) (j : Fin (K-r.val+1)) : Fin (K+1) :=
  ⟨r.val+j.val, by omega⟩

/-- The suffix has a successor length, as required by the concrete C interface. -/
def restartCuts {k N K : ℕ} (cuts : Cuts k N (K+1)) (r : Fin (K+1)) :
    Cuts k N (K-r.val+1) where
  count j := cuts.count (restartIndex r j)
  sum_count j := cuts.sum_count (restartIndex r j)

@[simp] theorem restartCuts_profile {k N K : ℕ} (cuts : Cuts k N (K+1))
    (r : Fin (K+1)) (hn : 0 < N) (j : Fin (K-r.val+1)) :
    (restartCuts cuts r).profile hn j = cuts.profile hn (restartIndex r j) := rfl

theorem restartCuts_heq_suffix {k N K : ℕ} (cuts : Cuts k N (K+1)) (r : Fin (K+1)) :
    HEq (restartCuts cuts r) (Margins.suffixCuts cuts r.val) := by
  apply cuts_heq (by omega)
  intro j j' hj l
  change cuts.count (restartIndex r j) l = cuts.count (Margins.suffixIndex r.val j') l
  congr 2
  apply Fin.ext
  dsimp [restartIndex, Margins.suffixIndex]
  omega

theorem restartTVContraction {k N K : ℕ} (cuts : Cuts k N (K+1)) (r : Fin (K+1)) :
    tv (physicalInverseLaw cuts) (uniformPermutation N) ≤
      tv (physicalInverseLaw (restartCuts cuts r)) (uniformPermutation N) := by
  have hh := deletedPrefixTVContraction cuts r.val (by omega)
  convert hh using 1 <;> try rfl
  congr 2
  · omega
  · exact restartCuts_heq_suffix cuts r

theorem margin_of_heq {k N n L L' a : ℕ} (c : Cuts k n L) (d : Cuts k n L')
    (hn : 0 < n) (hlen : L = L') (he : HEq c d) {η : ℝ}
    (hm : EmpiricalNegativeMargin N a c hn η) :
    EmpiricalNegativeMargin N a d hn η := by
  subst L'
  cases (eq_of_heq he)
  exact hm

/-- The explicit deletion and rounding budgets leave the required doubled margin. -/
theorem restartMargin {k N K : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    (cuts : Cuts k N (K+1)) (r : Fin (K+1)) {η0 η ρ : ℝ}
    (hη : 0 ≤ η) (hmargin : EmpiricalNegativeMargin N 0 cuts (by omega) η0)
    (hη0 : 4*η ≤ η0) (hbudget : ρ*Real.log (k : ℝ) ≤ η/7)
    (hround : 7*Real.log (k : ℝ)/logScale N ≤ η/2)
    (hr : (r.val : ℝ) ≤ ρ*logScale N+2) :
    EmpiricalNegativeMargin N 0 (restartCuts cuts r) (by omega) (2*η) := by
  have hdel := Margins.deletePrefixMargin_rounding hk hN cuts (r := r.val)
    (by omega) hr hmargin
  have hm : EmpiricalNegativeMargin N r.val (Margins.suffixCuts cuts r.val)
      (by omega) (2*η) := by
    apply Margins.negativeMargin_mono _ _ _ hdel
    nlinarith
  have hzero := rebaseMargin _ (by omega) hm
  exact margin_of_heq _ _ (by omega) (by omega) (restartCuts_heq_suffix cuts r).symm hzero

/-- Lowering both the good-column threshold and its density preserves LocalGood. -/
theorem localGood_mono {k N K : ℕ} (cuts : Cuts k N K) (hN : 2 ≤ N)
    {g g0 γ γ0 ρ a T : ℝ} (hg : g ≤ g0) (hγ : γ ≤ γ0) (hρ : 0 ≤ ρ)
    (h : LocalGood cuts (by omega) g0 γ0 ρ a T) :
    LocalGood cuts (by omega) g γ ρ a T := by
  intro b hab hbT
  have hh := h b hab hbT
  have hcount : ((Finset.univ.filter fun j : Fin K =>
      b ≤ columnTime N j ∧ columnTime N j ≤ b+ρ ∧ GoodColumn (cuts.profile (by omega) j) g0).card : ℝ) ≤
    ((Finset.univ.filter fun j : Fin K =>
      b ≤ columnTime N j ∧ columnTime N j ≤ b+ρ ∧ GoodColumn (cuts.profile (by omega) j) g).card : ℝ) := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    obtain ⟨l,m,hlm,hl,hm⟩ := hj.2.2
    exact ⟨hj.1,hj.2.1,l,m,hlm,hg.trans hl,hg.trans hm⟩
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hγ hρ)
    (logScale_pos hN).le).trans (hh.trans hcount)

/-- Every retained integer window is the corresponding original chronological window. -/
theorem restartWindowGood {k N K : ℕ} (cuts : Cuts k N (K+1)) (hn : 0 < N)
    (r : Fin (K+1)) {ρ γ g : ℝ}
    (h : Exploration.integerWindowGood N cuts hn ρ γ g) :
    Exploration.integerWindowGood N (restartCuts cuts r) hn ρ γ g := by
  intro b hb
  have hh := h (r.val+b) (by omega)
  have hc : (Finset.univ.filter fun j : Fin (K-r.val+1) =>
      b ≤ j.val ∧ j.val < b+Exploration.windowLength N ρ ∧
        GoodColumn ((restartCuts cuts r).profile hn j) g).card =
    (Finset.univ.filter fun j : Fin (K+1) =>
      r.val+b ≤ j.val ∧ j.val < r.val+b+Exploration.windowLength N ρ ∧
        GoodColumn (cuts.profile hn j) g).card := by
    apply Finset.card_bij (fun j _ => restartIndex r j)
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact ⟨by dsimp [restartIndex]; omega, by dsimp [restartIndex]; omega, hj.2.2⟩
    · intro j hj j' hj' hEq
      apply Fin.ext
      have he := congrArg Fin.val hEq
      dsimp [restartIndex] at he
      omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      let j' : Fin (K-r.val+1) := ⟨j.val-r.val, by omega⟩
      have he : restartIndex r j' = j := by apply Fin.ext; dsimp [restartIndex, j']; omega
      refine ⟨j', ?_, he⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [restartCuts_profile, he]
      exact ⟨by dsimp [j']; omega, by dsimp [j']; omega, hj.2.2⟩
  rw [hc]
  exact hh

theorem restartGoodCluster {k N K : ℕ} (cuts : Cuts k N (K+1)) (hn : 0 < N)
    (r j c : Fin (K+1)) {D : ℕ} {g : ℝ} (hrj : r < j) (hjc : j < c)
    (hspan : c.val-r.val ≤ D) (hr : GoodColumn (cuts.profile hn r) g)
    (hj : GoodColumn (cuts.profile hn j) g) (hc : GoodColumn (cuts.profile hn c) g) :
    Exploration.retainedGoodCluster (restartCuts cuts r) hn D g := by
  have hzero : restartIndex r 0 = r := by apply Fin.ext; simp [restartIndex]
  let j' : Fin (K-r.val+1) := ⟨j.val-r.val, by omega⟩
  let c' : Fin (K-r.val+1) := ⟨c.val-r.val, by omega⟩
  have hej : restartIndex r j' = j := by apply Fin.ext; dsimp [restartIndex,j']; omega
  have hec : restartIndex r c' = c := by apply Fin.ext; dsimp [restartIndex,c']; omega
  constructor
  · simpa only [restartCuts_profile,hzero] using hr
  · refine ⟨j',c',by dsimp [j']; omega,by change j'.val < c'.val; dsimp [j',c']; omega,hspan,?_,?_⟩
    · simpa only [restartCuts_profile,hej] using hj
    · simpa only [restartCuts_profile,hec] using hc

theorem restart_threshold {k : ℕ} {η ρ γ : ℝ} (hη : 0 < η)
    (hρ : 0 < ρ) (hγ : 0 < γ) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      4*Real.log (k : ℝ) ≤ logScale N ∧
      7*Real.log (k : ℝ)/logScale N ≤ η/2 ∧
      8 < γ*(ρ*Real.log (N : ℝ)) := by
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N1,hN1⟩ := eventually_atTop.mp
    (ht.eventually_ge_atTop (max (4*Real.log (k : ℝ)) (14*Real.log (k : ℝ)/η)))
  obtain ⟨N2,hN2,hcluster⟩ := Exploration.cluster_threshold_eventually hρ hγ
  refine ⟨max N1 N2, hN2.trans (le_max_right _ _), ?_⟩
  intro N hN
  have hN' : 2 ≤ N := hN2.trans ((le_max_right _ _).trans hN)
  have hh := hN1 N ((le_max_left _ _).trans hN)
  refine ⟨(le_max_left _ _).trans hh, ?_, hcluster N ((le_max_right _ _).trans hN)⟩
  have hdiv := (le_max_right _ _).trans hh
  have hmul := (div_le_iff₀ hη).mp hdiv
  apply (div_le_iff₀ (logScale_pos hN')).mpr
  dsimp [logScale]
  nlinarith

/-- Uniform concrete restart: all C-side deterministic hypotheses, the maximum
word bound, and physical deletion contraction follow from the endpoint inputs. -/
theorem restartHypotheses (k : ℕ) (hk : 2 ≤ k) (T η0 η g γ ρ : ℝ)
    (hη : 0 < η) (hη0 : 4*η ≤ η0) (hρ : 0 < ρ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hbudgetη : ρ*Real.log (k : ℝ) ≤ η/7)
    (hbudget1 : ρ*Real.log (k : ℝ) ≤ 1/4) :
    ∃ N0 : ℕ, ∃ hN0 : 2 ≤ N0, ∀ (N : ℕ) (hN : N0 ≤ N) (K : ℕ),
      ((K+1 : ℕ) : ℝ) ≤ T*Real.log (N : ℝ) → ∀ cuts : Cuts k N (K+1),
      EmpiricalNegativeMargin N 0 cuts (by omega) η0 →
      LocalGood cuts (by omega) g γ ρ 0 (((K+1 : ℕ) : ℝ)/Real.log (N : ℝ)) →
      ∃ r : Fin (K+1),
        ((K-r.val+1 : ℕ) : ℝ) ≤ T*Real.log (N : ℝ) ∧
        EmpiricalNegativeMargin N 0 (restartCuts cuts r) (by omega) (2*η) ∧
        Exploration.integerWindowGood N (restartCuts cuts r) (by omega) ρ γ g ∧
        Exploration.retainedGoodCluster (restartCuts cuts r) (by omega)
          (Exploration.clusterSpan γ) g ∧
        maximalMean (restartCuts cuts r) (by omega) ≤ (N : ℝ)^(-(2*η)) ∧
        tv (physicalInverseLaw cuts) (uniformPermutation N) ≤
          tv (physicalInverseLaw (restartCuts cuts r)) (uniformPermutation N) := by
  obtain ⟨N0,hN0,hthreshold⟩ := restart_threshold (k := k) hη hρ hγ
  refine ⟨N0,hN0,?_⟩
  intro N hN K hK cuts hmargin hlocal
  have hN' : 2 ≤ N := hN0.trans hN
  obtain ⟨hlarge,hround,hcluster⟩ := hthreshold N hN
  have hwindow := initialWindow_fits hk hN' cuts (by linarith) hρ.le hbudget1 hlarge hmargin
  have hgood := Exploration.localGood_integerWindow cuts hN' ρ γ g hlocal
  obtain ⟨r,j,c,hr,hc,hrj,hjc,hspan,hgr,hgj,hgc⟩ :=
    Exploration.integerWindow_cluster cuts (by omega) hρ.le hγ hγ1 (by omega)
      hcluster hgood 0 (by simpa using hwindow)
  have hrlen : (r.val : ℝ) ≤ ρ*logScale N+2 := by
    have hrv : r.val < Exploration.windowLength N ρ := by omega
    have hrc : (r.val : ℝ) < Exploration.windowLength N ρ := by exact_mod_cast hrv
    have hceil := Nat.ceil_lt_add_one (mul_nonneg hρ.le (logScale_pos hN').le)
    change (r.val : ℝ) ≤ ρ*Real.log (N : ℝ)+2
    dsimp [Exploration.windowLength] at hrc
    push_cast at hrc
    dsimp [logScale] at hceil
    linarith
  have hm := restartMargin hk hN' cuts r hη.le hmargin hη0 hbudgetη hround hrlen
  refine ⟨r,?_,hm,restartWindowGood cuts (by omega) r hgood,
    restartGoodCluster cuts (by omega) r j c hrj hjc hspan hgr hgj hgc,?_,
    restartTVContraction cuts r⟩
  · have hlen : ((K-r.val+1 : ℕ) : ℝ) ≤ ((K+1 : ℕ) : ℝ) := by
      exact_mod_cast (show K-r.val+1 ≤ K+1 by omega)
    exact hlen.trans hK
  · exact Margins.maximalMean_le_of_terminalMargin hN' 0 _ (by omega) hm.1

end RiffleUpperV2.EmpiricalUpper
