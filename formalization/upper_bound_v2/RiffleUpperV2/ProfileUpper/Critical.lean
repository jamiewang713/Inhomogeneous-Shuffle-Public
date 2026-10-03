import RiffleUpperV2.ProfileUpper.Analytic
import RiffleUpperV2.ProfileUpper.Random

noncomputable section
open Set Filter
open scoped ENNReal
namespace RiffleUpperV2.ProfileUpper
open TimeProfile

theorem earlierNegative {k : ℕ} {μ : TimeLaw k} {t : ℝ}
    (ht : criticalTime μ < ENNReal.ofReal t) :
    ∃ s : ℝ, 0 < s ∧ s < t ∧ reducedMargin μ s < 0 := by
  obtain ⟨x, ⟨s, hs, rfl⟩, hst⟩ := sInf_lt_iff.mp ht
  exact ⟨s, hs.1, (ENNReal.ofReal_lt_ofReal_iff'.mp hst).1, hs.2⟩

theorem fine_scalarIntegrable {k : ℕ} {μ : TimeLaw k}
    {cuts : ∀ N : ℕ, InfiniteCuts k N} (hFine : ArbitrarilyFineApproximation μ cuts)
    {t : ℝ} (ht : 0 < t) : ∃ P : BorelPartition k, ScalarIntegrable μ P t := by
  obtain ⟨χ, _, _, P, _, hI, _⟩ := hFine t ht 1 (by norm_num)
  exact ⟨P, hI⟩

theorem criticalTimeUpperOfBuffered (hP : Contracts.V1.P) {k : ℕ} (hk : 2 ≤ k)
    (μ : TimeLaw k) (cuts : ∀ N : ℕ, InfiniteCuts k N)
    (hFine : ArbitrarilyFineApproximation μ cuts) (t : ℝ) (_ht : 0 ≤ t)
    (hcrit : criticalTime μ < ENNReal.ofReal t) :
    Tendsto (fun N => tv (physicalInverseLaw ((cuts N).take (horizonDepth N t)))
      (uniformPermutation N)) atTop (nhds 0) := by
  obtain ⟨s, hs, hst, hneg⟩ := earlierNegative hcrit
  have ht : 0 < t := hs.trans hst
  obtain ⟨P', hI'⟩ := fine_scalarIntegrable hFine ht
  have htneg : reducedMargin μ t < 0 :=
    (marginMonotonicity hk hs.le hst.le hI').trans_lt hneg
  let η := -reducedMargin μ t
  have hη : 0 < η := neg_pos.mpr htneg
  obtain ⟨χ0, hχ0, hχ⟩ := hP k hk t η ht hη
  obtain ⟨χ, hχpos, hχsmall, P, hPreg, hI, g, γ, ρbar, hg, hgk, hγ, hρbar, hApprox⟩ :=
    hFine t ht χ0 hχ0
  obtain ⟨ρ0, hρ0, hρ⟩ := hχ χ hχpos hχsmall P hPreg g γ hg hgk hγ
  let ρ := min ρbar ρ0
  have hρpos : 0 < ρ := lt_min hρbar hρ0
  obtain ⟨φ0, hφ0, hφ⟩ := hρ ρ hρpos (min_le_right _ _)
  obtain ⟨NA, hNA, hA⟩ := hApprox ρ hρpos (min_le_left _ _) φ0 hφ0
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun N => ha.trans_le (tv_nonnegative _ _)
  · intro ε hε
    obtain ⟨NP, hNP, hEst⟩ := hφ φ0 hφ0 le_rfl μ hI (by dsimp [η]; linarith)
      (ε/2) (by positivity)
    filter_upwards [eventually_ge_atTop (max NA NP)] with N hN
    obtain ⟨hl, hg⟩ := hA N (by omega)
    have hb := hEst N (by omega) ((cuts N).take (horizonDepth N t)) hl hg
    linarith

theorem mixingTime_le_of_tv {k N m : ℕ} (cuts : InfiniteCuts k N) {ε : ℝ}
    (h : tv (physicalInverseLaw (cuts.take m)) (uniformPermutation N) ≤ ε) :
    mixingTime cuts ε ≤ (m : ℝ≥0∞) :=
  sInf_le ⟨m, h, rfl⟩

theorem eventually_mixingRatio_le {k : ℕ} {cuts : ∀ N : ℕ, InfiniteCuts k N}
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t)
    (hconv : Tendsto (fun N => tv (physicalInverseLaw ((cuts N).take (horizonDepth N t)))
      (uniformPermutation N)) atTop (nhds 0)) :
    ∀ᶠ N in atTop, mixingTime (cuts N) ε / ENNReal.ofReal (Real.log (N : ℝ)) ≤
      ENNReal.ofReal t := by
  filter_upwards [eventually_ge_atTop 2, hconv.eventually (eventually_lt_nhds hε)] with N hN hmix
  have hlog := logScale_pos hN
  have hf := Nat.floor_le (mul_nonneg ht hlog.le)
  have hd : (horizonDepth N t : ℝ) / Real.log (N : ℝ) ≤ t :=
    (div_le_iff₀ hlog).mpr hf
  calc
    _ ≤ (horizonDepth N t : ℝ≥0∞) / ENNReal.ofReal (Real.log (N : ℝ)) :=
      ENNReal.div_le_div_right (mixingTime_le_of_tv (cuts N) hmix.le) _
    _ = ENNReal.ofReal ((horizonDepth N t : ℝ) / Real.log (N : ℝ)) := by
      have hlog' : 0 < Real.log (N : ℝ) := hlog
      rw [ENNReal.ofReal_div_of_pos hlog', ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal t := ENNReal.ofReal_le_ofReal hd

theorem mixingTimeUpperOfConvergence {k : ℕ} (μ : TimeLaw k)
    (cuts : ∀ N : ℕ, InfiniteCuts k N)
    (hconv : ∀ t : ℝ, 0 ≤ t → criticalTime μ < ENNReal.ofReal t →
      Tendsto (fun N => tv (physicalInverseLaw ((cuts N).take (horizonDepth N t)))
        (uniformPermutation N)) atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    limsup (fun N => mixingTime (cuts N) ε / ENNReal.ofReal (Real.log (N : ℝ))) atTop
      ≤ criticalTime μ := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  obtain ⟨c, hcb, hbc⟩ := exists_between hb
  have hcfin : c ≠ ⊤ := ne_top_of_lt hbc
  have hcreal : ENNReal.ofReal c.toReal = c := ENNReal.ofReal_toReal hcfin
  have he := eventually_mixingRatio_le hε ENNReal.toReal_nonneg
    (hconv c.toReal ENNReal.toReal_nonneg (by simpa only [hcreal] using hcb))
  have hlim := Filter.limsup_le_of_le (h := he)
  rw [hcreal] at hlim
  exact hlim.trans hbc.le

theorem criticalOfBuffered (hP : Contracts.V1.P) : Contracts.V1.T := by
  intro k hk μ cuts hFine
  have hc := criticalTimeUpperOfBuffered hP hk μ cuts hFine
  exact ⟨hc, fun ε hε _ => mixingTimeUpperOfConvergence μ cuts hc ε hε⟩

end RiffleUpperV2.ProfileUpper
