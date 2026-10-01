import RiffleLowerV2.Witness.Selection
import RiffleLowerV2.Witness.Rounding
import RiffleLowerV2.Witness.Empirical
import RiffleLowerV2.Witness.OneColumn

noncomputable section
open Set
namespace RiffleLowerV2.Witness
open TimeProfile

/-- The finite witness is constructed from a shortened continuous empirical
witness, using only the actual column functions. -/
theorem roundWitness {k N K : ℕ} (hk : 2 ≤ k) (hN2 : 2 ≤ N)
    (cuts : Cuts k N K) (hN : 0 < N)
    {eta rho chi density T s0 u0 theta : ℝ}
    (heta : 0 < eta) (hrho : 0 < rho)
    (hmesh : 2*rho*Real.log k ≤ kappa eta/100)
    (herror : Real.log k/logScale N ≤ kappa eta/1000)
    (hHorizon : horizon N K ≤ T)
    (hcount : 3 < density*rho*logScale N)
    (hgood : LocalGood cuts hN chi density rho 0 T)
    (hbeta : beta cuts hN (horizon N K) < kappa0 eta)
    (htri : (s0,u0) ∈ triangle (horizon N K))
    (htheta : theta ∈ Icc (3 : ℝ) 4)
    (hb0 : eta/4 ≤ beta cuts hN s0)
    (hj0 : J cuts hN theta s0 u0 ≤ beta cuts hN s0/2-4*kappa eta)
    (hlower : theta=3 ∨ J cuts hN theta s0 u0 = beta cuts hN s0/2-4*kappa eta)
    (hf0 : 7*eta/8-16*kappa eta ≤ F cuts hN theta s0 u0) :
    ∃ W : ColdWitnessData, WitnessSpec cuts hN eta rho chi W := by
  have hL := logScale_pos hN2
  have hell : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hkappa : 0 < kappa eta := by unfold kappa; positivity
  have ht24 : theta ∈ Icc (2 : ℝ) 4 := ⟨by linarith [htheta.1], htheta.2⟩
  have ht1 : 1 ≤ theta := by linarith [htheta.1]
  have ht2 : (2 : ℝ) ∈ Icc (2 : ℝ) 4 := by norm_num
  have hS0 : 0 ≤ horizon N K := by unfold horizon; positivity
  have hs00 : 0 ≤ s0 := htri.1
  have hs0u0 : s0 ≤ u0 := htri.2.1
  have hu0S : u0 ≤ horizon N K := htri.2.2
  have hs0S : s0 ≤ horizon N K := hs0u0.trans hu0S
  have hs0mem : s0 ∈ Icc (0 : ℝ) (horizon N K) := ⟨hs00, hs0S⟩
  have hu0mem : u0 ∈ Icc (0 : ℝ) (horizon N K) := ⟨hs00.trans hs0u0, hu0S⟩
  have hzeroMem : (0 : ℝ) ∈ Icc (0 : ℝ) (horizon N K) := ⟨le_rfl,hS0⟩
  have hSMem : horizon N K ∈ Icc (0 : ℝ) (horizon N K) := ⟨hS0,le_rfl⟩
  have haBounds (j : Fin K) : |maxCost (cuts.profile hN j)| ≤ Real.log k := by
    rw [abs_of_nonneg (maxCost_bounds hk _).1]
    exact (maxCost_bounds hk _).2
  have hjBounds (j : Fin K) : |tiltedCost (cuts.profile hN j) theta| ≤ Real.log k := by
    rw [abs_of_nonneg (tiltedCost_bounds hk _ ht24).1]
    exact (tiltedCost_bounds hk _ ht24).2
  have hbpBounds (j : Fin K) : |psi (cuts.profile hN j) theta| ≤ 3*Real.log k := by
    rw [abs_of_nonneg (psi_sharp_bounds hk _ ht24).1]
    exact (psi_sharp_bounds hk _ ht24).2.trans
      (mul_le_mul_of_nonneg_right (by linarith [htheta.2]) hell.le)
  have hbtBounds (j : Fin K) : |psi (cuts.profile hN j) 2| ≤ Real.log k := by
    rw [abs_of_nonneg (psi_sharp_bounds hk _ ht2).1]
    convert (psi_sharp_bounds hk (cuts.profile hN j) ht2).2 using 1
    norm_num
  have hAdiff : beta cuts hN s0 - beta cuts hN (horizon N K) =
      A cuts hN s0 (horizon N K) := by
    have hadd := empiricalIntegral_add N (fun j => maxCost (cuts.profile hN j))
      0 s0 (horizon N K)
    change A cuts hN 0 (horizon N K) = A cuts hN 0 s0 + A cuts hN s0 (horizon N K) at hadd
    unfold beta
    linarith
  have hdiff : beta cuts hN s0-beta cuts hN (horizon N K) ≤
      (horizon N K-s0)*Real.log k := by
    rw [hAdiff]
    exact empiricalIntegral_le hN2 (fun j => (maxCost_bounds hk (cuts.profile hN j)).2)
      hs00 hs0S le_rfl
  have hclear := terminal_clearance heta hell hL hb0 hbeta hdiff hmesh herror
  let bN := ⌈2*rho*logScale N⌉₊
  let ms := ⌊s0*logScale N⌋₊
  let mu := min ⌊u0*logScale N⌋₊ (K-bN)
  let s := gridTime N ms
  let u := gridTime N mu
  have hround := rounded_indices hL hrho hs00 hs0u0 hu0S hclear
  change ms ≤ mu ∧ mu+bN ≤ K ∧ 0 ≤ s0-s ∧ s0-s < 1/logScale N ∧
    0 ≤ u0-u ∧ u0-u ≤ 2*rho+2/logScale N at hround
  obtain ⟨horder,hbridge,hsd0,hsd1,hud0,hud1⟩ := hround
  have hmuK : mu ≤ K := by omega
  have hmsK : ms ≤ K := horder.trans hmuK
  have hs0 : 0 ≤ s := by dsimp [s,gridTime]; positivity
  have hu0 : 0 ≤ u := by dsimp [u,gridTime]; positivity
  have hsu : s ≤ u := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast horder) hL.le
  have huS : u ≤ horizon N K := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hmuK) hL.le
  have hsMem : s ∈ Icc (0 : ℝ) (horizon N K) := ⟨hs0,hsu.trans huS⟩
  have huMem : u ∈ Icc (0 : ℝ) (horizon N K) := ⟨hu0,huS⟩
  have hsd : |s-s0| ≤ 1/logScale N := by
    rw [abs_sub_comm,abs_of_nonneg hsd0]
    exact hsd1.le
  have hud : |u-u0| ≤ 2*rho+2/logScale N := by
    rw [abs_sub_comm,abs_of_nonneg hud0]
    exact hud1
  let r := 2*rho*Real.log k
  let e := Real.log k/logScale N
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hbErr : |beta cuts hN s-beta cuts hN s0| ≤ e := by
    have hept := empiricalIntegral_endpoint_bound hN2 haBounds hzeroMem hsMem hzeroMem hs0mem
    have hid : beta cuts hN s-beta cuts hN s0 = -(A cuts hN 0 s-A cuts hN 0 s0) := by
      unfold beta; ring
    rw [hid,abs_neg]
    change |A cuts hN 0 s-A cuts hN 0 s0| ≤ _ at hept
    simp only [sub_self,abs_zero,zero_add] at hept
    apply hept.trans
    convert mul_le_mul_of_nonneg_right hsd hell.le using 1
    dsimp [e]
    ring
  have hjErr : |J cuts hN theta s u-J cuts hN theta s0 u0| ≤ r+3*e := by
    have hept := empiricalIntegral_endpoint_bound hN2 hjBounds hsMem huMem hs0mem hu0mem
    apply hept.trans
    have hm := mul_le_mul_of_nonneg_right (add_le_add hsd hud) hell.le
    convert hm using 1
    dsimp [r,e]
    ring
  have hbpErr : |B cuts hN theta s u-B cuts hN theta s0 u0| ≤ 3*(r+3*e) := by
    have hept := empiricalIntegral_endpoint_bound hN2 hbpBounds hsMem huMem hs0mem hu0mem
    apply hept.trans
    have hm := mul_le_mul_of_nonneg_right (add_le_add hsd hud) (by positivity : 0 ≤ 3*Real.log k)
    convert hm using 1
    dsimp [r,e]
    ring
  have hbtErr : |B cuts hN 2 u (horizon N K)-B cuts hN 2 u0 (horizon N K)| ≤ r+2*e := by
    have hept := empiricalIntegral_endpoint_bound hN2 hbtBounds huMem hSMem hu0mem hSMem
    simp only [sub_self,abs_zero,add_zero] at hept
    apply hept.trans
    have hm := mul_le_mul_of_nonneg_right hud hell.le
    convert hm using 1
    dsimp [r,e]
    ring
  obtain ⟨hjErr',hfErr'⟩ := endpoint_error_algebra htheta hr he hbErr hjErr hbpErr hbtErr
  have hjSmall : |(J cuts hN theta s u-beta cuts hN s/2)-
      (J cuts hN theta s0 u0-beta cuts hN s0/2)| ≤ kappa eta/10 := by
    apply hjErr'.trans
    change r ≤ kappa eta/100 at hmesh
    change e ≤ kappa eta/1000 at herror
    linarith
  have hfSmall : |F cuts hN theta s u-F cuts hN theta s0 u0| ≤ kappa eta/10 := by
    apply hfErr'.trans
    change r ≤ kappa eta/100 at hmesh
    change e ≤ kappa eta/1000 at herror
    linarith
  obtain ⟨hf,hj,hl⟩ := rounding_margins heta hj0 hlower hf0 hjSmall hfSmall
  have hjNonneg : 0 ≤ J cuts hN theta s u :=
    empiricalIntegral_nonneg hN2 (fun j => (tiltedCost_bounds hk (cuts.profile hN j) ht24).1) hsu
  have hhNonneg : 0 ≤ H cuts hN theta s u :=
    empiricalIntegral_nonneg hN2 (fun j => (tiltedEntropy_bounds hk (cuts.profile hN j) ht24).1) hsu
  have hhj : H cuts hN theta s u ≤ J cuts hN theta s u :=
    empiricalIntegral_mono hN2 (fun j => (tiltedEntropy_bounds hk (cuts.profile hN j) ht24).2) hsu
  have hidentity (a : ℝ) (ha : 1 ≤ a) (x y : ℝ) :
      H cuts hN a x y = a*J cuts hN a x y-B cuts hN a x y := by
    change empiricalIntegral N (fun j => tiltedEntropy (cuts.profile hN j) a) x y = _
    simp_rw [tiltedEntropy_identity _ ha]
    exact empiricalIntegral_linear _ _ a x y
  obtain ⟨hh,hH,hGamma⟩ := final_margins heta htheta hjNonneg hhNonneg hhj hj hl hf
    (hidentity theta ht1 s u) (hidentity 2 (by norm_num) u (horizon N K))
  have hmean : beta cuts hN s-J cuts hN theta s u-J cuts hN 2 u (horizon N K) ≤
      beta cuts hN (horizon N K) := by
    have hp := empiricalIntegral_mono hN2
      (fun j => maxCost_le_tiltedCost (cuts.profile hN j) ht1) hsu
    have ht := empiricalIntegral_mono hN2
      (fun j => maxCost_le_tiltedCost (cuts.profile hN j) (alpha := 2) (by norm_num)) huS
    have hsum := empiricalIntegral_add N (fun j => maxCost (cuts.profile hN j)) s u (horizon N K)
    have hprefix := empiricalIntegral_add N (fun j => maxCost (cuts.profile hN j)) 0 s (horizon N K)
    change A cuts hN s u ≤ J cuts hN theta s u at hp
    change A cuts hN u (horizon N K) ≤ J cuts hN 2 u (horizon N K) at ht
    change A cuts hN s (horizon N K) = A cuts hN s u+A cuts hN u (horizon N K) at hsum
    change A cuts hN 0 (horizon N K) = A cuts hN 0 s+A cuts hN s (horizon N K) at hprefix
    unfold beta
    linarith
  have hbridgeGood := good_bridge_columns cuts hN hL hrho hbridge hHorizon hcount hgood
  let W : ColdWitnessData := ⟨ms,mu,bN,theta⟩
  refine ⟨W, ?_⟩
  change W.bridgeLength = ⌈2*rho*logScale N⌉₊ ∧ _
  exact ⟨rfl,horder,hbridge,htheta,hbridgeGood,hf,hj,hl,hh,hH,hGamma,hmean,hbeta⟩

end RiffleLowerV2.Witness
