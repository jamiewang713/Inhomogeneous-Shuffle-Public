import Contracts.v1.WitnessGeometry

noncomputable section
open scoped BigOperators
open Set
namespace RiffleLowerV2.Witness
open TimeProfile

/-- The only asymptotic ingredient used in rounding; its proof is a local port of
`TimeProfile.exists_logScale_threshold`, AnalyticParameters.lean, lines 33--47.
The exponential threshold is fixed before N and any cuts. -/
theorem exists_logScale_threshold (B epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → B / logScale N ≤ epsilon / 16 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp (16 * B / epsilon))
  refine ⟨max 2 n, le_max_left _ _, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hnN : n ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hexp : Real.exp (16 * B / epsilon) ≤ (N : ℝ) :=
    hn.le.trans (by exact_mod_cast hnN)
  have hlog : 16 * B / epsilon ≤ logScale N :=
    (Real.le_log_iff_exp_le hNpos).mpr hexp
  have hmul := (div_le_iff₀ hepsilon).mp hlog
  apply (div_le_iff₀ (logScale_pos hN2)).mpr
  nlinarith

theorem exists_logScale_gt (B : ℝ) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → B < logScale N := by
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp B)
  refine ⟨max 2 n, le_max_left _ _, ?_⟩
  intro N hN
  have hnN : n ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  exact (Real.lt_log_iff_exp_lt hNpos).mpr (hn.trans_le (by exact_mod_cast hnN))

theorem floor_grid_error {L s : ℝ} (hL : 0 < L) (hs : 0 ≤ s) :
    0 ≤ s - (⌊s * L⌋₊ : ℝ) / L ∧ s - (⌊s * L⌋₊ : ℝ) / L < 1 / L := by
  constructor
  · exact sub_nonneg.mpr ((div_le_iff₀ hL).mpr (Nat.floor_le (mul_nonneg hs hL.le)))
  · have hfloor := Nat.lt_floor_add_one (s * L)
    apply (mul_lt_mul_iff_left₀ hL).mp
    simpa only [sub_mul, div_mul_cancel₀ _ hL.ne'] using
      (show s * L - (⌊s * L⌋₊ : ℝ) < 1 by linarith)

/-- Source rounding, with terminal clipping. No endpoint is required to lie in a
positive-cost column. The strict terminal clearance is the sole geometric input. -/
theorem rounded_indices {K : ℕ} {L rho s u : ℝ}
    (hL : 0 < L) (hrho : 0 < rho) (hs : 0 ≤ s) (hsu : s ≤ u)
    (hu : u ≤ (K : ℝ) / L) (hclear : s + 2*rho + 2/L < (K : ℝ)/L) :
    let b := ⌈2*rho*L⌉₊
    let ms := ⌊s*L⌋₊
    let mu := min ⌊u*L⌋₊ (K-b)
    ms ≤ mu ∧ mu+b ≤ K ∧
    0 ≤ s - (ms : ℝ)/L ∧ s - (ms : ℝ)/L < 1/L ∧
    0 ≤ u - (mu : ℝ)/L ∧ u - (mu : ℝ)/L ≤ 2*rho+2/L := by
  dsimp only
  let b := ⌈2*rho*L⌉₊
  let ms := ⌊s*L⌋₊
  let mu := min ⌊u*L⌋₊ (K-b)
  have hfloor : (ms : ℝ) ≤ s*L := Nat.floor_le (mul_nonneg hs hL.le)
  have hceil : (b : ℝ) < 2*rho*L+1 := Nat.ceil_lt_add_one (by positivity)
  have hclear' := (mul_lt_mul_iff_left₀ hL).mpr hclear
  simp only [add_mul, div_mul_cancel₀ _ hL.ne'] at hclear'
  have hsum : ms+b ≤ K := by
    have : (ms : ℝ)+(b : ℝ) ≤ K := by nlinarith
    exact_mod_cast this
  have hb : b ≤ K := by omega
  have hmsClip : ms ≤ K-b := by omega
  have hmsFloor : ms ≤ ⌊u*L⌋₊ := Nat.floor_mono (mul_le_mul_of_nonneg_right hsu hL.le)
  have horder : ms ≤ mu := le_min hmsFloor hmsClip
  have hbridge : mu+b ≤ K := by
    have : mu ≤ K-b := min_le_right _ _
    omega
  have hsError := floor_grid_error hL hs
  have hu0 : 0 ≤ u := hs.trans hsu
  have huError := floor_grid_error hL hu0
  have hmuFloor : (mu : ℝ) ≤ (⌊u*L⌋₊ : ℝ) := by
    exact_mod_cast (min_le_left ⌊u*L⌋₊ (K-b))
  have hmuU : (mu : ℝ)/L ≤ u :=
    (div_le_div_of_nonneg_right hmuFloor hL.le).trans (by linarith [huError.1])
  refine ⟨horder, hbridge, hsError.1, hsError.2, sub_nonneg.mpr hmuU, ?_⟩
  change u - (mu : ℝ)/L ≤ 2*rho+2/L
  by_cases hcase : ⌊u*L⌋₊ ≤ K-b
  · have hmu : mu = ⌊u*L⌋₊ := min_eq_left hcase
    rw [hmu]
    have : 0 < 1/L := by positivity
    have htwo : 2/L = 2*(1/L) := by ring
    linarith [huError.2]
  · have hmu : mu = K-b := min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hcase))
    have hcast : (mu : ℝ) = (K : ℝ)-(b : ℝ) := by rw [hmu, Nat.cast_sub hb]
    have hu' := (le_div_iff₀ hL).mp hu
    apply (mul_le_mul_iff_left₀ hL).mp
    simp only [sub_mul, add_mul, div_mul_cancel₀ _ hL.ne']
    nlinarith

/-- The beta gap excludes a witness born too close to the terminal endpoint. -/
theorem rounding_terminal_clearance {S s rho eta ell L b betaS Aend : ℝ}
    (heta : 0 < eta) (hell : 0 < ell) (_hL : 0 < L)
    (hb : eta/4 ≤ b) (hbeta : betaS < kappa0 eta)
    (hAeq : Aend = b-betaS) (hAbound : Aend ≤ (S-s)*ell)
    (hmesh : 2*rho*ell ≤ kappa eta/100)
    (hround : ell/L ≤ kappa eta/400) :
    s+2*rho+2/L < S := by
  have hk : 0 < kappa eta := by unfold kappa; positivity
  have hetaK : eta = 1000*kappa eta := by unfold kappa; ring
  have hk0 : kappa0 eta ≤ kappa eta/100 := min_le_left _ _
  have hfrac : (2/L)*ell = 2*(ell/L) := by ring
  apply (mul_lt_mul_iff_right₀ hell).mp
  nlinarith [hfrac]

/-- Every column in an interior interval belongs to the bridge. Using an
interior interval avoids the possible single-column loss at a closed left endpoint. -/
theorem good_bridge_columns {k N K mu : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    {rho chi density T : ℝ} (hL : 0 < logScale N) (hrho : 0 < rho)
    (hbridge : mu + ⌈2*rho*logScale N⌉₊ ≤ K)
    (hHorizon : horizon N K ≤ T)
    (hcount : 3 < density*rho*logScale N)
    (hgood : LocalGood cuts hN chi density rho 0 T) :
    ∃ gL gR : Fin K, mu ≤ gL.val ∧ gL.val < gR.val ∧
      gR.val < mu + ⌈2*rho*logScale N⌉₊ ∧
      GoodColumn (cuts.profile hN gL) chi ∧ GoodColumn (cuts.profile hN gR) chi := by
  classical
  let L := logScale N
  let b := ⌈2*rho*L⌉₊
  let a := (mu : ℝ)/L + rho/2
  have hL' : 0 < L := hL
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 2*rho*L ≤ (b : ℝ) := Nat.le_ceil _
  have hcastBridge : (mu : ℝ)+(b : ℝ) ≤ K := by exact_mod_cast hbridge
  have haT : a+rho ≤ T := by
    apply le_trans _ hHorizon
    change a+rho ≤ (K : ℝ)/L
    dsimp [a]
    apply (le_div_iff₀ hL').mpr
    have hcancel : (mu : ℝ)/L*L = mu := div_mul_cancel₀ _ hL'.ne'
    nlinarith
  let G : Finset (Fin K) := Finset.univ.filter fun j =>
    a ≤ columnTime N j ∧ columnTime N j ≤ a+rho ∧ GoodColumn (cuts.profile hN j) chi
  have hG : 1 < G.card := by
    have hlocal := hgood a ha haT
    change density*rho*L ≤ (G.card : ℝ) at hlocal
    have : (1 : ℝ) < G.card := by linarith
    exact_mod_cast this
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hG
  have hmem (j : Fin K) (hj : j ∈ G) :
      mu ≤ j.val ∧ j.val < mu+b ∧ GoodColumn (cuts.profile hN j) chi := by
    have hdata := (Finset.mem_filter.mp hj).2
    have hleft : (mu : ℝ) < (j.val : ℝ)+1 := by
      have htemp := (le_div_iff₀ hL').mp hdata.1
      change a*L ≤ (j.val : ℝ)+1 at htemp
      dsimp [a] at htemp
      have hcancel : (mu : ℝ)/L*L = mu := div_mul_cancel₀ _ hL'.ne'
      nlinarith
    have hright : (j.val : ℝ)+1 ≤ (mu : ℝ)+(b : ℝ) := by
      have htemp := (div_le_iff₀ hL').mp hdata.2.1
      change (j.val : ℝ)+1 ≤ (a+rho)*L at htemp
      dsimp [a] at htemp
      have hcancel : (mu : ℝ)/L*L = mu := div_mul_cancel₀ _ hL'.ne'
      nlinarith
    have hl : mu < j.val+1 := by exact_mod_cast hleft
    have hr : j.val+1 ≤ mu+b := by exact_mod_cast hright
    exact ⟨by omega, by omega, hdata.2.2⟩
  have hx' := hmem x hx
  have hy' := hmem y hy
  have hne : x.val ≠ y.val := fun heq => hxy (Fin.ext heq)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨x,y,hx'.1,hlt,hy'.2.1,hx'.2.2,hy'.2.2⟩
  · exact ⟨y,x,hy'.1,hgt,hx'.2.1,hy'.2.2,hx'.2.2⟩

end RiffleLowerV2.Witness
