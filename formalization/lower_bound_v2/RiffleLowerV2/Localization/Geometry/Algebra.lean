import Contracts.v1.WitnessGeometry

noncomputable section
namespace RiffleLowerV2.Localization

def geometryError (eta : ℝ) : ℝ := min (kappa eta) (kappa0 eta) / 1000

theorem geometryError_pos {eta : ℝ} (heta : 0 < eta) : 0 < geometryError eta := by
  unfold geometryError kappa0 kappa
  positivity

theorem geometryError_le_kappa (eta : ℝ) :
    geometryError eta ≤ kappa eta / 1000 := by
  exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)

theorem geometryError_le_kappa0 (eta : ℝ) :
    geometryError eta ≤ kappa0 eta / 1000 := by
  exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)

/-- The entropy buffer comes from H≤J, retaining six units before rounding. -/
theorem prefix_exponent_buffers {b jp hp jstar hstar kap err : ℝ}
    (hkap : 0 < kap) (herr : err ≤ kap / 1000)
    (hhj : hp ≤ jp) (hj : jp ≤ b/2-3*kap) (hh : kap ≤ b-jp+hp)
    (happrox : |jstar-jp| + |hstar-hp| ≤ err) :
    b/2+2*kap ≤ b-jstar ∧ hstar ≤ (b-jstar)-kap ∧
      kap/2 ≤ b-jstar+hstar := by
  have hja : |jstar-jp| ≤ err := le_trans (le_add_of_nonneg_right (abs_nonneg _)) happrox
  have hha : |hstar-hp| ≤ err := le_trans (le_add_of_nonneg_left (abs_nonneg _)) happrox
  rcases abs_le.mp hja with ⟨hjlo, hjhi⟩
  rcases abs_le.mp hha with ⟨hhlo, hhhi⟩
  constructor
  · linarith
  constructor <;> linarith

/-- All type perturbations and the deleted bridge are retained explicitly. -/
theorem collision_exponent_buffers
    {b jp hp jt ht jps hps jts hts ellb dj dh kap kap0 err : ℝ}
    (_hkap : 0 < kap) (hkap0 : 0 < kap0) (hkap0le : kap0 ≤ kap/100)
    (herr : err ≤ kap0/1000)
    (hpapprox : |jps-jp| + |hps-hp| ≤ err)
    (htapprox : |jts-(jt-dj)| + |hts-(ht-dh)| ≤ err)
    (hdj0 : 0 ≤ dj) (hdj : dj ≤ kap0/50) (hdh : dh ≤ kap0/50)
    (hell0 : 0 ≤ ellb) (hell : ellb ≤ kap0/50)
    (hgap : kap ≤ (2*b-2*jp-2*jt+hp+ht)-(b-jp+hp)/2)
    (hz : b-jp-jt < kap0) :
    kap/2 ≤ (2*(b-jps-jts-ellb)+hps+hts)-(b-jps+hps)/2 ∧
      b-jps-jts-ellb ≤ 2*kap0 := by
  have hpj : |jps-jp| ≤ err := le_trans (le_add_of_nonneg_right (abs_nonneg _)) hpapprox
  have hph : |hps-hp| ≤ err := le_trans (le_add_of_nonneg_left (abs_nonneg _)) hpapprox
  have htj : |jts-(jt-dj)| ≤ err := le_trans (le_add_of_nonneg_right (abs_nonneg _)) htapprox
  have hth : |hts-(ht-dh)| ≤ err := le_trans (le_add_of_nonneg_left (abs_nonneg _)) htapprox
  rcases abs_le.mp hpj with ⟨hpjl, hpju⟩
  rcases abs_le.mp hph with ⟨hphl, hphu⟩
  rcases abs_le.mp htj with ⟨htjl, htju⟩
  rcases abs_le.mp hth with ⟨hthl, hthu⟩
  constructor <;> linarith

theorem ambient_exponent_lower {b jp kap : ℝ}
    (hjp : 0 ≤ jp) (hell : b/2+2*kap ≤ b-jp) : 4*kap ≤ b := by
  linarith

end RiffleLowerV2.Localization
