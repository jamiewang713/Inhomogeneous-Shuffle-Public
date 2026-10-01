import RiffleLowerV2.Shared.Empirical
import RiffleLowerV2.Shared.Path

/-!
LB-00 reviewer proposal only. No target below is asserted or proved. These
proposition-valued definitions are an exact interface proposal for LB-07,
LB-10, and LB-11; the coordinator alone may incorporate a reviewed version
into the shared contract. This file has not been compiled by the reviewer.

The proposed transfer and macro forms quantify mu after N0. This is an
optional stronger uniformity than uniformity over cuts for one fixed mu.
It is supported by the intended explicit quadrature estimates: their
constants use only probability normalization, the selected finite partition,
uniform spatial cost bounds, and the displayed fixed parameters. No norm,
modulus of time continuity, or other profile-dependent constant is used.
-/

noncomputable section
open Set MeasureTheory

namespace RiffleLowerV2.EndpointProposal
open TimeProfile

/-- A proof adapter, not an extra mathematical assumption. -/
def deckPos {N : ℕ} (hN : 2 ≤ N) : 0 < N := by omega

/-- Shared horizon specialization; no property of a cut array is assumed. -/
abbrev HorizonCuts (k N : ℕ) (T : ℝ) := Cuts k N (horizonDepth N T)

/-- Exact uniform A/B endpoint errors on the empirical horizon. -/
def ProfileIntervalErrors {k N : ℕ} (T : ℝ)
    (cuts : HorizonCuts k N T) (hN : 0 < N) (μ : TimeLaw k) (e : ℝ) : Prop :=
  (∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ horizon N (horizonDepth N T) →
    |A cuts hN r s - integratedMaxCost μ r s| ≤ e) ∧
  (∀ α ∈ Icc (2 : ℝ) 4, ∀ r s : ℝ,
    0 ≤ r → r ≤ s → s ≤ horizon N (horizonDepth N T) →
    |B cuts hN α r s - integratedPsi μ α r s| ≤ e)

/-- Terminal errors are explicit. The constant 14 safely bounds 27/2. -/
def ProfileMarginErrors {k N : ℕ} (T : ℝ)
    (cuts : HorizonCuts k N T) (hN : 0 < N) (μ : TimeLaw k) (e : ℝ) : Prop :=
  |beta cuts hN (horizon N (horizonDepth N T)) - macroBeta μ T| ≤
      e + Real.log (k : ℝ) / logScale N ∧
  |lambda1 cuts hN - macroLambda1 μ T| ≤
      (13 / 2 : ℝ) * e + 14 * Real.log (k : ℝ) / logScale N

/-- LB-07 margin-transfer helper. It assumes the A/B estimate only as a
generic lemma input; the complete transfer target below must construct it.

The scalar predicate is indexed by P even though this helper uses only its
a/psi clauses. Retaining the same-P interface prevents an unnoticed switch
of partitions when this helper is composed with quadrature.
-/
def MarginTransferTarget : Prop :=
  ∀ (k N : ℕ), 2 ≤ k → ∀ (hN : 2 ≤ N) (T : ℝ), 0 < T →
  ∀ (P : BorelPartition k) (μ : TimeLaw k), ScalarIntegrable μ P T →
  ∀ (cuts : HorizonCuts k N T) (e : ℝ), 0 ≤ e →
    ProfileIntervalErrors T cuts (deckPos hN) μ e →
    ProfileMarginErrors T cuts (deckPos hN) μ e

/-- LB-07 complete uniform transfer. Choose P first; only afterwards require
ScalarIntegrable for that same P. The supplied positive rho ceiling permits
simultaneous cold-bridge restrictions. The threshold may depend on rho/phi.
-/
def ProfileTransferTarget : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (T e rhoCeiling : ℝ),
    0 < T → 0 < e → 0 < rhoCeiling →
  ∃ (chiPartition : ℝ), 0 < chiPartition ∧ chiPartition < 1 / (k : ℝ) ∧
  ∃ (P : BorelPartition k), P.IsRegular chiPartition 1 ∧
  ∃ (rho0 : ℝ), 0 < rho0 ∧ rho0 ≤ rhoCeiling ∧
    ∀ (rho : ℝ), 0 < rho → rho ≤ rho0 →
    ∃ (phi0 : ℝ), 0 < phi0 ∧
      ∀ (phi : ℝ), 0 < phi → phi ≤ phi0 →
      ∃ (N0 : ℕ), 2 ≤ N0 ∧
        ∀ (N : ℕ) (hN : 2 ≤ N), N0 ≤ N →
        ∀ (μ : TimeLaw k), ScalarIntegrable μ P T →
        ∀ (cuts : HorizonCuts k N T),
          AlmostLike cuts (deckPos hN) μ P T rho phi →
          ProfileIntervalErrors T cuts (deckPos hN) μ e ∧
          ProfileMarginErrors T cuts (deckPos hN) μ e

/-- Fixed cold-branch parameters, all independent of N and the cut array. -/
def ColdParameters (k : ℕ) (etaCold chiGood gamma rho : ℝ) : Prop :=
  0 < chiGood ∧ 0 < gamma ∧ 0 < rho ∧
    2 * rho * Real.log (k : ℝ) ≤ kappa0 etaCold / 100

/-- LB-10 largest-word-only endpoint. No profile or local-good parameter
occurs at all. It concerns the chronological physical inverse law. -/
def LargestOnlyTarget : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (T etaLargest : ℝ),
    0 < T → 0 < etaLargest →
  ∀ (epsilon : ℝ), 0 < epsilon →
  ∃ (N0 : ℕ), 2 ≤ N0 ∧
    ∀ (N : ℕ) (hN : 2 ≤ N), N0 ≤ N →
    ∀ (cuts : HorizonCuts k N T),
      etaLargest ≤ beta cuts (deckPos hN) (horizon N (horizonDepth N T)) →
      1 - epsilon ≤ tv (physicalInverseLaw cuts) (uniformPermutation N)

/-- LB-10 standalone cold endpoint matching prop:cold-lower. The positive
margin fixes kappa and kappa0 before rho and N0. LocalGood is an explicit
cut hypothesis; witness/localization/concentration are not premises. -/
def ColdOnlyTarget : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (T etaCold : ℝ),
    0 < T → 0 < etaCold →
  ∀ (chiGood gamma rho : ℝ), ColdParameters k etaCold chiGood gamma rho →
  ∀ (epsilon : ℝ), 0 < epsilon →
  ∃ (N0 : ℕ), 2 ≤ N0 ∧
    ∀ (N : ℕ) (hN : 2 ≤ N), N0 ≤ N →
    ∀ (cuts : HorizonCuts k N T),
      LocalGood cuts (deckPos hN) chiGood gamma rho 0 T →
      etaCold ≤ lambda1 cuts (deckPos hN) →
      beta cuts (deckPos hN) (horizon N (horizonDepth N T)) < kappa0 etaCold →
      1 - epsilon ≤ tv (physicalInverseLaw cuts) (uniformPermutation N)

/-- Both numerical alternatives use actual finite columns. The whole local
parameter restriction is inside the cold branch, so the largest branch is
valid even if the supplied cold parameters are inadmissible. In the cold
alternative, assembly itself splits at terminal beta = kappa0 etaCold.
-/
def EmpiricalAlternative {k N : ℕ} (T : ℝ)
    (cuts : HorizonCuts k N T) (hN : 0 < N)
    (etaLargest etaCold chiGood gamma rho : ℝ) : Prop :=
  etaLargest ≤ beta cuts hN (horizon N (horizonDepth N T)) ∨
    (ColdParameters k etaCold chiGood gamma rho ∧
      LocalGood cuts hN chiGood gamma rho 0 T ∧
      etaCold ≤ lambda1 cuts hN)

/-- Endpoint E. Fixed parameters and accuracy precede N0; N and all cuts
follow N0. There is no TimeLaw, regularity premise, or supplied witness. -/
def EmpiricalCombinedTarget : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (T etaLargest etaCold : ℝ),
    0 < T → 0 < etaLargest → 0 < etaCold →
  ∀ (chiGood gamma rho epsilon : ℝ), 0 < epsilon →
  ∃ (N0 : ℕ), 2 ≤ N0 ∧
    ∀ (N : ℕ) (hN : 2 ≤ N), N0 ≤ N →
    ∀ (cuts : HorizonCuts k N T),
      EmpiricalAlternative T cuts (deckPos hN)
        etaLargest etaCold chiGood gamma rho →
      1 - epsilon ≤ tv (physicalInverseLaw cuts) (uniformPermutation N)

/-- Endpoint M. This is the separately named strengthened macro target.

The partition is chosen independently of N before ScalarIntegrable appears.
The positive rho0 satisfies the exact bridge restriction with etaCold=eta/2.
Each fixed rho permits a phi threshold. The local good constants and final
accuracy precede N0, exposing their threshold dependence. All mu/cuts after
N0 obey the same selected partition and fixed parameter bounds.

The transfer accuracy e and its restrictions are proof-assembly choices:
0 < e < min (kappa0 (eta/2)/10) (eta/100). They need not be extra user premises
in this final endpoint because LB-11 chooses such an e before selecting P.
-/
def MacroscopicIntegrableTarget : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (T eta : ℝ), 0 < T → 0 < eta →
  ∃ (chiPartition : ℝ), 0 < chiPartition ∧ chiPartition < 1 / (k : ℝ) ∧
  ∃ (P : BorelPartition k), P.IsRegular chiPartition 1 ∧
  ∃ (rho0 : ℝ), 0 < rho0 ∧
      2 * rho0 * Real.log (k : ℝ) ≤ kappa0 (eta / 2) / 100 ∧
    ∀ (rho : ℝ), 0 < rho → rho ≤ rho0 →
    ∃ (phi0 : ℝ), 0 < phi0 ∧
      ∀ (phi : ℝ), 0 < phi → phi ≤ phi0 →
      ∀ (chiGood gamma : ℝ), 0 < chiGood → 0 < gamma →
      ∀ (epsilon : ℝ), 0 < epsilon →
      ∃ (N0 : ℕ), 2 ≤ N0 ∧
        ∀ (N : ℕ) (hN : 2 ≤ N), N0 ≤ N →
        ∀ (μ : TimeLaw k), ScalarIntegrable μ P T →
        ∀ (cuts : HorizonCuts k N T),
          AlmostLike cuts (deckPos hN) μ P T rho phi →
          LocalGood cuts (deckPos hN) chiGood gamma rho 0 T →
          eta ≤ max (macroBeta μ T) (macroLambda1 μ T) →
          1 - epsilon ≤ tv (physicalInverseLaw cuts) (uniformPermutation N)

end RiffleLowerV2.EndpointProposal
