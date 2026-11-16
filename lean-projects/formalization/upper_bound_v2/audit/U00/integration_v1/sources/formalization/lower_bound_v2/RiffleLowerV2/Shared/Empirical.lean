import RiffleLowerV2.Shared.Model

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Set MeasureTheory
namespace RiffleLowerV2
open TimeProfile

/-- Finite-column horizon. Endpoints normally use K = floor(T log N). -/
def horizon (N K : ℕ) : ℝ := (K : ℝ) / logScale N

def gridTime (N m : ℕ) : ℝ := (m : ℝ) / logScale N

/-- Fraction of column j elapsed by time t; no macro profile is involved. -/
def columnFraction {K : ℕ} (N : ℕ) (j : Fin K) (t : ℝ) : ℝ :=
  max 0 (min 1 (t * logScale N - j.val))

/-- Signed integral of the bounded finite step function, with zero extension. -/
def empiricalIntegral {K : ℕ} (N : ℕ) (f : Fin K → ℝ) (r s : ℝ) : ℝ :=
  ∑ j, (columnFraction N j s - columnFraction N j r) * f j / logScale N

def gridSum {K : ℕ} (N : ℕ) (f : Fin K → ℝ) (a b : ℕ) : ℝ :=
  (∑ j ∈ Finset.univ.filter (fun j : Fin K => a ≤ j.val ∧ j.val < b), f j) / logScale N

def A {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N) : ℝ → ℝ → ℝ :=
  empiricalIntegral N (fun j => maxCost (cuts.profile hN j))
def B {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N) (α : ℝ) : ℝ → ℝ → ℝ :=
  empiricalIntegral N (fun j => psi (cuts.profile hN j) α)
def J {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N) (α : ℝ) : ℝ → ℝ → ℝ :=
  empiricalIntegral N (fun j => tiltedCost (cuts.profile hN j) α)
def H {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N) (α : ℝ) : ℝ → ℝ → ℝ :=
  empiricalIntegral N (fun j => tiltedEntropy (cuts.profile hN j) α)
def beta {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N) (s : ℝ) : ℝ := 1 - A cuts hN 0 s

def F {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N) (α s u : ℝ) : ℝ :=
  (α + 3) / 2 * beta cuts hN s - B cuts hN α s u - 2 * B cuts hN 2 u (horizon N K)

def triangle (T : ℝ) : Set (ℝ × ℝ) := {su | 0 ≤ su.1 ∧ su.1 ≤ su.2 ∧ su.2 ≤ T}
def lambda1 {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N) : ℝ :=
  sSup ((fun su : ℝ × ℝ => sInf ((fun α => F cuts hN α su.1 su.2) '' Icc 3 4)) ''
    triangle (horizon N K))

def kappa (η : ℝ) : ℝ := η / 1000
def kappa0 (η : ℝ) : ℝ := min (kappa η / 100) (1 / 1000)

def macroBeta {k : ℕ} (μ : TimeLaw k) (s : ℝ) : ℝ := 1 - integratedMaxCost μ 0 s
def macroF {k : ℕ} (μ : TimeLaw k) (T α s u : ℝ) : ℝ :=
  (α + 3) / 2 * macroBeta μ s - integratedPsi μ α s u - 2 * integratedPsi μ 2 u T
def macroLambda1 {k : ℕ} (μ : TimeLaw k) (T : ℝ) : ℝ :=
  sSup ((fun su : ℝ × ℝ => sInf ((fun α => macroF μ T α su.1 su.2) '' Icc 3 4)) '' triangle T)

/-- Opt-in regularity for this exact chosen partition; historical TimeLaw is unchanged. -/
def ScalarIntegrable {k : ℕ} (μ : TimeLaw k) (P : BorelPartition k) (T : ℝ) : Prop :=
  (∀ i, IntervalIntegrable (cellMass μ P i) volume 0 T) ∧
  IntervalIntegrable (profileMaxCost μ) volume 0 T ∧
  ∀ α ∈ Icc (2 : ℝ) 4, IntervalIntegrable (fun t => profilePsi μ t α) volume 0 T

@[simp] theorem empiricalIntegral_self {K : ℕ} (N : ℕ) (f : Fin K → ℝ) (r : ℝ) :
    empiricalIntegral N f r r = 0 := by simp [empiricalIntegral]

theorem empiricalIntegral_add {K : ℕ} (N : ℕ) (f : Fin K → ℝ) (r s t : ℝ) :
    empiricalIntegral N f r t = empiricalIntegral N f r s + empiricalIntegral N f s t := by
  simp only [empiricalIntegral, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end RiffleLowerV2
